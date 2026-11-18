# leanlight-evm: a checked `eth_call` at the light client's anchor

`evm/` adds local `eth_call` to leanLight, as an optional package. It runs
[EthLib](https://github.com/ethereum/EthLib)'s EVM, vendored, on a partial state: the accounts,
slots and code the light client proved at its anchored block. A call is answered only when the
run read nothing outside those facts. This document says what it is made of, what is proved,
what is tested and what is trusted.

## Packages

| Package | Directory | Requires | What |
|---|---|---|---|
| `leanlight` | `/` | nothing | the light client, unchanged; requiring it fetches and builds nothing of the EVM |
| `leanlight-evm` | `evm/` | `leanlight` | `EthLibEvm` (EthLib's EVM, vendored), `LeanLightEvm` (the checked entry, the chain table, the driver), `LeanLightEvmCli` and the `leanlight-evm` executable, the tests |
| `leanlight-evm-proofs` | `evm/proofs/` | `leanlight-evm`, `leanlight-proofs` (so Mathlib) | `LeanLightEvmProofs`: the agreement theorem, over EthLib's vendored proofs (`EthLibProofs`, in `leanlight-evm`, not a default target) |

A consumer opts in with Lake's subdirectory form (Lean 4.35's Lake: `git URL @ REV / SUBDIR`):

```lean
require «leanlight-evm» from git "https://github.com/nconsigny/leanLight" @ "<rev>" / "evm"
```

`leanlight-evm` requires `leanlight` by the path `..`, which inside the clone Lake makes of the
repository is its root, so both come from the same revision.

## What runs

`LeanLightEvm.call (b : Budgets) (i : Input) : Outcome` (`evm/LeanLightEvm/Call.lean`):

- **The rules** (EthLib's fork and EIP-7892's blob schedule) come from the header's chain id and
  timestamp in `i.table`, by default `LeanLightEvm.Chain.known`, derived from leanLight's own
  chain table (`LeanLight.Lc.Forks`: Electra runs `.pectra`, Fulu `.fusaka`, the k-th BPO entry
  `.bpoK`, Gloas `.glamsterdam`). Before a chain's first row or from its horizon
  (`reviewedHorizon`, 2027-03-01) the call is refused (`.rules`). A consumer that follows another
  chain passes its own `ChainRules`.
- **The run**: EthLib's `prepareCall` steps then `processMessageCall`, observed. No gas price:
  `Request` has no fee field, base fee and gas price are 0. EIP-3860's init-code limit is
  applied as `validateTransaction` applies it. Execution gas is capped at
  `Budgets.executionGas` (2^24); a request that names more is refused, one that names none runs
  capped and is refused if a frame may have run out of gas because of the cap.
- **The checks after the run** (R0 to R5): every account accessed (EthLib's tracker, plus the
  sender and the recipient) has a fact; every slot accessed has one, or its account is absent or
  has the empty storage root; every deployment candidate accessed (EIP-7610) has the empty storage
  root (a proved non-empty root is refused as undecidable); every code accessed is held under its
  hash; every `BLOCKHASH` asked within the last 256 blocks is among the hashes held. If not, the
  outcome is `needs` with what to fetch, at most the round's width; budgets bound rounds, keys,
  code bytes and the request's data.

`LeanLightEvm.Driver.run` (`evm/LeanLightEvm/Driver.lean`) builds `call`'s input from what a
client fetched, through leanLight's readers only: the store's anchor (`Store.anchored`), the EL
header bound to it (`Anchor.bind`), the EVM's header fields from the same RLP's field list
(`Anchor.fieldsB`), each account and its slots under the header's state root
(`Facts.storageAt`), code only under the code hash its account's proof proved, and, when asked,
the 256 ancestors' hashes from the EIP-2935 history contract under the same root
(`History.blockHash`). An account the trie proves absent reads as the empty account and becomes
an absent fact: from EIP-161 on no state holds an empty account, which EIP-7523 makes a rule on
every chain past the Merge.

`leanlight-evm` (`evm/EvmMain.lean`, `evm/LeanLightEvmCli/Call.lean`) syncs as `leanlight` does,
then runs the call in rounds, each fetching at the anchored block what the previous run's `needs`
named (`eth_getProof`, `eth_getCode`, the history contract's proofs). `estimate` bisects the gas
named in the request between the gas a capped run used and the header's limit, each probe a
checked run: it prints a gas at which the checked call succeeds and one below at which it fails
or is refused.

## What is proved

All in `evm/proofs`, audited by `evm/scripts/check-axioms.sh` (every constant of `LeanLightEvm`,
`LeanLightEvmProofs` and the vendored EthLib, runtime and proofs, rests only on `propext`,
`Classical.choice` and `Quot.sound`) and replayed through the kernel by
`evm/scripts/check-kernel.sh`.

**`LeanLightEvmProofs.call_agrees : LeanLightEvm.CallAgrees`.** For any budgets and input: if
`call` answers `a`, then on every full state `F` in which the facts hold (`Facts.HoldIn`: each
account fact is `F`'s account, each slot fact `F`'s word, each code `F`'s under its hash, and an
account with the empty storage root has no nonzero slot in `F`), whose storage sits only at
existing accounts (`StorageAtAccounts`) and which holds every account's code (`CodesAvailable`),
and for the chain's full list of ancestor hashes `full` of which the held hashes are a suffix
(`AncestorsOf`), the plain run (`reference`: the same preparation, EthLib's `processMessageCall`
with no observer, with `full`) gives `a.result`: the same success flag, output, error, gas used,
refund and logs. If `call` refuses the request, the plain run refuses it for the same reason. It
rests on EthLib's `processMessageCall_agrees` (noninterference over its read tracker) and
`processMessageCallWith_modify` (the observed run is the plain run), vendored and audited with
it. Ported from the wallet leanLight was extracted from, with the chain table made a field of the
input.

What it does not say: that `prepare` is EthLib's own `eth_call` preparation (it re-expresses
`Rpc/Call.lean`'s steps, which are not vendored; tested on recorded calls), that EthLib's EVM is
execution-specs' (EthLib's own concern; tested here against nodes), anything about `needs` and
`unsupported`, or about the answer's other fields (`reads`, `fork`, `capped`).

**`LeanLightEvmProofs.Driver`** composes it with the light client: see
[Composition with the light client](#composition-with-the-light-client).

## Composition with the light client

`evm/proofs/LeanLightEvmProofs/Driver.lean`, proved and audited with the rest.

**The two models of a state.** `Represents F S stor`: `F` is EthLib's state (what the EVM runs
on); `S` and `stor` are the Yellow Paper's world state as leanLight's trie specification has it
(`Spec.Mpt.Trie`, what a state root commits to). They are one state: the account `S` holds at
each address is `F`'s, with the storage root of `stor a` (the empty account where `F` has none);
`stor a` holds `F`'s words; the tries' contents are well formed; `F` holds code under its own
Keccak-256; and `F` holds no empty account (nonce 0, balance 0, no code), as no state has since
EIP-161's clearing and as EIP-7523 makes a rule past the Merge. `represents_empty` shows the
relation can hold.

**The collisions.** `Collision F S stor fx` names byte strings built from the fetched bytes `fx`
and the honest tries: a fetched account or slot proof against the honest proof
(`Spec.Mpt.collision`), two addresses or slots with one Keccak-256 (`Spec.Mpt.Trie.clash`), the
empty proof against the honest proof of a slot of an account read with the empty storage root,
and fetched code against the code `F` holds under the same hash (EthLib's Keccak-256). Each
disjunct holds only if Keccak-256 maps two different byte strings it names to one hash; this is
how leanLight states its own reads (`reaches_read_sound`), and no collision-freedom axiom is
assumed.

**The theorems.**

- `factsAt_holdIn`: the facts `Driver.factsAt` reads under the state root of `S`, once `call`'s
  R0 accepted them, hold in every `F` that represents `S` and holds every account's code
  (`Facts.HoldIn`), or a named collision.
- `inputAt_agrees`: an answer (a refusal) of `call` on `Driver.inputAt`'s input is `reference`'s
  on every such `F` whose storage sits at existing accounts, for the chain's ancestors `full`
  (`AncestorsOf`), or a named collision.
- `run_agrees`: if `Driver.run` returns `ran`, the store had an anchor `anc` at the clock
  (`Store.anchored`), `Anchor.bind` keeps the fetched RLP as `ran.el` for it, the outcome is
  `call`'s on `ran.input`, and an answer (a refusal) is `reference`'s on every `F` that
  represents a world state whose trie's root is `ran.el`'s state root, or a named collision.
- `reaches_run_agrees`: the same at a store reached from the checkpoint (`Reaches`, which
  `LeanLight.Lc.Driver.start` and `feed` give), with `AnchorProved` for `anc` (fresh, not halted;
  anchor, finalized header and committee carried from the checkpoint by passed signature checks
  of two thirds of an authenticated committee), and the EVM's header read from the field list
  whose canonical RLP is the fetched RLP, whose Keccak-256 is the anchor's execution block hash.
- `ancestorsOf_spec`: the ancestor hashes held are, one by one, the EIP-2935 history contract's
  words under the anchored state root as `History.blockHash` reads them (whose meaning in the
  trie is leanLight's `blockHash_spec`).

**What stays a hypothesis.** That the world state with the anchored header's state root is the
chain's (it is what the header commits to; `Represents` relates it to EthLib's model); that its
storage sits at existing accounts and its code is held (`StorageAtAccounts`, `CodesAvailable`);
that the chain's ancestor hashes are those the history contract holds (`AncestorsOf`, which
`ancestorsOf_spec` reduces to EIP-2935's rule that each block's system call stores its parent's
hash); what a passed signature check means (leanLight's pairing hypotheses and
`Committee.Consistent`, in `LeanLightProofs.Signers`, cited, not imported: see below).

## The BLS namespace clash, and what it forbids

leanLight's proofs vendor EthLib's BLS12-381 at another pin (`57af539e`) under
`LeanLightProofs.Vendor.EthLib.Bls`, whose declarations sit in `EthLib.Cryptography.Bls`, as the
EVM's own BLS precompiles' do (pin `230e355b`). No Lean environment can hold both. The light
client's driver theorems (`LeanLightProofs.Driver`: `Reaches`, `AnchorProved`, `read_sound`,
`reaches_read_sound`) do not import the vendored BLS: their closure is leanLight's runtime, its
store and trie proofs, and `Mathlib.Data.Finset.Card`. So `evm/proofs` requires
`leanlight-proofs` and imports those modules beside the EVM, and the composition is one theorem
in one environment. What is forbidden: importing, from `evm/proofs`, any module whose closure
holds `LeanLightProofs.Vendor` (the BLS theorems: `Bls/*`, `Signers`); `evm/proofs/Audit.lean`
fails if one is in the environment. The meaning of a passed signature check
(`verifySignature_iff_pairing`, under the pairing hypotheses and `Committee.Consistent`) is
therefore cited, not imported: it is a theorem about the same runtime function the store calls.

## What is tested

`lake exe leanlight-evm-test [--quick]` from `evm/` (`evm/LeanLightEvmTests/`), on recorded public
chain data (`evm/tests/vectors`, about 1,100 calls on mainnet and Sepolia, with `SHA256SUMS`):

- each recorded call answered or refused as the node did (output and flag; EthLib's gas, error
  kind and logs as a regression check), discovered from no facts with the default budgets;
- unless `--quick`, sweeps: every required fact withheld in turn (no answer may be given), and
  unread facts withheld and corrupted (the answer must not change);
- the proof-backed tier: two blocks' `eth_getProof` answers and code read only through
  `Driver.factsAt` and `Driver.headerOf` (leanLight's readers), every case answered from them,
  and forged proofs and headers refused;
- synthetic worlds: `call` against `reference` on the full state, the statement of
  `call_agrees` run on concrete cases; hostile calls (gas-burning loops, slot sweeps, pointer
  chases, code fan-out) refused within the budgets; EIP-7610's holes; the chain table against
  EthLib's mainnet configuration and leanLight's epochs.

## What is trusted

- Lean's compiler and runtime, GMP, and the toolchain's `Std` (the tree maps EthLib's state is
  made of: `Std.Data.ExtTreeMap`, `Std.Data.ExtTreeSet` and the 32 modules they import). This is
  the one exception to leanLight's rule that its runtime imports Lean core only:
  `evm/scripts/check-runtime.sh` checks that `LeanLightEvm`'s closure is Init, those Std modules,
  the vendored EVM and `LeanLight`, and holds no `implemented_by`, `extern`, `opaque`, `unsafe`,
  `partial`, `sorry` or `axiom`.
- EthLib's EVM as the specification of the EVM: what is proved is that `call` gives what
  EthLib's plain run gives on the full state; that EthLib computes what a node computes is
  tested against nodes, not proved.
- The fetch loop of `leanlight-evm`, as `leanlight`'s: which calls it makes and in what order.
  It cannot make a wrong answer pass; it can make a call fail.
- Keccak-256 collision resistance, as everywhere in leanLight: the theorems name the byte strings
  whose collision would break them.
