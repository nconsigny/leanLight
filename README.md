# leanLight

An Ethereum consensus light client written in Lean 4, whose definitions are what runs and what
its machine-checked proofs are about. It follows mainnet or Sepolia from a checkpoint by the sync protocol (BLS12-381
signatures of the sync committee, SSZ Merkle branches), then answers execution-layer reads
(balances, nonces, code, storage) by checking `eth_getProof` proofs against the state root of a
block its own verified beacon header names. Nothing an RPC endpoint says is believed until the
light client has checked it, with two exceptions this README names: the checkpoint when you opt in
with `--unsafe-untrusted-checkpoint`, and which addresses the endpoint learns you read
([Trust model](#trust-model)).

It is research software: young, without an outside audit, and not yet something to trust with
funds on its own word.

The code was extracted from [leanKohakuDesktop](https://github.com/nconsigny/leanKohakuDesktop)'s
light client (commit `8bddee0e`), where it runs sandboxed inside the wallet. Here it stands
alone: a library, its proofs, its tests and a command-line client.

## What is in it

| Directory | What | Imports |
|---|---|---|
| `LeanLight/` | The light client: SHA-256, Keccak-256, RLP, SSZ (decoding, `hash_tree_root`, branches), BLS12-381 (fields to `Fp12`, G1, G2, hash-to-G2, the pairing, FastAggregateVerify), the chain table (mainnet, Sepolia, Electra to Gloas), the sync protocol's store, execution-layer headers, Merkle-Patricia proofs, the reads anchored on a verified header, and the inclusion verdict for transactions and receipts | Lean core only |
| `proofs/` | Theorems about `LeanLight`'s definitions, against readable specifications: the vendored [ssz-specs](https://github.com/ethereum/ssz-specs) (MIT), [EthLib](https://github.com/ethereum/EthLib)'s BLS12-381 (CC0) and [VCVio](https://github.com/Verified-zkEVM/VCVio)'s SHA-2 and Keccak (Apache-2.0), with Mathlib's elliptic-curve group law | Mathlib |
| `tests/` | consensus-specs' light-client and SSZ vectors, BLS vectors and a differential test against EthLib's readable BLS; recorded mainnet runs replayed offline, honest and forged (`leanlight-client-test`); the offline benchmark (`leanlight-bench`) | `LeanLight` |
| `Main.lean`, `LeanLightCli/` | `leanlight`, the command-line client (HTTP through `curl`) | `LeanLight` |
| `bench/` | The comparison with [Helios](https://github.com/a16z/helios) on the same endpoints (`compare.py`), Helios's checks replayed offline on the same recorded bytes (`helios-replay`), and their results | Python 3, Rust |
| `scripts/` | The axiom audit and the kernel replay | |
| `evm/` | Optional, a package of its own: a checked local `eth_call` at the anchored block over [EthLib](https://github.com/ethereum/EthLib)'s EVM, vendored; its proofs (`evm/proofs/`), tests and the `leanlight-evm` client ([below](#optional-local-eth_call)) | `LeanLight`, `Std`'s tree maps; proofs: Mathlib |

What the proofs cover, in brief (the statements are in the files):

- **BLS12-381**: the runtime's field and curve arithmetic is Mathlib's group law
  (`Bls/Curves.lean`, `Bls/Jacobian.lean`); decompression is sound and canonical; KeyValidate
  accepts exactly the compressions of the points of G1 other than the identity, and equals
  EthLib's (`Bls/Decompress.lean`, `Bls/Roundtrip.lean`, `Bls/FavEth.lean`); the subgroup
  checks run Scott's tests, σ on G1 and ψ on G2, proved sound and complete through Hasse's
  bound and the curves' point counts (`Bls/Scott.lean`, `Bls/ScottComplete.lean`,
  `Bls/Hasse.lean`, `Bls/PointCount.lean`); hash-to-G2 equals EthLib's and lands in G2
  (`Bls/HashEth.lean`, `hashInG2`); the runtime's Miller loop is EthLib's line by line and its
  fast final exponentiation is the cube of the naive one (`Bls/Miller.lean`,
  `Bls/FinalExpPow.lean`, `Bls/Frobenius.lean`, `Bls/GrangerScott.lean`), so FastAggregateVerify
  equals EthLib's when the message does not hash to the identity and the signature is not the
  identity's encoding (`fastAggregateVerifyBytes_eq_eth`), and on the identity's encoding too
  given non-degeneracy (`Bls/FavEthG2.lean`). That the pairing is bilinear and non-degenerate is
  the one named hypothesis left, checked by the vectors, not proved (`H_vec` in the comments).
- **Committee keys** are not validated, as in the consensus specs' light client and in Helios:
  the store keeps a committee's encodings under the root that proved them and, per signature,
  takes the committee's aggregate key less the absent keys when more than half signed. On a
  committee as the chain holds one (`Committee.Consistent`: its keys decode to points of G1, its
  aggregate key to their sum) that is the participants' sum, and the signature check is the
  verification equation over it (`signersKey?_eq`, `verifySignature_iff_pairing`,
  `Signers.lean`).
- **SSZ**: each of the 14 light-client decoders returns a value exactly when ssz-specs'
  `deserialize` does, and the same value (`decode_iff`), and accepts only the canonical encoding
  of it (`decode_canonical`, `decode_injective_bytes`; `SszDecode.lean`, `SszDecodeElectra.lean`);
  `hash_tree_root` of each light-client container is ssz-specs'; a branch verifies exactly when
  the leaf is in the tree (`Ssz*.lean`).
- **The sync protocol** (`Spec/SyncProtocol.lean`, `SyncProtocol.lean`): consensus-specs
  v1.7.0-beta.5's light-client sync protocol is transcribed function by function
  (`initialize_light_client_store`, `validate_light_client_update`, `apply_light_client_update`,
  `process_light_client_update`, `process_light_client_store_force_update`, `is_better_update`,
  the fork-dependent gindices and `is_valid_light_client_header` from Altair to Gloas), and
  leanLight's store is proved to refine it: every update the store accepts, the specification's
  `process_light_client_update` accepts at the same clock, and the two stores (finalized header,
  committees, best update, optimistic header, participation counters) agree after it; every other
  update leaves the specification's store as it was (`receive_refines`). So every store the
  client reaches is one the specification reaches from the same checkpoint (`reaches_spec`). The
  runtime's ranking is `is_better_update` (`isBetter_spec`), its header check implies
  `is_valid_light_client_header` (`isValidHeader_spec`), its branch check phase0's
  `is_valid_merkle_branch` (`normalized_of_runtime`), and its signature check (the aggregate key
  less the absent keys) `FastAggregateVerify` over the participants' keys
  (`verifySignature_spec`). The chain table agrees with mainnet's and Sepolia's `config.yaml`, every
  fork from Altair on (`agrees_mainnet`, `agrees_sepolia`). The transcription itself is run on
  consensus-specs' `sync` and `update_ranking` vectors beside the store, and matches them.
- **The store**: bootstrap binds the checkpoint; an update is accepted only after every check of
  the sync protocol, BLS included; conflicts halt the store; the age bound and the clock
  (`Store.lean`, `Forks.lean`).
- **The client's decisions** (`Driver.lean`): see [Trust model](#trust-model).
- **Reads**: an EL header is bound to the verified beacon header only when its RLP hashes to the
  execution block hash; an account or storage value is what the Merkle-Patricia trie under that
  header's state root holds, short of a Keccak-256 collision on bytes the theorem names
  (`Anchor.lean`, `Trie.lean`, `Spec/MptTrie.lean`, `Inclusion.lean`).

`scripts/check-axioms.sh` audits every constant of `LeanLight` and `LeanLightProofs` (about
7,400, 3,752 of them theorems): each may rest only on `propext`, `Classical.choice` and
`Quot.sound`, so no `sorry` and no `native_decide`. `scripts/check-kernel.sh` replays every
module through Lean's kernel. `scripts/check-runtime.sh` refuses any `@[implemented_by]`,
`@[extern]`, `opaque` or `unsafe` in `LeanLight/`. CI runs all three on every push.

## Trust model

What a proof gives, what is assumed, and what is trusted without either.

**Proved.** The theorems are refinements: the runtime definition equals, or is sound against, a
readable specification (ssz-specs, EthLib's BLS12-381, VCVio's SHA-256 and Keccak-256, Mathlib's
group law, consensus-specs' sync protocol transcribed in `proofs/LeanLightProofs/Spec/SyncProtocol.lean`,
the Yellow Paper's trie). A mistake in one of those specifications would carry into leanLight;
the theorems do not prove the light client secure, they prove it computes what those
specifications say. The transcription of the sync protocol is checked against consensus-specs'
own `sync` and `update_ranking` vectors (`leanlight-store-test` runs it), and the store is proved
to refine it (`reaches_spec`): leanLight refuses more updates than the specification (below two
thirds of the committee, before Electra, older than `MAX_AGE`, after a conflict) and never calls
the forced update the specification makes optional, but every update it accepts has the effect
the specification gives it.

**Assumed, checked by test vectors.** That the pairing is bilinear and non-degenerate on
G1 × G2: named hypotheses in the BLS theorems (`PairingCheckIs`, `PairingNonDegenerate`; `H_vec`
in the design notes), checked by the BLS vectors and the differential test, never axioms. That
hash-to-G2 lands in G2, that the fast final exponentiation is the cube of the naive one and that
the Miller loop is EthLib's are theorems (`hashInG2`, `finalExp_toGF`, `millerLoopsCube`).

**Assumed, the chain's.** That a sync committee's keys are points of G1 and its
`aggregate_pubkey` their sum (`Committee.Consistent`, a hypothesis of the signature theorems in
`Signers.lean`; `Valid` in `SyncProtocol.lean`, where each key also passes KeyValidate, as the
specification's `FastAggregateVerify` requires). The beacon state's committees are: each key passed KeyValidate at deposit, and
the aggregate is `eth_aggregate_pubkeys` of the keys. The light client takes a committee only
under a root the previous committee signed (or the checkpoint's), so this is the trust it
already places in that committee; Helios and the consensus specs' light client rest on the same.

**Fast paths are proved.** What runs is never swapped in unproved: no `@[implemented_by]` or
`@[extern]` (`scripts/check-runtime.sh`). A fast version replaces a readable one only through a
`@[csimp]` equation, a theorem the axiom audit covers: Keccak-256 (`keccak256_eq_fast`,
`Base/KeccakFast.lean`), SHA-256's schedule, compression and hash (`Base/Sha256.lean`), the RLP
reader (`El/Rlp.lean`). The aggregate key less the absent keys is proved equal to the
participants' sum on a consistent committee (`signersKey?_eq`).

**Trusted, unverified.**

- Lean's compiler and runtime, and GMP, which computes `Nat` arithmetic (BLS12-381's fields).
- The command-line client's fetch loop (`Main.lean`, `LeanLightCli/`): which objects it fetches
  and in what order, its retries, how `curl`'s output and JSON become bytes. Every decision about
  those bytes is `LeanLight.Driver`'s, and proved (`LeanLightProofs/Driver.lean`): the store is
  only ever one `Store.bootstrap` of the checkpoint started and `Store.receive` steps carried
  (`start_reaches`, `feed_reaches`), and a value printed is read at that store's anchor, under
  the EL header `Anchor.bind` keeps for it, by the trie's specification (`read_sound`), code only
  when it hashes to the proved hash (`codeOk_spec`). Every store so reached holds committees
  each proved, from the checkpoint's on, by a branch under a header an earlier committee's
  signature check passed, a finalized header and an anchor likewise (`reaches_committees`,
  `reaches_finalized`, `reaches_anchor`; what a passed check means rests on the BLS hypotheses
  and `Committee.Consistent` above), and a read there binds account and storage values short of
  a Keccak-256 collision (`reaches_read_sound`). So a bug in the loop can fail a read or leave
  the anchor stale; it cannot make a value pass that those checks refuse. The loop itself is not
  proved.
- `curl`, the operating system and the clock: a clock set back can make an old checkpoint look
  fresh (`docs/spec-16-light-client.md`, "The clock"), and, as in the specification
  (`current_slot >= signature_slot`), refuses updates signed after the clock's slot until it
  catches up (verdict "signature slot after the clock's slot").
- **The checkpoint, when you opt in to fetching one.** With `--unsafe-untrusted-checkpoint`
  instead of `--checkpoint`, leanlight takes the beacon node's finalized root on trust and says so
  on standard error. Everything after is checked against that root: give `--checkpoint` with a root
  you got elsewhere (a block explorer, another node, a friend) to remove that trust.

## Privacy

A light client checks what endpoints say; it does not hide what you ask. The execution endpoint
learns every address and storage slot you read (`eth_getProof` names them) and, from your
connection, who asks; the beacon node learns that you follow the chain. leanlight sends a run's
reads in one JSON-RPC batch, so the endpoint also sees them together, linked. Use your own node,
or Tor, if that matters to you. (The wallet leanLight came from splits reads by account across
Tor circuits and endpoints; the command-line client does not.)

## Building

Lean 4.35.0 (`elan` picks it from `lean-toolchain`) and, for the client, `curl`.

```sh
lake build                               # the library and leanlight: .lake/build/bin/leanlight
(cd tests && lake build && ./.lake/build/bin/leanlight-store-test \
  && ./.lake/build/bin/leanlight-ssz-test && ./.lake/build/bin/leanlight-bls-test --quick \
  && ./.lake/build/bin/leanlight-client-test && ./.lake/build/bin/leanlight-bench --runs 3)
(cd proofs && lake exe cache get && lake build)   # the proofs, with Mathlib's cache
scripts/check-axioms.sh && scripts/check-kernel.sh
```

## The client

```sh
leanlight [--network mainnet|sepolia] --consensus-rpc URL[,URL...] --execution-rpc URL[,URL...] \
          (--checkpoint 0xROOT | --unsafe-untrusted-checkpoint) [--json] [-v] COMMAND
```

| Command | Prints |
|---|---|
| `sync` | the finalized and anchored slots, what was fetched and how long checking took |
| `follow` | `sync`, then the store kept: each new head as it is verified, once a slot, with its execution block bound when `--execution-rpc` is given (Ctrl-C stops) |
| `block-number` | the anchored execution block's number |
| `balance ADDR`, `nonce ADDR` | the account's, from its proof |
| `code ADDR` | the proved code hash, the code accepted only if it hashes to it |
| `storage ADDR SLOT...` | storage words, from their proofs |
| `queries FILE` | one sync, then every line of `FILE` (`bench/mainnet.queries`) at one block |
| `record DIR [FILE]` | a run (and `FILE`'s reads) recorded for the offline tests and benchmark, after checking it |

The beacon node must serve the light-client API in SSZ (Nimbus and Lodestar do; publicnode's
beacon API serves JSON only). Pass `--checkpoint 0xROOT` with a root you got elsewhere, or
`--unsafe-untrusted-checkpoint` to take the node's finalized root on trust. Example:

```sh
leanlight --consensus-rpc http://testing.mainnet.beacon-api.nimbus.team,https://lodestar-mainnet.chainsafe.io \
  --execution-rpc https://ethereum-rpc.publicnode.com,https://eth.drpc.org \
  --unsafe-untrusted-checkpoint \
  balance 0xd8dA6BF26964aF9D7eEd9e03E53415D37aA96045
```

**How it fetches.** The network, not the checking, sets a run's time, so the client spends its
round trips carefully:

- **One round trip to sync**: the bootstrap, the current period's update and the finality and
  optimistic updates are fetched together; older periods' updates after the bootstrap.
- **Reads fetched while the sync is checked**: the whole set of reads goes out in one JSON-RPC
  batch as soon as the optimistic update names its block, before it is verified; when the
  checked anchor is that block, the reads are there when the sync ends.
- **Several sources, the first good answer**: `--consensus-rpc` and `--execution-rpc` take
  comma-separated lists. All are asked at once and the first answer that verifies is used; every
  beacon node's finality and optimistic updates that arrived are fed to the store too, so a fast
  node that is behind does not hold the anchor back.
- **Batches an endpoint refuses**: a batch answered with an error is halved and asked again, a
  429 backed off (dRPC's free tier refuses a batch of 12 proofs and serves batches of 3).
- **One check per signature**: a beacon node's optimistic update usually repeats its finality
  update's signed header, which is then checked once.

None of this is in what the proofs cover, and none needs to be: every value the client prints
comes out of `LeanLight`'s checked readers, from a store only `Driver.start` and `Driver.feed`
made (`read_sound`), never out of the JSON. Fetching can delay a read or make it fail, not make a
wrong value pass.

## Speed

**What verifying costs, offline.** `tests/` replays two recorded mainnet runs (`leanlight
record`, in `tests/fixtures/`) with no network, so only the light client's own work is timed
(`lake exe leanlight-bench`; median of 15 runs, on a shared 32-core machine;
`bench/results/offline-2026-10-30/`). Helios's consensus checks (`helios-consensus-core` at
`a16z/helios` `2af9b41`) replay the same bytes in `bench/helios-replay` (`cargo run --release --
15 ../../tests/fixtures/mainnet-fresh ../../tests/fixtures/mainnet-week`):

| Step | leanLight (1 core) | Helios |
|---|---|---|
| Bootstrap (the checkpoint's root and committee branch) | 2.3–2.6 ms | 0.4 ms |
| A period update (a signature and the next committee's root) | 21–22 ms | 2.7–3.0 ms |
| A finality or optimistic update (one signature) | 16–17 ms | 2.4–3.0 ms |
| Binding the anchored block's header | 15 µs | |
| 13 reads (balances, nonces, storage, code), proofs checked | 0.8 ms | |
| **A sync from a fresh checkpoint** (leanLight: then the 13 reads) | **59 ms** | **8.2 ms** |
| **A sync from a checkpoint 7 periods old** | **0.18 s** | **26 ms** |

More cores change nothing. A signature check is the cost, about 7 times Helios's: hash-to-G2
(about 7 ms), the pairing (about 9 ms), the signature's decoding and ψ subgroup check (0.5 ms),
in Lean over GMP, where Helios calls a native BLS library. Committee keys are not validated, as
in the consensus specs and Helios: a signature decodes only the committee's aggregate key and
the absent keys (`Signers.lean`). Proofs and headers are cheap.

**Against Helios, on the same endpoints.** `bench/compare.py` starts Helios (`a16z/helios`
`2af9b41`) and `leanlight` from the same checkpoint on the same consensus and execution
endpoints, and compares every read at leanLight's anchored block with Helios's and the endpoint's
(mainnet, the Nimbus beacon node with publicnode's or dRPC's execution endpoint, 3 rounds each;
`bench/results/2026-10-30/`). The network dominates, so read it as two request strategies over
the same network rather than as the two verifiers' speed: leanlight fetches its sync objects in
one round trip and its reads in one JSON-RPC batch started during the sync ("How it fetches"),
while Helios asks one call per read after it.

| | Helios | leanLight |
|---|---|---|
| Sync from a fresh checkpoint | 0.9–1.1 s | 0.27–0.68 s (verifying 0.07–0.13 s) |
| Sync from a checkpoint 6 sync periods old | 1.0–1.1 s | 1.0–1.4 s (verifying 0.27–0.37 s) |
| 14 reads (balances, nonces, code, storage) after a sync, publicnode | 0.46–0.55 s, one call each | 5 ms to 0.34 s, fetched during the sync |
| The same, dRPC | 1.7–1.9 s, one call each | 1.0–1.4 s, in the batches dRPC accepts |
| Memory (peak RSS) | 23–25 MB | 27–78 MB |
| Binary | 25 MB | 6.5 MB |

Every value leanLight returned equalled the endpoint's at its block, and Helios's wherever Helios
answered at that block.

## Optional: local eth_call

`evm/` is a second Lake package, `leanlight-evm`, that answers `eth_call` locally at the block the
light client anchored, on the accounts, slots and code it proved there, and answers only when the
run read nothing else (`docs/evm.md` has the details). Requiring `leanlight` alone fetches and
builds none of it. To depend on it (Lake's `git URL @ REV / SUBDIR` form):

```lean
require «leanlight-evm» from git "https://github.com/nconsigny/leanLight" @ "<rev>" / "evm"
```

**What it adds.** `LeanLightEvm.call`, the checked entry: it runs
[EthLib](https://github.com/ethereum/EthLib)'s EVM (pin `230e355b`, vendored byte for byte in
`evm/EthLib`, CC0) on the facts it is given and answers only when every account, slot and code the
run touched, the sender and the recipient, EIP-7610's storage roots and every `BLOCKHASH` asked
are among them; otherwise it names what to fetch (`needs`) or refuses. No gas price is ever
named; EIP-3860's init-code limit is applied; the fork and blob schedule come from the header's
timestamp in a table derived from leanLight's own chain table (`LeanLightEvm.Chain`, refused past
a reviewed horizon; a consumer passes its own table for another chain); execution gas is capped at
2^24, with a refusal whenever the cap could change the answer; budgets bound rounds, keys, code and
request data. `LeanLightEvm.Driver.run` builds that input from leanLight's store and the fetched
bytes through leanLight's readers only (`Anchor.bind`, `Facts.storageAt`, the code-hash check,
EIP-2935's history contract for ancestors). `leanlight-evm` is the command-line client:

```sh
(cd evm && lake build)    # evm/.lake/build/bin/leanlight-evm
leanlight-evm --consensus-rpc URL[,URL...] --execution-rpc URL[,URL...] \
  (--checkpoint 0xROOT | --unsafe-untrusted-checkpoint) [--from ADDR] [--value WEI] [--gas N] \
  [--compare] [--json] [-v] (call TO [DATA] | create INITCODE | estimate TO [DATA])
```

It syncs as `leanlight` does, then runs the call in rounds, each fetching at the anchored block
what the previous run asked for (`eth_getProof`, `eth_getCode`, the history contract's proofs).
`estimate` prints a gas at which the checked call succeeds and one below at which it does not,
each a checked run. `--compare` prints the endpoint's own `eth_call`, marked unchecked.

**What is proved** (`evm/proofs`, every constant of `LeanLightEvm`, its proofs and the vendored
EthLib audited to rest on Lean's three axioms only, 8,498 constants; 229 modules replayed through
the kernel; `evm/scripts/check-axioms.sh`, `check-kernel.sh`):

- `call_agrees`: an answer of `call` is the plain run's (EthLib's `processMessageCall`, no
  observer) on every full state the facts hold in, whose storage sits at existing accounts and
  which holds its code, for the chain's ancestors; a refusal is the plain run's refusal. It rests
  on EthLib's noninterference theorem `processMessageCall_agrees`, vendored with it.
- `reaches_run_agrees`: composed with the light client. At a store reached from the checkpoint,
  an answer of `Driver.run` was given at an anchor `AnchorProved` holds for (as for `leanlight`'s
  reads), with the EVM's header read from the RLP whose Keccak-256 is the anchor's block hash, and
  is the plain run's on every EthLib state that represents the world state whose trie has that
  header's state root (`Represents`, with no empty account, EIP-161 and EIP-7523), unless
  Keccak-256 collides on byte strings the theorem names. The hypotheses left are the same kind as
  leanLight's (the BLS ones and `Committee.Consistent`), plus that the chain's ancestor hashes are
  those EIP-2935's history contract holds, which the driver reads.
- Not proved: that `call`'s preparation is EthLib's own `eth_call` (`Rpc/Call.lean`, not
  vendored), and that EthLib's EVM computes what a node computes. Both are tested.

**What is tested** (`cd evm && lake exe leanlight-evm-test [--quick]`): about 1,100 recorded
mainnet and Sepolia calls (`evm/tests/vectors`, public chain data) answered or refused as the node
did, sweeps that withhold or corrupt each fact, two blocks of `eth_getProof` answers read through
the driver's readers with forgeries refused, synthetic worlds against the plain run, hostile calls
within the budgets. Measured: `--quick` 2,740 checks in 1 min 50 s; the full run 18,911 checks in
15 min, none failed (one core of a shared 32-core machine).

**What it trusts beyond leanLight.** `Std`'s tree maps (`Std.Data.ExtTreeMap`,
`Std.Data.ExtTreeSet` and the 32 Std modules they import), which EthLib's state is made of: the
one exception to "Lean core only", checked by `evm/scripts/check-runtime.sh` (the closure is Init,
those modules, the vendored EVM and `LeanLight`; no `implemented_by`, `extern`, `opaque`,
`unsafe`, `partial`, `sorry` or `axiom` in it). EthLib's EVM as the specification of the EVM. The
fetch loop of `leanlight-evm`, as `leanlight`'s: it can make a call fail, not a wrong answer pass.

**Costs, measured** (2026-11-18). The vendored EVM builds in 35 s on 32 cores (2 min of CPU);
`leanlight-evm` is 15 MB (unstripped). A live `balanceOf` of USDC (a proxy) for
`0xd8dA6BF26964aF9D7eEd9e03E53415D37aA96045` on mainnet from a fresh checkpoint: 5 rounds, 9
requests, 253 KB, 3.3 s wall time of which 53 ms verifying (the sync's signatures included), the
answer equal to publicnode's `eth_call` at the same block. A `BLOCKHASH` call reads 256 history
proofs (1.1 MB). `estimate` of a USDC transfer gave 45,122, and the node's `eth_call` at that block
succeeds with 45,122 gas and reverts with 45,121.

## Reading the comments

The code keeps the identifiers of the design it came from, leanKohakuDesktop's
`spec/16-light-client.md` and `spec/INVARIANTS.md` at `8bddee0e`:

- `25a` to `25l`: the light client's invariant rows (25c BLS, 25d the chains, 25e bootstrap,
  25f acceptance, 25g conflicts, 25h the age bound, 25i the clock, 25j EL binding, 25k facts,
  25l inclusion).
- `LC1` to `LC9`: the milestones that built it; `Dn`, `Gn` and "open decision n": the design's
  decisions and goals; `H_vec`, `H_nonce`: named hypotheses.
- `lkd-lc`, `netd`, `keyd`, `lkd_verified`: the wallet's light-client process, network service,
  signer and verified Rust crate, which the comments mention where the wallet uses the code.

## Acknowledgements

leanLight's proofs stand on three projects, whose code is vendored under
`proofs/LeanLightProofs/Vendor/` as the readable specifications the runtime is proved against (and, for `evm/`, in `evm/EthLib`).
Thank you to their authors:

- **[ssz-specs](https://github.com/ethereum/ssz-specs)** (Ethereum Foundation, MIT), commit
  `3394318c`: SSZ's types, serialization, `hash_tree_root` and Merkle proofs, with their proofs.
  The light client's SSZ decoders, container roots and branch checks are proved against it.
- **[EthLib](https://github.com/ethereum/EthLib)** (CC0-1.0), commit `57af539e`: BLS12-381 in
  Lean, its readable layer and its G1 group-law proofs. KeyValidate, hash-to-G2 and
  FastAggregateVerify are proved equal to EthLib's, and the Jacobian formulas' proofs are
  ported from it.
- **[EthLib](https://github.com/ethereum/EthLib)**, again, commit `230e355b`: its EVM and its
  noninterference proofs, vendored in `evm/EthLib` (CC0-1.0) for the optional `leanlight-evm`,
  which runs that EVM and whose agreement theorem rests on EthLib's `processMessageCall_agrees`.
- **[VCVio](https://github.com/Verified-zkEVM/VCVio)** (Apache-2.0), commits `afa6593f` (SHA-256)
  and `88efe971` (Keccak-256): SHA-256 and Keccak-256 in Lean, the specifications the runtime's
  hashes are proved against.

Thanks to [Th0rgal](https://github.com/Th0rgal) (Thomas Marchand) [turbo-lean](https://github.com/Th0rgal/turbo-lean), which leanKohakuDesktop's proof work runs on.

They are copied, not required: each file names its source commit, and the copies changed only
as their headers say. Thanks also to [Mathlib](https://github.com/leanprover-community/mathlib4),
whose elliptic-curve group law the BLS proofs use, and to
[Helios](https://github.com/a16z/helios), the light client leanLight is measured against.

## License

MIT OR Apache-2.0, at your option (`LICENSE-MIT`, `LICENSE-APACHE`). The vendored code under
`proofs/LeanLightProofs/Vendor/` keeps its own license (`LICENSE` in each directory), and
`scripts/CheckKernel.lean` holds Lean's `leanchecker` replay (Apache-2.0, attributed there).
