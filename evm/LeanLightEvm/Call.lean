import LeanLightEvm.Chain
import EthLib.Execution.Transactions.Process

/-!
# A checked `eth_call` on what the light client proved

`LeanLightEvm.call` runs one `eth_call` on a partial state: the facts the light client proved at
one anchored block (accounts, storage slots, code by its hash) and the anchored header. It
answers only when the run read nothing outside those facts; otherwise it names what to fetch
(`needs`), or refuses. It never guesses: a read outside the facts would be answered by EthLib's
defaults (an account that does not exist, a slot holding 0), so an answer is given only when the
run's own read tracker shows that every read is among them.

## What runs

The steps of EthLib's `ChainView.prepareCall` then `CallSetup.run` (`Rpc/Call.lean` at the pin,
which is not vendored: it needs `Lean.Json`), re-expressed over the vendored modules, with these
conventions fixed:

- **No gas price is ever named.** A request pays no fee, its block environment has a base fee of
  0 and the code sees a gas price of 0, as EthLib's `eth_call` does for a request that names no
  fee. A request that names a price makes nodes disagree (geth debits gas × price, reth does
  not), so `Request` has no such field.
- **EIP-3860's init-code limit is applied**: a creation whose init code is longer than
  `maxInitCodeSize fork` is refused, as `validateTransaction` refuses it (`Validity.lean`,
  `initCodeFits`), in the same place among the checks. EthLib's `eth_call` skips that check.
- **Execution gas is capped** at `Budgets.executionGas` (2^24 by default), on the execution gas
  only: the transaction's gas limit (the request's, else the header's) still sizes the intrinsic
  gas and, from Glamsterdam, the state-gas reservoir, since capping the limit itself starves the
  reservoir. At Glamsterdam EthLib's own split already keeps execution gas under 2^24, so the
  cap never bites there. Before it, a request that names more gas than the cap leaves is refused
  as over budget; one that names none runs with the capped gas, is marked `capped`, and is
  refused as over budget if it ends out of gas, or if a frame of it may have. A capped run that
  halts otherwise (an invalid opcode) consumes the capped gas, not the header's: its `gasUsed`
  follows the convention.
- **The fork and the blob schedule** come from `LeanLightEvm.Chain` by chain id and timestamp,
  in the table the input carries (`Input.table`, by default `Chain.known`).

## The requirements, and which clause of `AgreesOnTracker` each establishes

EthLib proves (`Proofs/Transactions/Noninterference.lean`, `processMessageCall_agrees`, at the
pin) that a message call gives the same output on any state `F` that agrees with the state it ran
on, `S`, on four sets that its end state names (`Proofs/State/Agreement.lean`,
`BlockState.AgreesOnTracker`): `accessedAccount` (accounts read or written), `accessedSlot`
(slots read or written), `candidateStorage` (the whole storage of each accessed account with
nonce 0 and no code in `S`: the EIP-7610 collision check reads it and the tracker does not record
it) and `accessedCode` (the code under the code hash of each accessed account). `S` here is
`Facts.toState`. Each check of `call` is there to establish one clause for every `F` the facts
hold in (`Facts.HoldIn`); `checkRun` lists them as R1 to R5, and `Facts.check` as R0.

## The theorem

`CallAgrees` below states it as a `Prop`, proved in `evm/proofs` as
`LeanLightEvmProofs.call_agrees`: an answer of `call` is the answer of the plain run
(`reference`, EthLib's `processMessageCall` with no observer) on every full state that the facts
hold in, whose storage sits only at existing accounts and which holds the code of every account;
and a refusal is the plain run's refusal. The proof: the observed run is the plain run
(`processMessageCallWith_modify`, `Proofs/Transactions/Observe.lean`); R0 to R4 give
`AgreesOnTracker` between the facts' state and `F`; `processMessageCall_agrees` carries it over
the run, on the states after the sender's nonce increment; `prepare` agrees on both states since
it reads only the sender's account and the recipient's code, which R1 and R4 fix; R5 makes the
block environment with the hashes `call` holds answer every `BLOCKHASH` the run asked as the
chain's full list of 256 ancestors does.

That `prepare` is EthLib's own `ChainView.prepareCall` and `CallSetup.run` (`Rpc/Call.lean`, not
vendored) is tested on recorded calls, not proved: `reference` reuses `prepare`, so no theorem
about `call` can say it.

Not part of it: that the facts hold in the chain's state at the anchor (that is what
`LeanLightEvm.Driver` adds, from the light client's readers, and
`LeanLightEvmProofs.Driver` proves short of a Keccak-256 collision); that EthLib's semantics are
execution-specs' (tested on recorded calls, never proved); Lean's compiler and the `Std` modules
EthLib's state maps use.
-/

namespace LeanLightEvm

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State
open EthLib.Execution.Transactions
open EthLib.Execution.Blocks (Log)

/-! ## Inputs -/

/-- The fields of the bound execution header that a call reads (`Anchor.bind` binds the header;
nothing here checks it). `excessBlobGas` and `slotNumber` are 64-bit fields of the header. -/
structure Header where
  /-- The block number. -/
  number : Nat
  /-- The timestamp, in seconds; it picks the fork in `LeanLightEvm.Chain`. -/
  timestamp : Nat
  /-- The block's gas limit: the transaction's gas limit when the request names none. -/
  gasLimit : Nat
  /-- The fee recipient (`COINBASE`). -/
  coinbase : Address
  /-- `mixHash`, the beacon randomness (`PREVRANDAO`). -/
  prevRandao : Bytes32
  /-- The excess blob gas, which gives `BLOBBASEFEE` under the row's blob schedule. -/
  excessBlobGas : Nat
  /-- The parent beacon block root (EIP-4788). -/
  parentBeaconBlockRoot : Hash32
  /-- The beacon slot (`SLOTNUM`), read from Glamsterdam only. -/
  slotNumber : Nat
  /-- The parent's hash: `BLOCKHASH(number - 1)` when no ancestors are given. -/
  parentHash : Hash32

/-- What the light client proved about one account at the anchor. -/
inductive AccountFact where
  /-- Proved absent from the state trie (an exclusion proof). -/
  | absent
  /-- Proved present, with its nonce, balance and code hash, and its storage root when the
  proof gave one (an account proof always does; facts taken from plain getters do not). -/
  | present (nonce : Nat) (balance : U256) (codeHash : Hash32) (storageRoot : Option Hash32)
  deriving Repr, DecidableEq

/-- The facts the run may read: accounts, slots, and code by its hash. -/
structure Facts where
  /-- The proved accounts, absent or present. -/
  accounts : Std.ExtTreeMap Address AccountFact := ∅
  /-- The proved slots of present accounts, zero values included. -/
  slots : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256) := ∅
  /-- Code, keyed by its Keccak-256 hash; `call` refuses a key that is not the hash. -/
  code : Std.ExtTreeMap Hash32 ByteArray := ∅

/-- An `eth_call` request. It names no fee, no access list and no nonce (module doc). -/
structure Request where
  /-- The sender, `from`: it must be among the facts. -/
  sender : Address
  /-- The recipient, or none for a creation: it must be among the facts. -/
  to : Option Address
  /-- The call data, or the init code of a creation. -/
  data : ByteArray
  /-- The wei sent. -/
  value : Nat
  /-- The gas limit, or none for the header's gas limit. -/
  gas : Option Nat
  /-- The number of EIP-7702 authorizations the request carries: any is unsupported. -/
  authorizations : Nat := 0
  /-- The number of blob versioned hashes the request carries: any is unsupported. -/
  blobs : Nat := 0

/-- The budgets of one call. A call that would pass one ends as `unsupported (.budget _)`. The
"honest maximum" of each is the largest any of about 770 recorded mainnet and Sepolia calls
needed when the defaults were calibrated. -/
structure Budgets where
  /-- Runs per call: a call is refused at round `rounds` (0-based). Honest maximum 20. -/
  rounds : Nat := 32
  /-- Accounts plus slots per call, the facts held and the keys asked for together; block
  hashes count apart. Honest maximum 1,074. -/
  stateKeys : Nat := 1536
  /-- Accounts asked for in one round. Honest maximum 12. -/
  accountsPerRound : Nat := 32
  /-- The keys asked for in round 0; each round doubles it, up to `maxWidth`. -/
  firstWidth : Nat := 4
  /-- The most keys asked for in one round (block hashes apart). -/
  maxWidth : Nat := 256
  /-- Bytes of code held per call. Honest maximum 238,850. -/
  codeBytes : Nat := 524288
  /-- Execution gas per run, at most `maxExecutionGas` (2^24; more is refused). Honest maximum
  11,775,032. It does not bound time well: a loop of cheap opcodes runs for seconds at 2^24, so
  a caller that runs calls it did not choose wants a wall-clock bound of its own. -/
  executionGas : Nat := 16777216

/-- The most execution gas any `Budgets` may name, 2^24 (`Budgets.executionGas`'s default):
`checkInput` refuses budgets above it. It bounds a run's memory: a frame's memory costs
`3 w + w² / 512` gas for `w` words, and every frame's memory, copies and call depth are paid
from this gas. That bound, and those of `maxCodeFact` and `maxRequestData`, hold only for runs
entered through `call`, whose `checkInput` applies them: `prepare`, `reference` and
`Prepared.run` take any cap and check none, and are for the statement and the tests. -/
def maxExecutionGas : Nat := 16777216

/-- The most bytes one code may have among the facts, 65,536: the largest code any fork allows
(EIP-7954 at Glamsterdam; 24,576 from Spurious Dragon, and below that before it, since 200 gas
per byte deposited never fit a block), so no account's code on chain is larger. `checkInput`
refuses a larger one as over budget: each frame that runs a code holds one flag per byte of it
(`validJumpDestinations`, 8 bytes each). -/
def maxCodeFact : Nat := 65536

/-- The most bytes of call data (or init code) a request may carry, 262,144 = 2^18: twice the
largest init code any fork allows (EIP-7954's 131,072 at Glamsterdam), so that every init code
a node refuses as too large up to that size is refused here as the node refuses it.
`checkInput` refuses a longer request as
over budget (`Budget.dataBytes`). No execution gas pays for the request's own data: the intrinsic
gas and, from Pectra, the calldata floor bound it only through the gas named or the header's
limit, up to about 30 MB at a 300M limit. Yet each of its bytes costs tens of bytes of transient
memory before and outside the EVM's memory accounting (the zero-byte count walks it as a list,
`Validity.zeroBytes`; the message copies it), so it is bounded here: IDENTITY on 262,144 zero
bytes peaked at 43 MB when measured (2026-11-18). -/
def maxRequestData : Nat := 262144

/-- One run of a call: the rules' table, the anchored header, the facts and the request. -/
structure Input where
  /-- The rules of each chain (`LeanLightEvm.Chain`): `Chain.known` unless the caller extends it. -/
  table : List ChainRules := known
  /-- The chain id; with the header's timestamp it picks the rules in `table`. -/
  chainId : Nat
  /-- The bound header's fields. -/
  header : Header
  /-- The hashes of up to 256 ancestors, oldest first, the parent's last; or none, and then only
  the parent's hash (from the header) is known. -/
  ancestors : Option (List Hash32)
  /-- The facts held so far. -/
  facts : Facts
  /-- The call. -/
  request : Request
  /-- How many runs of this call came before this one. -/
  round : Nat := 0

/-! ## Outcomes -/

/-- Why a request is refused before it runs, as a node would refuse it. -/
inductive Refusal where
  /-- The sender cannot pay the value (EthLib's code 809). -/
  | insufficientFunds
  /-- The gas limit is below the intrinsic gas or, from Pectra, the calldata floor (code 800). -/
  | intrinsicGasTooLow
  /-- EIP-3860: a creation's init code is longer than the fork allows. -/
  | initCodeTooLarge (size : Nat)
  /-- A number of the request, or the sender's nonce, of 2^256 or more. -/
  | tooLarge (what : String)
  /-- No address for the creation (an RLP failure EthLib reports as internal). -/
  | noCreationAddress
  /-- The sender's account cannot take the nonce increment. -/
  | senderAccount
  deriving Repr, DecidableEq

/-- Which budget a call would pass. -/
inductive Budget where
  | rounds
  | stateKeys
  | accountsPerRound
  | codeBytes
  /-- The request's call data or init code is longer than `maxRequestData`. -/
  | dataBytes
  /-- The run ended out of gas, or a frame of it ran out of gas, with its execution gas
  shortened by the cap. -/
  | executionGas
  /-- Facts are missing but the round's width (`firstWidth`, `maxWidth`) lets none be asked. -/
  | width
  deriving Repr, DecidableEq

/-- Inputs that are not facts of one state, or not a header. -/
inductive Malformed where
  /-- Code held under a key that is not its Keccak-256 hash. -/
  | codeHash (claimed : Hash32)
  /-- A slot of an address that has no present account among the facts. -/
  | slotWithoutAccount (address : Address)
  /-- A nonzero slot of an account whose proved storage root is the empty root. -/
  | slotUnderEmptyRoot (address : Address)
  /-- More than 256 ancestors, more than the block number, or a last one that is not the
  header's `parentHash`. -/
  | ancestors
  /-- A 64-bit header field of 2^64 or more, or a chain id of 2^64 or more. -/
  | header
  deriving Repr, DecidableEq

/-- Why a call is not run, or not answered, and never will be with more facts. -/
inductive Unsupported where
  /-- The fork table has no rules for the header. -/
  | rules (gap : TableGap)
  /-- An EIP-7702 authorization list. -/
  | authorizations
  /-- Blobs. -/
  | blobs
  /-- An accessed account with nonce 0 and no code whose proved storage root is not the empty
  root: EIP-7610 reads its whole storage, which no proof of single slots gives. -/
  | collisionUndecidable (address : Address)
  /-- A budget. -/
  | budget (which : Budget)
  /-- Inputs that cannot be facts of one state. -/
  | malformed (why : Malformed)
  /-- The run aborted for a reason other than missing code (an EthLib internal error). -/
  | aborted (why : String)
  deriving Repr

/-- What to fetch before running the call again, at most the round's width of keys. -/
structure Needs where
  /-- Accounts (an account proof, or an exclusion proof). -/
  accounts : List Address := []
  /-- Slots of present accounts. -/
  slots : List (Address × Bytes32) := []
  /-- Code by hash. -/
  code : List Hash32 := []
  /-- Accounts whose storage root is needed (their account proof again: facts taken without
  one). -/
  storageRoots : List Address := []
  /-- Whether the 256 ancestors' hashes are needed (a `BLOCKHASH` asked past the parent). -/
  ancestors : Bool := false
  deriving Repr

/-- What a call ended in: the part a node's answer is made of, and that `CallAgrees` equates. -/
structure Result where
  /-- No error. -/
  ok : Bool
  /-- The returned data, or the revert's data. -/
  output : ByteArray
  /-- The error that stopped the message, if any. -/
  error : Option EvmError
  /-- Gas used before the refund: the intrinsic gas, plus the execution gas and the state gas
  the message spent (the recorded fixtures' `gasUsed`). -/
  gasUsed : Nat
  /-- The refund counter at the end, before its cap. -/
  refund : Nat
  /-- The logs, oldest first (none for a failed message). -/
  logs : Array Log

/-- What the run read, by EthLib's tracker plus the sender and the recipient. -/
structure Reads where
  /-- Accounts read or written. -/
  accounts : List Address
  /-- Slots read or written. -/
  slots : List (Address × Bytes32)
  /-- The block numbers `BLOCKHASH` asked for within the last 256 blocks. -/
  blockNumbers : List Nat

/-- An answer: the result, what it read, the rules it ran under, and whether the gas cap
shortened the run. -/
structure Answer where
  /-- The result. -/
  result : Result
  /-- What the run read. -/
  reads : Reads
  /-- The fork it ran under. -/
  fork : Fork
  /-- Whether `Budgets.executionGas` shortened the execution gas. -/
  capped : Bool

/-- The outcome of `call`. -/
inductive Outcome where
  /-- Every requirement holds: the answer. -/
  | answer (a : Answer)
  /-- The request is refused before it runs, as a node refuses it (only once the sender and the
  recipient are known). -/
  | refused (r : Refusal)
  /-- Fetch these, then call again with `round + 1`. -/
  | needs (n : Needs)
  /-- Not run, or not answered. -/
  | unsupported (u : Unsupported)

/-! ## The facts as a state -/

/-- The storage root of empty storage: Keccak-256 of the RLP of the empty string, `0x80`
(`0x56e81f…b421`). -/
def EMPTY_STORAGE_ROOT : Hash32 := EthLib.Cryptography.Hash.Keccak.keccak256 (ByteArray.mk #[0x80])

namespace Facts

/-- Whether the facts say the address's storage is empty: proved absent, or present with the
empty storage root. Slots of such an account need no fact of their own. -/
def storageEmpty (f : Facts) (a : Address) : Bool :=
  match f.accounts[a]? with
  | some .absent => true
  | some (.present _ _ _ (some root)) => root == EMPTY_STORAGE_ROOT
  | _ => false

/-- Whether the facts fix the slot's value. -/
def slotKnown (f : Facts) (a : Address) (k : Bytes32) : Bool :=
  f.storageEmpty a || (f.slots.getD a ∅).contains k

/-- The state `S` the run reads: the present accounts, their nonzero slots, the code. -/
def toState (f : Facts) : State :=
  { accounts := f.accounts.foldl (fun m a fact => match fact with
      | .absent => m
      | .present nonce balance codeHash _ => m.insert a ⟨nonce, balance, codeHash⟩) ∅
    storage := f.slots.foldl (fun m a slots =>
      let nonzero := slots.filter fun _ v => v != 0
      if nonzero.isEmpty then m else m.insert a nonzero) ∅
    code := f.code }

/-- The accounts plus slots the facts hold. -/
def stateKeys (f : Facts) : Nat :=
  f.slots.foldl (fun n _ slots => n + slots.size) f.accounts.size

/-- The bytes of code the facts hold. -/
def codeBytes (f : Facts) : Nat :=
  f.code.foldl (fun n _ c => n + c.size) 0

/-- R0: the facts can be facts of one state, and code sits under its own hash.

- Every code is held under its Keccak-256 hash (EthLib's Keccak, the one the EVM hashes with).
  So `accessedCode` agreement needs only the hash to be the account's (R4): two codes under one
  hash would be a Keccak collision. `LeanLightEvm.Driver` also checks code against the account
  proof's code hash before it becomes a fact (`LeanLight.Lc.Driver.codeOk`, leanLight's Keccak).
- Every slot belongs to a present account (an absent account has no storage in a state whose
  storage sits at existing accounts, `StorageAtAccounts`).
- No nonzero slot under the empty storage root (so `toState` agrees with `storageEmpty`). -/
def check (f : Facts) : Except Malformed Unit := do
  for (h, c) in f.code.toList do
    if EthLib.Cryptography.Hash.Keccak.keccak256 c != h then throw (.codeHash h)
  for (a, slots) in f.slots.toList do
    match f.accounts[a]? with
    | some (.present _ _ _ root) =>
      if root == some EMPTY_STORAGE_ROOT && slots.toList.any (fun (_, v) => v != 0) then
        throw (.slotUnderEmptyRoot a)
    | _ => throw (.slotWithoutAccount a)

end Facts

/-! ## The environment and the preparation (EthLib's `prepareCall`, its steps re-expressed) -/

/-- The block environment of a call at `fork`: the header's fields, the blob schedule of the
table's row, base fee 0 (no fee is named, so EthLib's `eth_call` sets it to 0), and `hashes`. -/
def environment (fork : Fork) (blobs : BlobSchedule) (chainId : Nat) (h : Header)
    (hashes : List Hash32) : BlockEnvironment fork :=
  { chainId := UInt64.ofNat chainId, coinbase := h.coinbase, number := h.number,
    gasLimit := h.gasLimit, timestamp := BitVec.ofNat 256 h.timestamp, difficulty := 0,
    blockHashes := hashes, baseFeePerGas := fun _ => 0, prevRandao := fun _ => h.prevRandao,
    excessBlobGas := fun _ => UInt64.ofNat h.excessBlobGas,
    parentBeaconBlockRoot := fun _ => h.parentBeaconBlockRoot,
    slotNumber := fun _ => UInt64.ofNat h.slotNumber, blobSchedule := fun _ => blobs,
    blobGasPrice := none }

/-- The hashes `BLOCKHASH` can answer: the ancestors given, else the parent's alone. -/
def blockHashes (h : Header) (ancestors : Option (List Hash32)) : List Hash32 :=
  match ancestors with
  | some hs => if hs.isEmpty then [h.parentHash] else hs
  | none => [h.parentHash]

/-- A call ready to run. -/
structure Prepared where
  /-- The fork of the row. -/
  fork : Fork
  /-- The block environment. -/
  env : BlockEnvironment fork
  /-- The sender. -/
  sender : Address
  /-- The unsigned legacy transaction of the request (no fee field), as EthLib builds it. -/
  transaction : Transaction
  /-- The state with the sender's nonce incremented. -/
  state : TransactionState
  /-- The first message. -/
  message : Message fork
  /-- The substate it starts from. -/
  substate : Substate
  /-- The intrinsic gas. -/
  intrinsic : Nat
  /-- The execution gas the message got, after the cap. -/
  execution : Nat
  /-- The state-gas reservoir it got (0 before Glamsterdam). -/
  reservoir : Nat
  /-- Whether the cap lowered the execution gas. -/
  capped : Bool

/-- Why `prepare` stops. -/
inductive PrepareStop where
  | refused (r : Refusal)
  /-- The recipient's code is not in the state (EthLib's `transactionMessage` fails). -/
  | missingCode (h : Hash32)
  /-- `transactionMessage` failed otherwise (it only reads code). -/
  | internal

/-- 2^256, written as a literal so that no runtime `Nat.pow` is called (`wordBound_eq` checks
the literal). -/
def wordBound : Nat :=
  115792089237316195423570985008687907853269984665640564039457584007913129639936

theorem wordBound_eq : wordBound = 2 ^ 256 := by decide

/-- 2^64, as a literal (`u64Bound_eq`). -/
def u64Bound : Nat := 18446744073709551616

theorem u64Bound_eq : u64Bound = 2 ^ 64 := by decide

/-- A word of the request, or the refusal of one of 2^256 or more. -/
def word (what : String) (n : Nat) : Except PrepareStop U256 :=
  if n < wordBound then .ok (BitVec.ofNat 256 n) else .error (.refused (.tooLarge what))

/-- EthLib's `ChainView.prepareCall` for a request that names no fee, type 0, with this module's
conventions (module doc): the steps in EthLib's order, with EIP-3860's check added where
`validateTransaction` puts it, and the execution gas capped at `cap`. It reads the state only
through the sender's account and the recipient's code. It checks none of `call`'s ceilings
(`maxExecutionGas`, `maxRequestData`, `maxCodeFact`): the abort-site notes hold for a run
prepared here only when `call` prepared it. -/
def prepare (rules : Activation) (chainId : Nat) (h : Header) (ancestors : Option (List Hash32))
    (cap : Nat) (r : Request) (S : State) : Except PrepareStop Prepared := do
  let fork := rules.fork
  let env := environment fork rules.blobSchedule chainId h (blockHashes h ancestors)
  let sender := r.sender
  let state := TransactionState.ofBlock ⟨S, ∅, ∅, ∅, ∅⟩
  let account := state.getAccount sender
  let gas := r.gas.getD env.gasLimit
  let t : Transaction := .legacy
    { nonce := ← word "nonce" account.nonce, gasPrice := 0, gas := ← word "gas" gas, to := r.to,
      value := ← word "value" r.value, data := r.data, v := 0, r := 0, s := 0 }
  unless t.value.toNat ≤ account.balance.toNat do throw (.refused .insufficientFunds)
  let target ← (messageTarget sender account.nonce t).mapError fun _ => .refused .noCreationAddress
  let state ← (state.incrementNonce fork sender).mapError fun _ => .refused .senderAccount
  unless t.value.toNat ≤ (state.getAccount sender).balance.toNat do
    throw (.refused .insufficientFunds)
  let initCodeFits : Except PrepareStop Unit :=
    unless (fork ≥ .shapella → t.to = none → t.data.size ≤ maxInitCodeSize fork) do
      throw (.refused (.initCodeTooLarge t.data.size))
  let coversMinimum : Except PrepareStop Unit :=
    unless minimumGas fork sender t ≤ gas do throw (.refused .intrinsicGasTooLow)
  if fork ≥ .glamsterdam then
    initCodeFits
    coversMinimum
  else
    coversMinimum
    initCodeFits
  let intrinsic := intrinsicGas fork sender t
  let txEnv : TransactionEnvironment fork :=
    { origin := sender, gasPrice := 0, blobVersionedHashes := fun _ => t.blobHashes }
  let alloc := allocateGas fork t intrinsic
  let execution := min alloc.execution cap
  let message ← (transactionMessage env txEnv state sender target execution t).mapError fun
    | .state (.missingCode c) => .missingCode c
    | _ => .internal
  return { fork, env, sender, transaction := t, state
           message := { message with reservoir := alloc.reservoir }
           substate := startSubstate fork env.coinbase sender target t
           intrinsic, execution, reservoir := alloc.reservoir
           capped := cap < alloc.execution }

/-- The result of a message that ran: gas used is the intrinsic gas, plus the execution gas and
the reservoir the message spent. -/
def Prepared.result (p : Prepared) (o : CallOutput) : Result :=
  { ok := o.error.isNone, output := o.output, error := o.error
    gasUsed := p.intrinsic + (p.execution - o.gasLeft) + (p.reservoir - o.reservoir)
    refund := o.refund, logs := o.logs }

/-- `CallSetup.run`: the message at the meter of the fork, with no observer. Like `prepare`, it
checks none of `call`'s ceilings: for tests and `reference` only, never exported. -/
def Prepared.run (p : Prepared) : Except EvmError CallOutput :=
  let paid := paidWrites p.sender p.message.currentTarget p.transaction
  if p.fork ≥ .glamsterdam then
    processMessageCall (Meter := StateGasMeter) p.env.chainId.toNat p.message p.state p.substate
      p.transaction.authorizations paid
  else
    processMessageCall (Meter := Nat) p.env.chainId.toNat p.message p.state p.substate
      p.transaction.authorizations paid

/-! ## The observed run -/

/-- What the observer notes, step by step. -/
structure Notes where
  /-- The block numbers `BLOCKHASH` asked for within the 256 blocks before the call's. -/
  blockNumbers : Std.ExtTreeSet Nat := ∅
  /-- The unknown accounts (slot none) and slots that the steps were about to read, first seen
  first, at most `noteCap`. A prediction may be a read that never happens (a step that then runs
  out of gas): only those the tracker also holds are asked for. -/
  order : Array (Address × Option Bytes32) := #[]
  /-- The accounts in `order`. -/
  seenAccounts : Std.ExtTreeSet Address := ∅
  /-- The slots in `order`. -/
  seenSlots : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32) := ∅
  /-- Whether a frame may have run out of gas: a step failed with `outOfGas`, or a creation or a
  precompile call ended in failure (its caller's next step finds 0 on the stack), which covers
  a code deposit and a precompile that ran out of gas without a step of their own. In a run the
  cap shortened, its answer may be the cap's and not the chain's, so `call` does not give it. -/
  starved : Bool := false
  /-- The depths of the frames waiting for a creation or a precompile call to end, innermost
  first. -/
  pending : List Nat := []

/-- The most unknown reads noted, four times the widest round. -/
def noteCap : Nat := 1024

/-- The account or slot the next step reads from the state, when its opcode names it on the
stack: SLOAD and SSTORE, BALANCE, EXTCODESIZE, EXTCODECOPY, EXTCODEHASH, SELFDESTRUCT, and the
four calls. -/
def nextRead {fork : Fork} {Meter : Type} [GasMeter Meter] (evm : Evm fork Meter) (op : UInt8) :
    Option (Address × Option Bytes32) :=
  match evm.stack.val with
  | [] => none
  | top :: rest =>
    if op = 0x54 ∨ op = 0x55 then some (evm.message.currentTarget, some (U256.toBeBytes top))
    else if op = 0x31 ∨ op = 0x3b ∨ op = 0x3c ∨ op = 0x3f ∨ op = 0xff then
      some (toAddressMasked top, none)
    else if op = 0xf1 ∨ op = 0xf2 ∨ op = 0xf4 ∨ op = 0xfa then
      rest.head?.map fun w => (toAddressMasked w, none)
    else none

/-- The observer's record of one step: it only changes the notes, so the observed run is the
plain run (`processMessageCallWith_modify`, `Proofs/Transactions/Observe.lean:49` at the pin). -/
def record (f : Facts) (number : Nat) {fork : Fork} {Meter : Type} [GasMeter Meter]
    (evm : Evm fork Meter) (res : Except EvmError (StepResult fork Meter)) (n : Notes) : Notes :=
  -- a creation or precompile call this frame waited for has ended: 0 on the stack is a failure
  let n := match n.pending with
    | d :: rest =>
      if d = evm.message.depth then
        { n with pending := rest
                 starved := n.starved || evm.stack.val.head?.any (· == 0) }
      else n
    | [] => n
  let n := match res with
    | .error .outOfGas => { n with starved := true }
    | .ok (.child _ m _) =>
      if m.target.isNone || (precompileAddress fork m).isSome then
        { n with pending := evm.message.depth :: n.pending }
      else n
    | _ => n
  if h : evm.pc < evm.code.size then
    let op := evm.code[evm.pc]
    let n := if op = 0x40 then
        match evm.stack.val with
        | w :: _ =>
          let b := w.toNat
          if b < number ∧ number ≤ b + 256 then { n with blockNumbers := n.blockNumbers.insert b }
          else n
        | [] => n
      else n
    match nextRead evm op with
    | none => n
    | some (a, none) =>
      if f.accounts.contains a || n.seenAccounts.contains a || noteCap ≤ n.order.size then n
      else { n with order := n.order.push (a, none), seenAccounts := n.seenAccounts.insert a }
    | some (a, some k) =>
      if f.slotKnown a k || (n.seenSlots.getD a ∅).contains k || noteCap ≤ n.order.size then n
      else { n with order := n.order.push (a, some k)
                    seenSlots := n.seenSlots.insert a ((n.seenSlots.getD a ∅).insert k) }
  else n

/-- The message with the observer, at the meter of the fork: the output and the notes. -/
def Prepared.runObserved (p : Prepared) (f : Facts) (number : Nat) :
    Except EvmError (CallOutput × Notes) :=
  let paid := paidWrites p.sender p.message.currentTarget p.transaction
  if p.fork ≥ .glamsterdam then
    (processMessageCallWith (Meter := StateGasMeter) (M := StateT Notes (Except EvmError))
      (fun evm res => modify (record f number evm res)) p.env.chainId.toNat p.message p.state
      p.substate p.transaction.authorizations paid).run {}
  else
    (processMessageCallWith (Meter := Nat) (M := StateT Notes (Except EvmError))
      (fun evm res => modify (record f number evm res)) p.env.chainId.toNat p.message p.state
      p.substate p.transaction.authorizations paid).run {}

/-! ## The checks after the run -/

/-- The accounts the run accessed: the sender and the recipient (fixed reads: `prepare` reads
them outside the tracker), then EthLib's `accessedAccount`: `accountReads` and the keys of
`accountWrites`. -/
def accessedAccounts (r : Request) (o : CallOutput) : Std.ExtTreeSet Address :=
  let s : Std.ExtTreeSet Address := (∅ : Std.ExtTreeSet Address).insert r.sender
  let s := match r.to with | some a => s.insert a | none => s
  let s := o.state.accountReads.foldl (fun s a => s.insert a) s
  o.state.accountWrites.foldl (fun s a _ => s.insert a) s

/-- The slots the run accessed: EthLib's `accessedSlot`, `storageReads` and the keys of
`storageWrites`. -/
def accessedSlots (o : CallOutput) : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32) :=
  let m := o.state.storageReads
  o.state.storageWrites.foldl (fun m a slots =>
    m.insert a (slots.foldl (fun s k _ => s.insert k) (m.getD a ∅))) m

/-- The round's width: `firstWidth` doubled `round` times, at most `maxWidth`. -/
def widthAt (maxWidth : Nat) : Nat → Nat → Nat
  | w, 0 => min w maxWidth
  | w, n + 1 => if maxWidth ≤ w then maxWidth else widthAt maxWidth (2 * w) n

/-- What the checks after the run found. -/
structure Findings where
  /-- R4: accessed accounts whose code is not held. -/
  code : List Hash32 := []
  /-- R3: accessed deployment candidates (nonce 0, no code) with no storage root. -/
  roots : List Address := []
  /-- R3: accessed deployment candidates whose storage root is proved not empty. -/
  nonEmpty : List Address := []
  /-- R1: accessed accounts with no fact. -/
  accounts : Std.ExtTreeSet Address := ∅
  /-- R2: accessed slots the facts do not fix. -/
  slots : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32) := ∅
  /-- R5: whether a `BLOCKHASH` asked past the hashes held. -/
  ancestors : Bool := false

/-- Whether the checks R1, R2, R4 and R5 found nothing missing (R3's proved non-empty roots
apart: they are never fetched). An answer is given only then, whatever the round's width. -/
def Findings.complete (fd : Findings) : Bool :=
  fd.code.isEmpty && fd.roots.isEmpty && fd.accounts.isEmpty && fd.slots.isEmpty && !fd.ancestors

/-- The checks R1 to R5 on a run that ended. Each establishes, for every full state `F` the facts
hold in (`Facts.HoldIn`) with storage only at existing accounts, one part of what
`CallAgrees`'s proof needs:

- **R1, `accessedAccount`**: every accessed account (plus the sender and the recipient) has a
  fact, so `S` and `F` agree on it (present with the same nonce, balance and code hash, or
  absent from both).
- **R2, `accessedSlot`**: every accessed slot has a fact, or its account is absent (no storage
  in `F`) or has the empty storage root (no slot in `F`, by proof binding).
- **R3, `candidateStorage`**: every accessed account that is a deployment candidate in `S`
  (absent, or nonce 0 and no code) has empty storage in `F` as in `S`: absent ones by
  `StorageAtAccounts`, present ones because their storage root is the empty root. A root that
  is missing is asked for; one that is proved not empty makes the call unsupported, since
  EIP-7610 reads that whole storage, which no fetch of single slots gives.
- **R4, `accessedCode`**: every accessed account's code is held under its code hash, so `S` and
  `F` (which holds every code, `CodesAvailable`) agree on it.
- **R5, the block environment** (outside `AgreesOnTracker`):
  every `BLOCKHASH` within the last 256 blocks asked for a hash among those held, so the
  environment is the same as with all 256 ancestors. -/
def checkRun (f : Facts) (h : Header) (ancestors : Option (List Hash32)) (r : Request)
    (o : CallOutput) (notes : Notes) : Findings := Id.run do
  let held := (blockHashes h ancestors).length
  let mut out : Findings :=
    { ancestors := notes.blockNumbers.toList.any fun b => held < h.number - b }
  for a in (accessedAccounts r o).toList do
    match f.accounts[a]? with
    | none => out := { out with accounts := out.accounts.insert a }
    | some .absent => pure ()
    | some (.present nonce _ codeHash root) =>
      if codeHash != EMPTY_CODE_HASH && !f.code.contains codeHash then
        out := { out with code := codeHash :: out.code }
      if nonce == 0 && codeHash == EMPTY_CODE_HASH then
        match root with
        | none => out := { out with roots := a :: out.roots }
        | some root =>
          if root != EMPTY_STORAGE_ROOT then out := { out with nonEmpty := a :: out.nonEmpty }
  for (a, keys) in (accessedSlots o).toList do
    for k in keys.toList do
      if !f.slotKnown a k then
        out := { out with slots := out.slots.insert a ((out.slots.getD a ∅).insert k) }
  return out

/-- The keys to ask for this round, at most `width`: code hashes and storage roots first (they
belong to accounts already proved), then the unknown accounts and slots, those the observer saw
in the order it saw them, after those it could not see (the recipient's delegate, a created
address), which the run reaches first. -/
def needsOf (fd : Findings) (notes : Notes) (width : Nat) : Needs := Id.run do
  let mut n : Needs := { ancestors := fd.ancestors }
  let mut left := width
  for c in fd.code.reverse do
    if 0 < left then n := { n with code := c :: n.code }; left := left - 1
  for a in fd.roots.reverse do
    if 0 < left then n := { n with storageRoots := a :: n.storageRoots }; left := left - 1
  let observed (a : Address) (k : Option Bytes32) : Bool :=
    match k with
    | none => notes.seenAccounts.contains a
    | some k => (notes.seenSlots.getD a ∅).contains k
  -- unseen first
  for a in fd.accounts.toList do
    if 0 < left && !observed a none then
      n := { n with accounts := a :: n.accounts }; left := left - 1
  for (a, ks) in fd.slots.toList do
    for k in ks.toList do
      if 0 < left && !observed a (some k) then
        n := { n with slots := (a, k) :: n.slots }; left := left - 1
  -- then the observed ones, in their order, those the tracker confirms
  for (a, k) in notes.order do
    if 0 < left then
      match k with
      | none =>
        if fd.accounts.contains a then n := { n with accounts := a :: n.accounts }; left := left - 1
      | some k =>
        if (fd.slots.getD a ∅).contains k then
          n := { n with slots := (a, k) :: n.slots }; left := left - 1
  return { n with code := n.code.reverse, storageRoots := n.storageRoots.reverse
                  accounts := n.accounts.reverse, slots := n.slots.reverse }

/-- Whether a `Needs` asks for nothing. -/
def Needs.isEmpty (n : Needs) : Bool :=
  n.accounts.isEmpty && n.slots.isEmpty && n.code.isEmpty && n.storageRoots.isEmpty && !n.ancestors

/-- The keys a `Needs` counts against the round's and the call's budgets. -/
def Needs.keys (n : Needs) : Nat := n.accounts.length + n.slots.length

/-- What the run read, for the answer. -/
def readsOf (r : Request) (o : CallOutput) (notes : Notes) : Reads :=
  { accounts := (accessedAccounts r o).toList
    slots := (accessedSlots o).toList.flatMap fun (a, ks) => ks.toList.map fun k => (a, k)
    blockNumbers := notes.blockNumbers.toList }

/-! ## The entry point -/

/-- The checks before anything runs: the budgets of the round and the facts (execution gas at
most `maxExecutionGas`, the request's data at most `maxRequestData` bytes, each code at most
`maxCodeFact` bytes), the request's kind, the facts' consistency (R0), the header and
ancestors. -/
def checkInput (b : Budgets) (i : Input) : Except Unsupported Activation := do
  if b.rounds ≤ i.round then throw (.budget .rounds)
  if maxExecutionGas < b.executionGas then throw (.budget .executionGas)
  if maxRequestData < i.request.data.size then throw (.budget .dataBytes)
  let rules ← (rulesAt i.table i.chainId i.header.timestamp).mapError .rules
  if 0 < i.request.authorizations then throw .authorizations
  if 0 < i.request.blobs then throw .blobs
  unless i.chainId < u64Bound ∧ i.header.excessBlobGas < u64Bound ∧ i.header.slotNumber < u64Bound do
    throw (.malformed .header)
  if let some hs := i.ancestors then
    unless hs.length ≤ 256 ∧ hs.length ≤ i.header.number ∧
        (hs.isEmpty ∨ hs.getLast? = some i.header.parentHash) do
      throw (.malformed .ancestors)
  if b.stateKeys < i.facts.stateKeys then throw (.budget .stateKeys)
  if b.codeBytes < i.facts.codeBytes then throw (.budget .codeBytes)
  if i.facts.code.any (fun _ c => maxCodeFact < c.size) then throw (.budget .codeBytes)
  (i.facts.check).mapError .malformed
  return rules

/-- The checked call (module doc). In order:

1. `checkInput`: round, the ceilings (`maxExecutionGas`, `maxRequestData`, `maxCodeFact`),
   table, request kind, header, ancestors, the facts' budgets, R0.
2. The sender and the recipient must be facts: otherwise it asks for them alone, as running
   with a sender taken as absent gives a creation the wrong address.
3. `prepare` on `Facts.toState`: a refusal, or the recipient's code asked for. A request that
   names more execution gas than the cap allows is over budget here, before it runs: its answer
   could depend on the gas it named (`GAS`, the 63/64 rule), so it is not answered under less.
   A request that names none runs under the cap (this module's default; nodes' own defaults
   differ: EthLib's is the header's limit, reth's at most 50M), and its answer says `capped`.
4. The run, observed (`Prepared.runObserved`). An abort for missing code asks for that code (the
   abort loses the tracker); any other abort is unsupported.
5. `checkRun` (R1 to R5): if anything is missing (`Findings.complete` fails), `needsOf` asks
   for it, at most the round's width, within the per-round and per-call budgets; a width that
   lets nothing be asked is over budget. The answer is decided on the findings, never on the
   truncated `Needs`.
6. A deployment candidate proved to hold storage: unsupported.
7. A run the cap shortened that ended out of gas, or in which a frame may have run out of gas
   (`Notes.starved`): over budget, since with the gas a node gives it the answer could differ.
8. Otherwise the answer. -/
def call (b : Budgets) (i : Input) : Outcome :=
  match checkInput b i with
  | .error u => .unsupported u
  | .ok rules =>
    let f := i.facts
    let r := i.request
    let fixed := r.sender :: r.to.toList
    let missing := fixed.filter fun a => !f.accounts.contains a
    if !missing.isEmpty then .needs { accounts := missing.eraseDups } else
    match prepare rules i.chainId i.header i.ancestors b.executionGas r f.toState with
    | .error (.refused why) => .refused why
    | .error (.missingCode c) => .needs { code := [c] }
    | .error .internal => .unsupported (.aborted "the first message")
    | .ok p =>
      if p.capped && r.gas.isSome then .unsupported (.budget .executionGas) else
      match p.runObserved f i.header.number with
      | .error (.state (.missingCode c)) => .needs { code := [c] }
      | .error e => .unsupported (.aborted s!"{repr e}")
      | .ok (o, notes) =>
        let fd := checkRun f i.header i.ancestors r o notes
        if !fd.complete then
          let n := needsOf fd notes (widthAt b.maxWidth b.firstWidth i.round)
          if n.isEmpty then .unsupported (.budget .width)
          else if b.accountsPerRound < n.accounts.length then .unsupported (.budget .accountsPerRound)
          else if b.stateKeys < f.stateKeys + n.keys then .unsupported (.budget .stateKeys)
          else .needs n
        else match fd.nonEmpty with
        | a :: _ => .unsupported (.collisionUndecidable a)
        | [] =>
          let precompileFailed := (precompileAddress p.fork p.message).isSome && o.error.isSome
          if p.capped && (o.error == some .outOfGas || notes.starved || precompileFailed) then
            .unsupported (.budget .executionGas)
          else .answer { result := p.result o, reads := readsOf r o notes, fork := p.fork
                         capped := p.capped }

/-! ## The statement (proved: `LeanLightEvmProofs.call_agrees`, in `evm/proofs`) -/

/-- The run on a full state `F` with the chain's ancestor hashes `full`, as `CallAgrees`
compares it: the same rules, preparation and gas convention as `call`, then EthLib's
`processMessageCall` with no observer and no check. `none` when the table has no rules or the
run aborts. It checks none of `call`'s ceilings, so their bounds do not hold for it: a
statement and a test oracle. -/
def reference (b : Budgets) (i : Input) (full : List Hash32) (F : State) :
    Option (Except Refusal Result) :=
  match rulesAt i.table i.chainId i.header.timestamp with
  | .error _ => none
  | .ok rules =>
    match prepare rules i.chainId i.header (some full) b.executionGas i.request F with
    | .error (.refused why) => some (.error why)
    | .error _ => none
    | .ok p =>
      match p.run with
      | .ok o => some (.ok (p.result o))
      | .error _ => none

/-- Storage sits only at existing accounts: what makes an exclusion proof fix an account's
storage as empty. -/
def StorageAtAccounts (F : State) : Prop :=
  ∀ a k, F.getStorage a k ≠ 0 → (F.accounts[a]?).isSome

/-- `F` holds the code of every account: EthLib's `HasCodes` (`Proofs/State/CodeAvailability.lean`,
vendored with the proofs) of `TransactionState.ofBlock ⟨F, ∅, ∅, ∅, ∅⟩`. -/
def CodesAvailable (F : State) : Prop :=
  ∀ a, ∃ code, F.getCode ((F.getAccountOptional a).getD EMPTY_ACCOUNT).codeHash = .ok code

/-- The facts hold in `F`: each account fact is `F`'s account (absent, or present with that
nonce, balance and code hash), each slot fact is `F`'s word, each code is `F`'s under its hash,
and an account whose proved storage root is the empty root has no nonzero slot in `F` (proof
binding: `LeanLightEvmProofs.Driver` turns verified proofs under the anchor's root into this,
short of a Keccak-256 collision). A storage root that is not the empty one says nothing
here. -/
structure Facts.HoldIn (f : Facts) (F : State) : Prop where
  /-- Accounts. -/
  accounts : ∀ (a : Address) (fact : AccountFact), f.accounts[a]? = some fact →
    match fact with
    | AccountFact.absent => F.accounts[a]? = none
    | AccountFact.present nonce balance codeHash _ => F.accounts[a]? =
      some ({ nonce, balance, codeHash } : Account)
  /-- Empty storage roots. -/
  emptyRoots : ∀ (a : Address) (nonce : Nat) (balance : U256) (codeHash : Hash32),
    f.accounts[a]? = some (.present nonce balance codeHash (some EMPTY_STORAGE_ROOT)) →
    ∀ k, F.getStorage a k = 0
  /-- Slots. -/
  slots : ∀ (a : Address) (k : Bytes32) (v : U256), (f.slots.getD a ∅)[k]? = some v →
    F.getStorage a k = v
  /-- Code. -/
  code : ∀ (h : Hash32) (c : ByteArray), f.code[h]? = some c → F.code[h]? = some c

/-- `full` is the chain's list of ancestor hashes at the header (the `min 256 number` blocks
before it, oldest first, the parent's last), and the hashes `call` holds are its suffix. -/
def AncestorsOf (i : Input) (full : List Hash32) : Prop :=
  full.length = min 256 i.header.number ∧ full.getLast? = some i.header.parentHash ∧
    (blockHashes i.header i.ancestors).IsSuffix full

/-- **The obligation `call` is built for** (proved: `LeanLightEvmProofs.call_agrees`,
`evm/proofs/LeanLightEvmProofs/Hashes/Suffice.lean`).

For any budgets and input: if `call` answers `a`, then on every full state `F` in which the
facts hold (`Facts.HoldIn`, which includes that an account whose proved storage root is the
empty root has no slot in `F`), whose storage sits at existing accounts (`StorageAtAccounts`)
and which holds every account's code (`CodesAvailable`), and for the chain's full ancestor list
`full` (`AncestorsOf`), the plain run of the same call (`reference`, with `full`) gives
`a.result`: the same success flag, output, error, gas used, refund and logs. And if `call`
refuses the request, the plain run refuses it for the same reason. Both runs use `call`'s gas
convention (execution gas capped at `b.executionGas`; when the request names no gas the
answer's `capped` says so), and `prepare` for both: that `prepare` is EthLib's own `eth_call`
preparation is tested, not stated here. Vacuous at block 0, which has no parent.

What it does not say: that `F` is the chain's state at the anchor (proof binding and
`Anchor.bind`), that EthLib's run is what a node answers (EthLib as the specification; nodes
disagree on a named gas price, which `Request` cannot name), anything about `needs` and
`unsupported`, which answer nothing, or anything about the answer's other fields: that its read
set `a.reads` is enough for a re-check, that `capped` and `fork` are right. -/
def CallAgrees : Prop :=
  ∀ (b : Budgets) (i : Input) (F : State) (full : List Hash32),
    StorageAtAccounts F → CodesAvailable F → i.facts.HoldIn F → AncestorsOf i full →
      (∀ a, call b i = .answer a → reference b i full F = some (.ok a.result)) ∧
      (∀ r, call b i = .refused r → reference b i full F = some (.error r))

end LeanLightEvm
