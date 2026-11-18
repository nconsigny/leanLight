import LeanLightEvmTests.Checks

/-!
# Cases built by hand: each must end in a refusal or in `needs`, never in an answer

On a mainnet base case (the first recorded call, sender `0xd8dA…6045`) and a Sepolia one:
EIP-3860's limit, a hostile loop over the gas budget, a `BALANCE` sweep over the accounts
budget, the key, code and round budgets, the kinds of request that are unsupported, the fork
table's edges, code not under its hash, facts that cannot be one state's, and the EIP-7610
holes the read-tracker verifier recorded.
-/

namespace LeanLightEvmTests

open EthLib.Base
open EthLib.Execution.Evm (EvmError)
open EthLib.Execution.State (EMPTY_CODE_HASH)
open LeanLightEvm

def bytesOf (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- `JUMPDEST PUSH1 0 JUMP`: a loop that only burns gas. -/
def jumpLoop : ByteArray := bytesOf [0x5b, 0x60, 0x00, 0x56]

/-- `PUSH1 1 JUMPDEST DUP1 BALANCE POP PUSH1 1 ADD PUSH1 2 JUMP`: `BALANCE` of 1, 2, 3, … -/
def balanceSweep : ByteArray :=
  bytesOf [0x60, 0x01, 0x5b, 0x80, 0x31, 0x50, 0x60, 0x01, 0x01, 0x60, 0x02, 0x56]

def creation (base : Case) (name : String) (data : ByteArray) (gas : Option Nat) : Case :=
  { base with name, kind := "adversarial", expect := .none, gas := none, logs := #[],
              estimate := none, overrides := #[]
              request := { sender := base.request.sender, to := none, data, value := 0, gas } }

def isUnsupported (o : Outcome) (p : Unsupported → Bool) : Bool :=
  match o with | .unsupported u => p u | _ => false

def isBudget (which : Budget) (o : Outcome) : Bool :=
  isUnsupported o fun | .budget w => w == which | _ => false

/-- The checks that do not depend on the chain, on one base case (run on a mainnet one and a
Sepolia one, so that each holds before and at Glamsterdam). -/
def perBase (t : Tally) (label : String) (f : VFile) (c : Case) : Tally := Id.run do
  let mut t := t
  let (_, fs, _) := baseline f c
  let zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩
  -- a BALANCE sweep: the round widths 4, 8, 16, 32, then 64 accounts in one round
  let d := discover f (creation c "balance sweep" balanceSweep none) fs (start := fs)
  t := t.check (isBudget .accountsPerRound d.outcome && d.rounds ≤ 8)
    s!"{label}: BALANCE sweep: {d.outcome.show} after {d.rounds} rounds"
  let sweepCase := creation c "balance sweep" balanceSweep none
  let o := runWith f sweepCase fs (round := 0)
  t := t.check (match o with | .needs n => n.keys ≤ 4 | _ => false)
    s!"{label}: BALANCE sweep, round 0, asks for at most 4 keys: {o.show}"
  -- keys per call: facts over 1,536 keys, then facts that the round's keys push over
  let pad (fs : Facts) (n : Nat) : Facts :=
    let a := c.request.sender
    let key (i : Nat) : Bytes32 := U256.toBeBytes (BitVec.ofNat 256 (i + 1000000))
    let padded := (List.range n).foldl (fun m i => m.insert (key i) 0) (fs.slots.getD a ∅)
    { fs with slots := fs.slots.insert a padded }
  let o := runWith f c (pad fs (1537 - fs.stateKeys))
  t := t.check (isBudget .stateKeys o) s!"{label}: facts of 1,537 keys: {o.show}"
  let o := runWith f sweepCase (pad fs (1532 - fs.stateKeys)) (round := 1)
  t := t.check (isBudget .stateKeys o) s!"{label}: 1,532 keys held and a round asking for 8: {o.show}"
  -- code bytes per call
  let big := zeros 600000 |>.push 1
  let o := runWith f c { fs with code := fs.code.insert (keccak big) big }
  t := t.check (isBudget .codeBytes o) s!"{label}: 600,001 bytes of code held: {o.show}"
  -- rounds
  let o := runWith f c fs (round := 32)
  t := t.check (isBudget .rounds o) s!"{label}: round 32: {o.show}"
  let o := runWith f c fs (round := 31)
  t := t.check o.isAnswer s!"{label}: round 31 still answers: {o.show}"
  -- kinds of request that are unsupported
  let o := runWith f { c with request := { c.request with authorizations := 1 } } fs
  t := t.check (isUnsupported o fun | .authorizations => true | _ => false) s!"{label}: authorization list: {o.show}"
  let o := runWith f { c with request := { c.request with blobs := 1 } } fs
  t := t.check (isUnsupported o fun | .blobs => true | _ => false) s!"{label}: blobs: {o.show}"
  -- code not under its hash: refused before the EVM runs
  match fs.code.toList with
  | (h, b) :: _ =>
    let bad : ByteArray := ⟨b.data.modify 0 (· ^^^ 1)⟩
    let o := runWith f c { fs with code := fs.code.insert h bad }
    t := t.check (isUnsupported o fun | .malformed (.codeHash h') => h' == h | _ => false)
      s!"{label}: code not matching its hash: {o.show}"
  | [] => t := t.check false s!"{label}: the base case holds no code"
  -- facts that cannot be one state's
  let ghost : Address := Vector.replicate 20 0x42
  let oneSlot : Std.ExtTreeMap Bytes32 U256 := (∅ : Std.ExtTreeMap Bytes32 U256).insert (Vector.replicate 32 0) 1
  let o := runWith f c
    { fs with accounts := fs.accounts.insert ghost .absent, slots := fs.slots.insert ghost oneSlot }
  t := t.check (isUnsupported o fun | .malformed (.slotWithoutAccount _) => true | _ => false)
    s!"{label}: a slot of an absent account: {o.show}"
  let emptyGhost : AccountFact := .present 0 0 EMPTY_CODE_HASH (some EMPTY_STORAGE_ROOT)
  let o := runWith f c
    { fs with accounts := fs.accounts.insert ghost emptyGhost, slots := fs.slots.insert ghost oneSlot }
  t := t.check (isUnsupported o fun | .malformed (.slotUnderEmptyRoot _) => true | _ => false)
    s!"{label}: a nonzero slot under the empty root: {o.show}"
  let o := runWith f c fs (ancestors := some [Vector.replicate 32 7])
  t := t.check (isUnsupported o fun | .malformed .ancestors => true | _ => false)
    s!"{label}: ancestors whose last is not the parent: {o.show}"
  -- an absent sender sending value: refused as a node refuses it
  let o := runWith f { c with request := { c.request with value := 1 } }
    { fs with accounts := fs.accounts.insert c.request.sender .absent, slots := fs.slots.erase c.request.sender }
  t := t.check (match o with | .refused .insufficientFunds => true | _ => false)
    s!"{label}: an absent sender sending 1 wei: {o.show}"
  -- the sender or the recipient unknown: nothing runs, they alone are asked for
  let o := runWith f c (withhold fs (.account c.request.sender))
  t := t.check (match o with | .needs n => n.accounts == [c.request.sender] | _ => false)
    s!"{label}: sender withheld: {o.show}"
  -- the recipient unknown: nothing runs, it alone is asked for
  if let some to := c.request.to then
    if to != c.request.sender then
      let o := runWith f c (withhold fs (.account to))
      t := t.check (match o with | .needs n => n.accounts == [to] | _ => false)
        s!"{label}: recipient withheld: {o.show}"
  return t

/-- The checks on one base case of each chain. -/
def adversarial (t : Tally) (mf : VFile) (mc : Case) (sf : VFile) (sc : Case) : Tally := Id.run do
  let mut t := t
  let (_, mfs, _) := baseline mf mc
  let (_, sfs, _) := baseline sf sc
  let zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩
  -- EIP-3860: refused before any run, at the fork's limit (49,152 to BPO2, 131,072 at Glamsterdam)
  let o := runWith mf (creation mc "init code 49153" (zeros 49153) none) mfs
  t := t.check (match o with | .refused (.initCodeTooLarge 49153) => true | _ => false)
    s!"mainnet init code of 49,153 bytes: {o.show}"
  let d := discover mf (creation mc "init code 49152" (zeros 49152) none) mfs (start := mfs)
  t := t.check (match d.outcome with | .answer a => a.result.ok | _ => false)
    s!"mainnet init code of 49,152 bytes of STOP deploys: {d.outcome.show}"
  let o := runWith sf (creation sc "init code 131073" (zeros 131073) none) sfs
  t := t.check (match o with | .refused (.initCodeTooLarge 131073) => true | _ => false)
    s!"Sepolia (Glamsterdam) init code of 131,073 bytes: {o.show}"
  let d := discover sf (creation sc "init code 49153" (zeros 49153) none) sfs (start := sfs)
  t := t.check (match d.outcome with | .answer a => a.result.ok | _ => false)
    s!"Sepolia (Glamsterdam) init code of 49,153 bytes deploys: {d.outcome.show}"
  -- a hostile loop sent with no gas: out of gas at the cap, so over budget
  let d := discover mf (creation mc "jump loop" jumpLoop none) mfs (start := mfs)
  t := t.check (isBudget .executionGas d.outcome) s!"jump loop with no gas named: {d.outcome.show}"
  -- at Glamsterdam the protocol's own split (EIP-8037) keeps execution gas under 2^24: the
  -- same loop is an honest out-of-gas answer there, not capped
  let d := discover sf (creation sc "jump loop" jumpLoop none) sfs (start := sfs)
  t := t.check (match d.outcome with
      | .answer a => !a.result.ok && a.result.error == some .outOfGas && !a.capped | _ => false)
    s!"Sepolia (Glamsterdam) jump loop with no gas named: {d.outcome.show}"
  -- gas named above the cap before Glamsterdam: refused before it runs
  let o := runWith mf (creation mc "jump loop 30M" jumpLoop (some 30000000)) mfs
  t := t.check (isBudget .executionGas o) s!"jump loop with 30,000,000 gas named: {o.show}"
  -- the same loop with gas named under the cap: an honest out-of-gas answer, not capped
  let d := discover mf (creation mc "jump loop 1M" jumpLoop (some 1000000)) mfs (start := mfs)
  t := t.check (match d.outcome with
      | .answer a => !a.result.ok && a.result.error == some .outOfGas && !a.capped | _ => false)
    s!"jump loop with 1,000,000 gas named: {d.outcome.show}"
  -- the fork table's edges
  let at' (ts : Nat) (chain : Nat) : Case := { mc with chainId := chain, header := { mc.header with timestamp := ts } }
  let o := runWith mf (at' reviewedHorizon 1) mfs
  t := t.check (isUnsupported o fun | .rules (.pastHorizon _) => true | _ => false) s!"at the horizon: {o.show}"
  let o := runWith mf (at' 1746612310 1) mfs
  t := t.check (isUnsupported o fun | .rules (.beforeTable _) => true | _ => false)
    s!"a second before mainnet's Pectra, the table's first row: {o.show}"
  let o := runWith mf (at' mc.header.timestamp 5) mfs
  t := t.check (isUnsupported o fun | .rules (.unknownChain 5) => true | _ => false) s!"chain 5: {o.show}"
  let forkAt (chain ts : Nat) : Option Fork := (rulesAt known chain ts).toOption.map (·.fork)
  t := t.check (forkAt 1 1764798550 == some .pectra && forkAt 1 1764798551 == some .fusaka &&
      forkAt 1 1767747670 == some .bpo1 && forkAt 1 1767747671 == some .bpo2 &&
      forkAt 11155111 1791294816 == some .glamsterdam && forkAt 11155111 1791294815 == some .bpo2)
    "fork table: BPO2 on mainnet from 1767747671, Glamsterdam on Sepolia from 1791294816"
  t := perBase t "mainnet" mf mc
  t := perBase t "Sepolia" sf sc
  t := t.check (vhex EMPTY_STORAGE_ROOT == "0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
    "EMPTY_STORAGE_ROOT is Keccak-256 of 0x80"
  return t

/-- The EIP-7610 holes: the partial requests (the candidate's storage withheld) must not
answer; the full ones, whose candidate's storage root is proved not empty, are unsupported. -/
def holes (t : Tally) (f : VFile) : Tally := Id.run do
  let mut t := t
  for c in f.cases do
    match c.expect with
    | .hole full cand =>
      -- other accounts with nonce 0 and no code (Sepolia's sender) get the empty root assumed
      let others := c.accounts.toList.filterMap fun (a, l) =>
        if a != cand && !l.absent && l.root.isNone then some a else none
      let o := runWith f c (c.facts f others)
      if full then
        t := t.check (isUnsupported o fun | .collisionUndecidable a => a == cand | _ => false)
          s!"{c.name}: candidate with a non-empty root: {o.show}"
      else
        t := t.check (match o with | .needs n => n.storageRoots.contains cand | _ => false)
          s!"{c.name}: candidate with no root: {o.show}"
    | _ => t := t.check false s!"{c.name}: not a hole case"
  return t

end LeanLightEvmTests
