import LeanLightEvmTests.Adversarial
import LeanLight.Forks

/-!
# Synthetic worlds: `call` against `reference` on the full state

Each case is a small world written here (public-looking addresses `0xaa…`, no recorded data):
`call` runs from no facts, each round served from the world by `serve`, and its outcome is then
compared with `LeanLightEvm.reference` on the world's full state with the chain's 256 ancestors, as
`CallAgrees` states it (`AncestorsOf` holds by construction): an answer must be the reference's
result, a refusal the reference's refusal: the statement `LeanLightEvmProofs.call_agrees` proves,
run on concrete worlds.

The cases: the round widths of 0 (where an earlier version answered on a read it never
proved), a sub-call that runs out of gas only
because of the cap, `BLOCKHASH` at the edges of the 256, sender and recipient shapes, creations
and EIP-7610, refusals; the recursion-depth case (a CALL chain to depth 1024), hostile calls
(gas-burning loops, slot sweeps, pointer chases, code fan-out), the 64-bit header fields, the order of
the init-code and intrinsic-gas checks, and the fork table against EthLib's and the light
client's own tables.
-/

namespace LeanLightEvmTests.Synthetic

open EthLib.Base
open EthLib.Execution.Evm (EvmError)
open EthLib.Execution.State (EMPTY_CODE_HASH)
open LeanLightEvm
open LeanLightEvmTests

def bs (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- `0xaa00…00NNNN`: a synthetic address. -/
def ad (n : Nat) : Address := Vector.ofFn fun (i : Fin 20) =>
  if i.val = 19 then UInt8.ofNat (n % 256) else if i.val = 18 then UInt8.ofNat (n / 256 % 256)
  else if i.val = 0 then 0xaa else 0

def kb (k : Nat) : Bytes32 := U256.toBeBytes (BitVec.ofNat 256 k)
def p20 (a : Address) : List UInt8 := 0x73 :: a.toList
/-- `PUSH1 0 MSTORE PUSH1 32 PUSH1 0 RETURN`: return the top of the stack as one word. -/
def ret32 : List UInt8 := [0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3]
def balOf (x : Address) : ByteArray := bs (p20 x ++ [0x31] ++ ret32)
def bhOf (n : Nat) : ByteArray := bs ([0x61, UInt8.ofNat (n / 256), UInt8.ofNat (n % 256), 0x40] ++ ret32)
def revAfterBal (x : Address) : ByteArray := bs (p20 x ++ [0x31, 0x50, 0x60, 0, 0x60, 0, 0xfd])
def oogAfterBal (x : Address) : ByteArray := bs (p20 x ++ [0x31, 0x50, 0x5b, 0x60, 23, 0x56])
/-- CALL `b` with `g` gas, then return the success flag. -/
def callThen (b : Address) (g : Nat) : ByteArray :=
  bs ([0x60, 0, 0x60, 0, 0x60, 0, 0x60, 0, 0x60, 0] ++ p20 b ++
    [0x62, UInt8.ofNat (g / 65536), UInt8.ofNat (g / 256 % 256), UInt8.ofNat (g % 256), 0xf1] ++ ret32)
/-- CALL `b` with all the gas left, then return the success flag. -/
def callAll (b : Address) : ByteArray :=
  bs ([0x60, 0, 0x60, 0, 0x60, 0, 0x60, 0, 0x60, 0] ++ p20 b ++ [0x5a, 0xf1] ++ ret32)
/-- A loop of 1,000,000 iterations (about 20M gas), then STOP. -/
def burn : ByteArray := bs [0x63, 0x00, 0x0f, 0x42, 0x40, 0x5b, 0x60, 0x01, 0x90, 0x03, 0x80, 0x60, 0x05, 0x57, 0x00]
def sdTo (y : Address) : ByteArray := bs (p20 y ++ [0xff])
def coinbaseBal : ByteArray := bs ([0x41, 0x31] ++ ret32)
def create2Empty : ByteArray := bs ([0x60, 0, 0x60, 0, 0x60, 0, 0x60, 0, 0xf5] ++ ret32)
def gasProbe : ByteArray := bs ([0x5a] ++ ret32)
/-- Depth `d` from the call data, store `d + 1`, CALL itself with `d + 1` and all the gas left,
then return the word at 0: the callee's answer when it succeeded, else `d + 1`. So the top frame
returns the number of frames of the chain. -/
def selfDepth : ByteArray :=
  bs [0x60, 0x00, 0x35, 0x60, 0x01, 0x01, 0x60, 0x00, 0x52,
      0x60, 0x20, 0x60, 0x00, 0x60, 0x20, 0x60, 0x00, 0x60, 0x00, 0x30, 0x5a, 0xf1, 0x50,
      0x60, 0x20, 0x60, 0x00, 0xf3]

/-- `jump loop`. -/
def hJump : String :=
  "5b600056"

/-- `keccak(0 bytes) loop`. -/
def hKeccak : String :=
  "5b600060002050600056"

/-- `mulmod loop`. -/
def hMulmod : String :=
  "5b7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80800950600056"

/-- `bn254 2-pair pairing loop`. -/
def hPairing : String :=
  "61018061001e6000395b6020614000610180600060085afa5061000956001c76476f4def4bb94541d57ebba1193381ffa7aa76ada664dd31c16024c43f593034dd2920f673e204fee2811c678745fc819b55d3e9d294e45c9b03a76aef41209dd15ebff5d46c4bd888e51a93cf99a7329636c63514396b4a452003a35bf704bf11ca01483bfa8b34b43561848d28905960114c8ac04049af4b6315a416782bb8324af6cfc93537a2ad1a445cfd0ca2a71acd7ac41fadbf933c2a51be344d120a2a4cf30c1bf9845f20c6fe39e07ea2cce61f0c9bb048165fe5e4de877550111e129f1cf1097710d41c4ac70fcdfa5ba2023c6ff1cbeac322de49d1b6df7c2032c61a830e3c17286de9462bf242fca2883585b93870a73853face6a6bf411198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa"

/-- `modexp 32-byte loop`. -/
def hModexp : String :=
  "6100c061001e6000395b60206140006100c0600060055afa5061000956000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000002ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"

/-- The slot sweep: SLOAD of slot 0, 1, 2, … of the recipient. -/
def hSlotSweep : String := "5f5b805450600101600156"
/-- The pointer chase: `x = SLOAD(x)` from 0 until 0. -/
def hChase : String := "5f5b548015600b576001565b00"

def hexCode (s : String) : ByteArray := (unhex s).getD .empty

/-- One account of a synthetic world. -/
structure Acct where
  a : Address
  nonce : Nat := 0
  bal : Nat := 0
  code : ByteArray := .empty
  slots : List (Nat × Nat) := []

/-- A storage root that is not the empty one, for accounts given slots. -/
def nonEmptyRoot : Hash32 := keccak (bs [1, 2, 3])

/-- The world as facts: every listed account present with its storage root (the empty root when
it has no slot), its code and slots; `absent` proved absent. Anything else is absent too:
`serve` serves it so. -/
def world (xs : List Acct) (absent : List Address := []) : Facts := Id.run do
  let mut f : Facts := {}
  for x in xs do
    let ch := if x.code.size = 0 then EMPTY_CODE_HASH else keccak x.code
    let root := if x.slots.isEmpty then EMPTY_STORAGE_ROOT else nonEmptyRoot
    f := { f with accounts := f.accounts.insert x.a (.present x.nonce (BitVec.ofNat 256 x.bal) ch (some root)) }
    if x.code.size > 0 then f := { f with code := f.code.insert ch x.code }
    if !x.slots.isEmpty then
      let m := x.slots.foldl (fun (m : Std.ExtTreeMap Bytes32 U256) (k, v) => m.insert (kb k) (BitVec.ofNat 256 v)) ∅
      f := { f with slots := f.slots.insert x.a m }
  for a in absent do f := { f with accounts := f.accounts.insert a .absent }
  return f

def hashOf (n : Nat) : Hash32 := keccak (bs [UInt8.ofNat (n / 256), UInt8.ofNat (n % 256), 0x77])
def number : Nat := 1000
/-- The chain's 256 ancestors at `number`, oldest first, the parent's last. -/
def ancestorsFull : List Hash32 := (List.range 256).map fun i => hashOf (number - 256 + i)
def coinbaseA : Address := ad 0xc0
def hdr (ts : Nat) : Header :=
  { number, timestamp := ts, gasLimit := 60000000, coinbase := coinbaseA,
    prevRandao := keccak (bs [9]), excessBlobGas := 0, parentBeaconBlockRoot := keccak (bs [8]),
    slotNumber := 123456, parentHash := hashOf (number - 1) }

/-- Mainnet under BPO2, and Sepolia under Glamsterdam. -/
def mainnetTs : Nat := 1770000000
def sepoliaTs : Nat := 1792000000

structure Run where
  outcome : Outcome
  input : Input
  rounds : Nat

/-- `call` from `start`, each `needs` served from the world `orc` (`serve`), the ancestors given
when asked for. -/
def discoverW (orc : Facts) (chainId ts : Nat) (r : Request) (b : Budgets := {})
    (start : Facts := {}) (header : Header := hdr ts) : Run := Id.run do
  let mut fs := start
  let mut anc : Option (List Hash32) := none
  let mut inp : Input := { chainId, header, ancestors := anc, facts := fs, request := r }
  for round in [0:b.rounds + 1] do
    inp := { chainId, header, ancestors := anc, facts := fs, request := r, round }
    match call b inp with
    | .needs n =>
      let had := anc.isSome
      if n.ancestors then anc := some ancestorsFull
      let fs' := serve orc fs n
      if fs'.stateKeys == fs.stateKeys && fs'.code.size == fs.code.size && (had || !n.ancestors) then
        return { outcome := .needs n, input := inp, rounds := round + 1 }
      fs := fs'
    | o => return { outcome := o, input := inp, rounds := round + 1 }
  return { outcome := call b inp, input := inp, rounds := b.rounds + 1 }

/-- `CallAgrees` on one run: an answer is `reference`'s result on the full world with the 256
ancestors, a refusal its refusal; `needs` and `unsupported` claim nothing. -/
def agrees (b : Budgets) (orc : Facts) (r : Run) : Bool :=
  match r.outcome with
  | .answer a =>
    match reference b r.input ancestorsFull orc.toState with
    | some (.ok res) => sameResult res a.result
    | _ => false
  | .refused why =>
    match reference b r.input ancestorsFull orc.toState with
    | some (.error why') => why == why'
    | _ => false
  | _ => true

def showRef : Option (Except Refusal Result) → String
  | none => "none"
  | some (.error r) => s!"refused {repr r}"
  | some (.ok r) => s!"ok={r.ok} {errKind r.error} gas {r.gasUsed} {(toHex r.output).take 74}"

/-- The observed run that `call` performs once its checks pass (`prepare`, then
`Prepared.runObserved` on the facts), with the execution gas capped at `cap` and none of
`call`'s checks: for a run whose gas `call` refuses (above `maxExecutionGas`). -/
def observedRun (cap : Nat) (i : Input) : Option EthLib.Execution.Transactions.CallOutput :=
  match rulesAt i.table i.chainId i.header.timestamp with
  | .error _ => none
  | .ok rules =>
    match prepare rules i.chainId i.header i.ancestors cap i.request i.facts.toState with
    | .ok p => (p.runObserved i.facts i.header.number).toOption.map (·.1)
    | .error _ => none

/-- `observedRun`'s output as `call` would report it (`Prepared.result`: gas used, error,
output, refund, logs), so that it can be compared with `reference`'s whole result. -/
def observedResult (cap : Nat) (i : Input) : Option Result :=
  match rulesAt i.table i.chainId i.header.timestamp with
  | .error _ => none
  | .ok rules =>
    match prepare rules i.chainId i.header i.ancestors cap i.request i.facts.toState with
    | .ok p => (p.runObserved i.facts i.header.number).toOption.map fun (o, _) => p.result o
    | .error _ => none

def showObserved : Option EthLib.Execution.Transactions.CallOutput → String
  | none => "none"
  | some o => s!"ok={o.error.isNone} {errKind o.error} {(toHex o.output).take 74}"

def S : Address := ad 0x51
def X : Address := ad 0x58
def Y : Address := ad 0x59
def A : Address := ad 0xa1
def B : Address := ad 0xb1
def D : Address := ad 0xd1
def R : Address := ad 0xd0
def T : Address := ad 0xb0d6e

def base : List Acct := [{ a := S, bal := 10 ^ 18, nonce := 5 }, { a := coinbaseA, bal := 7 }]
def mk (extra : List Acct) (absent : List Address := []) : Facts := world (base ++ extra) absent
def req (to : Option Address) (data : ByteArray) (value : Nat := 0) (gas : Option Nat := none)
    (sender : Address := S) : Request :=
  { sender, to, data, value, gas }

def wordOut (n : Nat) : ByteArray := ⟨(U256.toBeBytes (BitVec.ofNat 256 n)).toArray⟩

/-- Every synthetic check. -/
def checks (t : Tally) : Tally := Id.run do
  let mut t := t
  let bd : Budgets := {}
  -- an agreement case: discovery, then `CallAgrees` against `reference`
  let mut agreeing := 0
  let cases : List (String × Nat × Nat × Facts × Request) :=
    let m := mainnetTs
    let s := sepoliaTs
    let created := (EthLib.Execution.Evm.createAddress S 5).toOption.getD (ad 0)
    let deleg := bs ([0xef, 0x01, 0x00] ++ D.toList)
    let sha := Vector.ofFn fun (i : Fin 20) => if i.val = 19 then (2 : UInt8) else 0
    let c2 := EthLib.Execution.Evm.create2Address A 0 .empty
    [("blockhash -1", 1, m, mk [{ a := A, code := bhOf (number - 1) }], req (some A) .empty),
     ("blockhash -2", 1, m, mk [{ a := A, code := bhOf (number - 2) }], req (some A) .empty),
     ("blockhash -256", 1, m, mk [{ a := A, code := bhOf (number - 256) }], req (some A) .empty),
     ("blockhash -257", 1, m, mk [{ a := A, code := bhOf (number - 257) }], req (some A) .empty),
     ("blockhash 0 (own block)", 1, m, mk [{ a := A, code := bhOf number }], req (some A) .empty),
     ("blockhash -2 at Glamsterdam", 11155111, s, mk [{ a := A, code := bhOf (number - 2) }], req (some A) .empty),
     ("sender absent, value 0", 1, m, mk [{ a := A, code := balOf A }] [ad 0x52], req (some A) .empty (sender := ad 0x52)),
     ("sender absent, value 1", 1, m, mk [{ a := A, code := balOf A }] [ad 0x52], req (some A) .empty 1 (sender := ad 0x52)),
     ("sender a contract", 1, m, mk [{ a := A, code := balOf A }, { a := ad 0x53, nonce := 1, bal := 100, code := bs [0x00] }], req (some A) .empty 1 (sender := ad 0x53)),
     ("sender delegated (7702)", 1, m, mk [{ a := A, code := balOf A }, { a := ad 0x54, nonce := 3, bal := 100, code := deleg }, { a := D, nonce := 1, code := bs [0x00] }], req (some A) .empty 1 (sender := ad 0x54)),
     ("to the sha256 precompile", 1, m, mk [{ a := sha }], req (some sha) (bs [1, 2, 3])),
     ("to the sha256 precompile, absent", 1, m, mk [] [sha], req (some sha) (bs [1, 2, 3])),
     ("to an absent account, with value", 1, m, mk [] [ad 0x60], req (some (ad 0x60)) .empty 1000),
     ("to a delegated account", 1, m, mk [{ a := ad 0x61, nonce := 1, code := deleg }, { a := D, nonce := 1, code := balOf X }, { a := X, bal := 9 }], req (some (ad 0x61)) .empty),
     ("to a delegated account, delegate absent", 1, m, mk [{ a := ad 0x61, nonce := 1, code := deleg }], req (some (ad 0x61)) .empty),
     ("creation", 1, m, mk [], req none (bs [0x00])),
     ("creation onto code (collision)", 1, m, mk [{ a := created, nonce := 1, code := bs [0x00] }], req none (bs [0x00])),
     ("creation onto a nonce (collision)", 1, m, mk [{ a := created, nonce := 1 }], req none (bs [0x00])),
     ("creation onto an empty candidate", 1, m, mk [{ a := created, bal := 1 }], req none (bs [0x00])),
     ("CREATE2 onto an empty candidate", 1, m, mk [{ a := A, nonce := 1, code := create2Empty }, { a := c2, bal := 3 }], req (some A) .empty),
     ("value above the balance", 1, m, mk [{ a := A, code := balOf A }], req (some A) .empty (10 ^ 18 + 1)),
     ("value equal to the balance", 1, m, mk [{ a := A, code := balOf A }], req (some A) .empty (10 ^ 18)),
     ("gas below the intrinsic", 1, m, mk [{ a := A, code := balOf A }], req (some A) .empty (gas := some 20999)),
     ("gas at the intrinsic", 1, m, mk [{ a := A, code := bs [0x00] }], req (some A) .empty (gas := some 21000)),
     ("GAS with 1,000,000 named", 1, m, mk [{ a := A, code := gasProbe }], req (some A) .empty (gas := some 1000000)),
     ("a read inside a reverting frame", 1, m, mk [{ a := A, code := callThen B 100000 }, { a := B, code := revAfterBal X }, { a := X, bal := 1 }], req (some A) .empty),
     ("a read inside a frame out of gas, 1M named", 1, m, mk [{ a := A, code := callThen B 30000 }, { a := B, code := oogAfterBal X }, { a := X, bal := 1 }], req (some A) .empty (gas := some 1000000)),
     ("a read inside a frame out of gas at Glamsterdam", 11155111, s, mk [{ a := A, code := callThen B 30000 }, { a := B, code := oogAfterBal X }, { a := X, bal := 1 }], req (some A) .empty),
     ("SELFDESTRUCT to an unknown beneficiary", 1, m, mk [{ a := A, bal := 5, code := sdTo Y }, { a := Y, bal := 1, code := bs [0x00] }], req (some A) .empty),
     ("SELFDESTRUCT to an absent beneficiary", 1, m, mk [{ a := A, bal := 5, code := sdTo Y }] [Y], req (some A) .empty),
     ("BALANCE of the coinbase", 1, m, mk [{ a := A, code := coinbaseBal }], req (some A) .empty),
     ("creation at Glamsterdam", 11155111, s, mk [], req none (bs [0x00])),
     ("GAS with no gas named at Glamsterdam", 11155111, s, mk [{ a := A, code := gasProbe }], req (some A) .empty),
     ("value to an absent account at Glamsterdam", 11155111, s, mk [] [ad 0x60], req (some (ad 0x60)) .empty 1000)]
  for (name, chainId, ts, orc, r) in cases do
    let run := discoverW orc chainId ts r
    let ok := agrees bd orc run
    if ok then agreeing := agreeing + 1
    t := t.check ok s!"synthetic {name}: {run.outcome.show}; reference {showRef (reference bd run.input ancestorsFull orc.toState)}"
    t := t.check (match run.outcome with | .needs _ => false | _ => true)
      s!"synthetic {name}: discovery did not end: {run.outcome.show}"
  t := t.note s!"synthetic: {agreeing} of {cases.length} cases agree with `reference` on the full world (CallAgrees, tested)"
  -- the round widths of 0: facts missing, no key may be asked; never an answer
  let w1 := mk [{ a := A, code := balOf X }, { a := X, bal := 42 }]
  let f1 := mk [{ a := A, code := balOf X }]
  let inp : Input := { chainId := 1, header := hdr mainnetTs, ancestors := none, facts := f1, request := req (some A) .empty }
  for (what, b) in [("firstWidth 0", ({ firstWidth := 0 } : Budgets)), ("maxWidth 0", { maxWidth := 0 })] do
    let o := call b inp
    t := t.check (isBudget .width o) s!"synthetic {what}, an accessed account not a fact: {o.show}"
  let o := call bd inp
  t := t.check (match o with | .needs n => n.accounts == [X] | _ => false) s!"synthetic default widths ask for the account: {o.show}"
  t := t.check (match reference bd inp ancestorsFull w1.toState with
      | some (.ok r) => r.output.data == (wordOut 42).data | _ => false)
    "synthetic: the account's balance in the full world is 42"
  -- a sub-call out of gas only because of the cap: over budget, not an answer
  let wc := mk [{ a := A, code := callAll B }, { a := B, code := burn }]
  let rc := discoverW wc 1 mainnetTs (req (some A) .empty)
  t := t.check (isBudget .executionGas rc.outcome) s!"synthetic capped sub-call: {rc.outcome.show}"
  let big : Budgets := { executionGas := 2 ^ 30 }
  t := t.check (match reference big rc.input ancestorsFull wc.toState, reference bd rc.input ancestorsFull wc.toState with
      | some (.ok r1), some (.ok r0) => r1.output.data == (wordOut 1).data && r0.output.data == (wordOut 0).data
      | _, _ => false)
    s!"synthetic capped sub-call: the sub-call succeeds with the header's gas and fails under the cap: {showRef (reference big rc.input ancestorsFull wc.toState)} / {showRef (reference bd rc.input ancestorsFull wc.toState)}"
  -- the same frame out of gas under a cap it did not need: a read in a frame given 30,000 gas
  let wo := mk [{ a := A, code := callThen B 30000 }, { a := B, code := oogAfterBal X }, { a := X, bal := 1 }]
  let ro := discoverW wo 1 mainnetTs (req (some A) .empty)
  t := t.check (isBudget .executionGas ro.outcome)
    s!"synthetic frame out of gas in a capped run (conservative): {ro.outcome.show}"
  -- recipient withheld: nothing runs, the recipient alone is asked for
  for (chainId, ts) in [(1, mainnetTs), (11155111, sepoliaTs)] do
    let o := call bd { chainId, header := hdr ts, ancestors := none, facts := mk [], request := req (some A) .empty }
    t := t.check (match o with | .needs n => n.accounts == [A] | _ => false) s!"synthetic recipient withheld, chain {chainId}: {o.show}"
  -- 64-bit header fields of 2^64
  for (chainId, ts) in [(1, mainnetTs), (11155111, sepoliaTs)] do
    let w := mk [{ a := A, code := balOf A }]
    for (what, h) in [("excessBlobGas", { hdr ts with excessBlobGas := 2 ^ 64 }), ("slotNumber", { hdr ts with slotNumber := 2 ^ 64 })] do
      let o := call bd { chainId, header := h, ancestors := none, facts := w, request := req (some A) .empty }
      t := t.check (isUnsupported o fun | .malformed .header => true | _ => false) s!"synthetic {what} = 2^64, chain {chainId}: {o.show}"
    let o := call bd { chainId, header := { hdr ts with excessBlobGas := 2 ^ 64 - 1 }, ancestors := none, facts := w, request := req (some A) .empty }
    t := t.check o.isAnswer s!"synthetic excessBlobGas = 2^64 - 1, chain {chainId}, still runs: {o.show}"
  -- the order of the init-code and intrinsic-gas checks: a creation failing both
  let zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩
  let o := call bd { chainId := 1, header := hdr mainnetTs, ancestors := none, facts := mk [], request := req none (zeros 49153) (gas := some 21000) }
  t := t.check (match o with | .refused .intrinsicGasTooLow => true | _ => false)
    s!"synthetic mainnet: init code 49,153 bytes and gas 21,000: intrinsic first: {o.show}"
  let o := call bd { chainId := 11155111, header := hdr sepoliaTs, ancestors := none, facts := mk [], request := req none (zeros 131073) (gas := some 21000) }
  t := t.check (match o with | .refused (.initCodeTooLarge 131073) => true | _ => false)
    s!"synthetic Glamsterdam: init code 131,073 bytes and gas 21,000: init code first: {o.show}"
  -- recursion depth: a CALL chain to depth 1024 under 2^40 gas, and the
  -- deepest chain the cap allows; both must answer, the first with 1,025 frames. `call` refuses
  -- budgets above `maxExecutionGas`, so the chain to depth 1024 runs the
  -- observed run `call` performs (`observedRun`), and `reference`, directly
  let wd := mk [{ a := R, code := selfDepth }]
  let deep : Budgets := { executionGas := 2 ^ 40 }
  let rdIn : Input := { chainId := 1, header := hdr mainnetTs, ancestors := none, facts := wd,
                        request := req (some R) .empty (gas := some (2 ^ 40)) }
  t := t.check (isBudget .executionGas (call deep rdIn))
    s!"synthetic budgets of 2^40 execution gas, above maxExecutionGas: {(call deep rdIn).show}"
  t := t.check (match observedRun (2 ^ 40) rdIn with
      | some o => o.error.isNone && o.output.data == (wordOut 1025).data | none => false)
    s!"synthetic CALL chain to depth 1024, observed run: {showObserved (observedRun (2 ^ 40) rdIn)}"
  -- the observed run and the plain one agree on the whole result at depth 1024 (gas used,
  -- error, output, refund, logs), as `agrees` compared them before `call` refused 2^40
  t := t.check (match observedResult (2 ^ 40) rdIn, reference deep rdIn ancestorsFull wd.toState with
      | some x, some (.ok y) => sameResult x y | _, _ => false)
    s!"synthetic CALL chain to depth 1024, observed run against reference: {(observedResult (2 ^ 40) rdIn).map (fun r => s!"ok={r.ok} {errKind r.error} gas {r.gasUsed}")} / {showRef (reference deep rdIn ancestorsFull wd.toState)}"
  t := t.check (match reference deep rdIn ancestorsFull wd.toState with
      | some (.ok r) => r.ok && r.output.data == (wordOut 1025).data | _ => false)
    s!"synthetic CALL chain to depth 1024, reference: {showRef (reference deep rdIn ancestorsFull wd.toState)}"
  -- the ceilings: budgets above maxExecutionGas, a code fact above
  -- maxCodeFact; the largest of each still runs
  let over : Budgets := { executionGas := maxExecutionGas + 1 }
  let o := call over rdIn
  t := t.check (isBudget .executionGas o) s!"synthetic budgets of maxExecutionGas + 1: {o.show}"
  let atMax : Budgets := { executionGas := maxExecutionGas }
  let o := (discoverW wd 1 mainnetTs (req (some R) .empty (gas := some 16000000)) atMax).outcome
  t := t.check o.isAnswer s!"synthetic budgets of maxExecutionGas: {o.show}"
  for (size, refused) in [(maxCodeFact + 1, true), (maxCodeFact, false)] do
    let big := bs ([0x60, 0x2a] ++ ret32 ++ List.replicate (size - 10) 0x5b)
    let wb := mk [{ a := A, code := big }]
    let o := call bd { chainId := 1, header := hdr mainnetTs, ancestors := none, facts := wb,
                       request := req (some A) .empty }
    t := t.check (if refused then isBudget .codeBytes o else
        match o with | .answer a => a.result.output.data == (wordOut 42).data | _ => false)
      s!"synthetic code fact of {size} bytes: {o.show}"
  -- the request's own data: at most maxRequestData
  -- bytes runs (the IDENTITY precompile echoes it), one byte more is over budget before
  -- anything runs, as a creation's init code is
  let pa : Address := Vector.ofFn fun i => if i.val = 19 then 4 else 0
  for (size, refused) in [(maxRequestData + 1, true), (maxRequestData, false)] do
    let o := call bd { chainId := 1, header := hdr mainnetTs, ancestors := none, facts := mk [] [pa],
                       request := req (some pa) (zeros size) }
    t := t.check (if refused then isBudget .dataBytes o else
        match o with | .answer a => a.result.ok && a.result.output.size == size | _ => false)
      s!"synthetic request data of {size} bytes: {o.show}"
  let o := call bd { chainId := 11155111, header := hdr sepoliaTs, ancestors := none, facts := mk [],
                     request := req none (zeros (maxRequestData + 1)) }
  t := t.check (isBudget .dataBytes o) s!"synthetic init code of maxRequestData + 1 bytes: {o.show}"
  let rd := discoverW wd 1 mainnetTs (req (some R) .empty (gas := some 16000000))
  t := t.check (match rd.outcome with | .answer a => a.result.ok && !a.capped | _ => false)
    s!"synthetic CALL chain under 16,000,000 gas: {rd.outcome.show}"
  t := t.note s!"synthetic CALL chain under 16,000,000 gas (the cap): {rd.outcome.show}"
  -- hostile calls sent with no gas: refused, never answered
  for (name, code) in [("jump loop", hJump), ("keccak(0 bytes) loop", hKeccak), ("mulmod loop", hMulmod),
      ("modexp 32-byte loop", hModexp)] do
    let r := discoverW (mk []) 1 mainnetTs (req none (hexCode code))
    t := t.check (isBudget .executionGas r.outcome) s!"hostile {name}, no gas named: {r.outcome.show}"
  -- the pairing loop costs about 7 s at the cap: run at 2^20 named
  let r := discoverW (mk []) 1 mainnetTs (req none (hexCode hPairing) (gas := some 1048576))
  t := t.check (match r.outcome with | .answer a => a.result.error == some .outOfGas && !a.capped | _ => false)
    s!"hostile bn254 pairing loop at 1,048,576 gas: {r.outcome.show}"
  let ws := mk [{ a := T, code := hexCode hSlotSweep, slots := [(1000000, 1)] }]
  let r := discoverW ws 1 mainnetTs (req (some T) .empty)
  t := t.check (isUnsupported r.outcome fun | .budget _ => true | _ => false)
    s!"hostile slot sweep: {r.outcome.show} after {r.rounds} rounds"
  let wch := mk [{ a := T, code := hexCode hChase, slots := (List.range 64).map fun i => (i, i + 1) }]
  let r := discoverW wch 1 mainnetTs (req (some T) .empty)
  t := t.check (isBudget .rounds r.outcome) s!"hostile pointer chase over 64 slots: {r.outcome.show} after {r.rounds} rounds"
  let fan := (List.range 40).map fun i => ad (0xfa00 + i)
  let fanCode := bs ((fan.flatMap fun a => [0x5f, 0x5f, 0x5f, 0x5f, 0x5f] ++ p20 a ++ [0x5a, 0xf1, 0x50]) ++ [0x00])
  let wf := mk ({ a := T, code := fanCode } :: (fan.zipIdx.map fun (a, i) =>
    { a, nonce := 1, code := ⟨#[0x00] ++ Array.replicate 24575 (UInt8.ofNat (i + 1))⟩ }))
  let r := discoverW wf 1 mainnetTs (req (some T) .empty)
  t := t.check (isBudget .codeBytes r.outcome) s!"hostile code fan-out (40 × 24,576 bytes): {r.outcome.show} after {r.rounds} rounds"
  -- the fork table against EthLib's mainnet configuration, its blob schedules, and the light
  -- client's epochs
  t := t.check (known.length == 2) s!"fork table: {known.length} chains derived from LeanLight.Lc.Forks"
  let rowsOf (c : Option ChainRules) : List LeanLightEvm.Activation := (c.map (·.activations)).getD []
  for row in rowsOf LeanLightEvm.mainnet do
    t := t.check ((EthLib.Base.ChainConfig.mainnet.activeFork 30000000 row.timestamp) == some row.fork &&
        (EthLib.Base.ChainConfig.mainnet.activeFork 30000000 (row.timestamp - 1)) != some row.fork)
      s!"fork table: mainnet row at {row.timestamp} is EthLib's {repr row.fork}"
  for c in known do
    for row in c.activations do
      let ok := if h : Fork.dencun ≤ row.fork then
          let s := EthLib.Execution.Fees.BlobBaseFee.blobSchedule row.fork h
          s.target == row.blobSchedule.target && s.max == row.blobSchedule.max &&
            s.baseFeeUpdateFraction == row.blobSchedule.baseFeeUpdateFraction
        else false
      t := t.check ok
        s!"fork table: chain {c.chainId} row at {row.timestamp}: blob schedule is EthLib's for {repr row.fork}"
  let atEpoch (c : LeanLight.Lc.Forks.Chain) (epoch : Nat) : Nat := c.genesisTime + epoch * 384
  let lc := LeanLight.Lc.Forks.mainnet
  let ls := LeanLight.Lc.Forks.sepolia
  let electra (c : LeanLight.Lc.Forks.Chain) : Nat := ((c.forks.find? fun f => f.name == .electra).map (·.epoch)).getD 0
  let fulu (c : LeanLight.Lc.Forks.Chain) : Nat := ((c.forks.find? fun f => f.name == .fulu).map (·.epoch)).getD 0
  let gloas (c : LeanLight.Lc.Forks.Chain) : Nat := ((c.forks.find? fun f => f.name == .gloas).map (·.epoch)).getD 0
  let expectM := [(atEpoch lc (electra lc), 9), (atEpoch lc (fulu lc), 9)] ++ lc.blobSchedule.map fun (e, m) => (atEpoch lc e, m)
  let gotM := (rowsOf LeanLightEvm.mainnet).map fun a => (a.timestamp, a.blobSchedule.max)
  t := t.check (expectM == gotM) s!"fork table: mainnet rows {gotM} are LeanLight.Lc.Forks' {expectM}"
  let expectS := [(atEpoch ls (electra ls), 9), (atEpoch ls (fulu ls), 9)] ++ ls.blobSchedule.map (fun (e, m) => (atEpoch ls e, m)) ++ [(atEpoch ls (gloas ls), 21)]
  let gotS := (rowsOf LeanLightEvm.sepolia).map fun a => (a.timestamp, a.blobSchedule.max)
  t := t.check (expectS == gotS) s!"fork table: Sepolia rows {gotS} are LeanLight.Lc.Forks' {expectS}"
  -- the reviewed values, as numbers: Osaka, BPO1, BPO2 and (Sepolia) Glamsterdam
  let forks (c : Option ChainRules) := (rowsOf c).map fun a => (a.timestamp, a.fork)
  t := t.check (forks LeanLightEvm.mainnet == [(1746612311, .pectra), (1764798551, .fusaka),
      (1765290071, .bpo1), (1767747671, .bpo2)]) s!"fork table: mainnet's rows {repr (forks LeanLightEvm.mainnet)}"
  t := t.check (forks LeanLightEvm.sepolia == [(1741159776, .pectra), (1760427360, .fusaka),
      (1761017184, .bpo1), (1761607008, .bpo2), (1791294816, .glamsterdam)])
    s!"fork table: Sepolia's rows {repr (forks LeanLightEvm.sepolia)}"
  return t

end LeanLightEvmTests.Synthetic
