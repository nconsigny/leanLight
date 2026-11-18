import EthLib.Base.Fork
import EthLib.Base.BlobSchedule
import LeanLight.Forks

/-!
# Which rules a call runs under

The rules (EthLib's fork and the blob schedule of EIP-7892) are chosen from the anchored header's
chain id and timestamp against a table, never named by a caller: a wrong fork gives a wrong
`BLOBBASEFEE` (EthLib's `.fusaka` carries Pectra's blob schedule, while mainnet runs BPO2's) or
a wrong opcode set, with nothing refusing it. Past a chain's horizon, or before its first row,
the call is refused rather than run under a guess.

The table is derived from the light client's own chain table, `LeanLight.Lc.Forks` (`ofForks`),
so the EVM and the light client cannot disagree about when a fork activates: an execution-layer
fork activates at the first slot of its consensus fork's epoch, `slotTime (startSlot epoch)`.

* Electra runs EthLib's `.pectra` and Fulu `.fusaka`, both with Pectra's blob schedule (6 / 9).
* The k-th entry of the consensus `BLOB_SCHEDULE` (EIP-7892's BPO forks) runs `.bpo1` to `.bpo5`,
  with the schedule its maximum names (`blobsOf`; only the maxima mainnet and Sepolia use, 15
  and 21, are known: any other fails the derivation).
* Gloas runs `.glamsterdam`, under the last BPO's schedule.

A consumer that follows another chain, or reviewed a later fork, passes its own `ChainRules`
(`LeanLightEvm.Input.table`); the default, `known`, is mainnet and Sepolia up to
`reviewedHorizon`.
-/

namespace LeanLightEvm

open EthLib.Base (BlobSchedule Fork)
open LeanLight.Lc.Forks (ForkName)

/-- From `timestamp` on (inclusive), blocks run under `fork` with the blob schedule
`blobSchedule`. -/
structure Activation where
  /-- The first timestamp of the fork, in seconds since the Unix epoch. -/
  timestamp : Nat
  /-- EthLib's name for the fork's rules. -/
  fork : Fork
  /-- The blob schedule of EIP-7892 from that timestamp on. -/
  blobSchedule : BlobSchedule
  deriving Repr

/-- A chain the EVM may run calls of. -/
structure ChainRules where
  /-- The chain id of EIP-155. -/
  chainId : Nat
  /-- The activations, oldest first. -/
  activations : List Activation
  /-- The first timestamp the table does not cover: a header at or past it is refused, since a
  fork scheduled after the table was reviewed would otherwise run under the previous rules. -/
  horizon : Nat
  deriving Repr

/-- Pectra's and Osaka's blob schedule: 6 / 9, update fraction 5007716 (EIP-7691, EIP-7892). -/
def pectraBlobs : BlobSchedule := { target := 6, max := 9, baseFeeUpdateFraction := 5007716 }

/-- BPO1's on mainnet and Sepolia: 10 / 15, update fraction 8346193. -/
def bpo1Blobs : BlobSchedule := { target := 10, max := 15, baseFeeUpdateFraction := 8346193 }

/-- BPO2's on mainnet and Sepolia: 14 / 21, update fraction 11684671. -/
def bpo2Blobs : BlobSchedule := { target := 14, max := 21, baseFeeUpdateFraction := 11684671 }

/-- The execution layer's blob schedule of a BPO entry, from the maximum the consensus layer's
`BLOB_SCHEDULE` gives (the target and the update fraction are execution-layer configuration,
which the consensus table does not carry). Only the two entries mainnet and Sepolia run are
known. -/
def blobsOf : Nat → Option BlobSchedule
  | 15 => some bpo1Blobs
  | 21 => some bpo2Blobs
  | _ => none

/-- EthLib's fork of the k-th BPO entry (0-based). -/
def bpoFork : Nat → Option Fork
  | 0 => some .bpo1
  | 1 => some .bpo2
  | 2 => some .bpo3
  | 3 => some .bpo4
  | 4 => some .bpo5
  | _ => none

/-- 2027-03-01T00:00:00Z: the horizon of `known`, to be moved only by a reviewed edit (with the
next fork's row in `LeanLight.Lc.Forks`, once scheduled). -/
def reviewedHorizon : Nat := 1803859200

/-- The activation time, in seconds, of the consensus epoch `epoch` of chain `c`. -/
def activationTime (c : LeanLight.Lc.Forks.Chain) (epoch : Nat) : Nat :=
  c.slotTime (c.startSlot epoch) / 1000

/-- Inserts an activation into a list sorted by timestamp, after those at the same time. -/
def insertSorted (a : Activation) : List Activation → List Activation
  | [] => [a]
  | b :: rest => if a.timestamp < b.timestamp then a :: b :: rest else b :: insertSorted a rest

/-- The rules of chain `c` from its consensus table, up to `horizon`; none when the table names a
blob maximum or a BPO index this module does not know. The consensus forks from Electra on and
the BPO entries, oldest first; Gloas takes the blob schedule of the last BPO before it. -/
def ofForks (c : LeanLight.Lc.Forks.Chain) (horizon : Nat) : Option ChainRules := do
  let mut bpos : List Activation := []
  let mut k := 0
  for (epoch, maxBlobs) in c.blobSchedule do
    let fork ← bpoFork k
    let blobs ← blobsOf maxBlobs
    bpos := bpos ++ [⟨activationTime c epoch, fork, blobs⟩]
    k := k + 1
  let mut rows := bpos
  for f in c.forks do
    let t := activationTime c f.epoch
    let blobsBefore := ((bpos.filter (·.timestamp ≤ t)).getLast?.map (·.blobSchedule)).getD pectraBlobs
    let row : Activation := match f.name with
      | .electra => ⟨t, .pectra, pectraBlobs⟩
      | .fulu => ⟨t, .fusaka, pectraBlobs⟩
      | .gloas => ⟨t, .glamsterdam, blobsBefore⟩
    rows := insertSorted row rows
  return { chainId := c.chainId, activations := rows, horizon }

/-- Mainnet's rules, from `LeanLight.Lc.Forks.mainnet`: Pectra, Osaka (`.fusaka`) at epoch
411392 (1764798551), BPO1 at 412672 (1765290071), BPO2 at 419072 (1767747671). -/
def mainnet : Option ChainRules := ofForks LeanLight.Lc.Forks.mainnet reviewedHorizon

/-- Sepolia's rules, from `LeanLight.Lc.Forks.sepolia`: Pectra, Osaka at epoch 272640
(1760427360), BPO1 at 274176 (1761017184), BPO2 at 275712 (1761607008), Glamsterdam (Gloas) at
353024 (1791294816), under BPO2's blob schedule. -/
def sepolia : Option ChainRules := ofForks LeanLight.Lc.Forks.sepolia reviewedHorizon

/-- The default table: every chain leanLight follows, up to `reviewedHorizon`. -/
def known : List ChainRules := [mainnet, sepolia].filterMap id

/-- Why the table gives no rules for a header. -/
inductive TableGap where
  /-- No row for the chain id. -/
  | unknownChain (chainId : Nat)
  /-- A timestamp before the chain's first row. -/
  | beforeTable (timestamp : Nat)
  /-- A timestamp at or past the chain's horizon. -/
  | pastHorizon (timestamp : Nat)
  deriving Repr, DecidableEq

/-- The last activation at or before `timestamp`, in a list sorted oldest first. -/
def lastActive (timestamp : Nat) : List Activation → Option Activation → Option Activation
  | [], found => found
  | a :: rest, found => if a.timestamp ≤ timestamp then lastActive timestamp rest (some a) else found

/-- The rules of a header of chain `chainId` at `timestamp` in `table`, or why there are none. -/
def rulesAt (table : List ChainRules) (chainId timestamp : Nat) : Except TableGap Activation := do
  let some c := table.find? (·.chainId == chainId) | throw (.unknownChain chainId)
  if c.horizon ≤ timestamp then throw (.pastHorizon timestamp)
  let some a := lastActive timestamp c.activations none | throw (.beforeTable timestamp)
  return a

end LeanLightEvm
