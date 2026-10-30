import LeanLightCli.Client

/-!
# Recording a run, for the offline tests and benchmark

`leanlight record DIR [QUERIES]` fetches what a run needs once and writes it to `DIR`, after
running it through `LeanLight.Driver` (so a recording the light client would refuse is never
written):

| File | What |
|---|---|
| `meta.txt` | `key value` lines: `network`, `now_ms` (the clock at recording), `checkpoint`, the forks of the bootstrap and of the finality and optimistic updates, `anchor_hash`, `block`, `periods` (how many sync periods the updates span) |
| `bootstrap.ssz` | `light_client/bootstrap/{checkpoint}` |
| `updates.ssz` | one `light_client/updates` answer from the checkpoint's period to the clock's (SSZ chunks) |
| `finality.ssz`, `optimistic.ssz` | the finality and optimistic updates |
| `block.json` | `eth_getBlockByHash` of the anchored execution block |
| `reads.txt` | one line per read: the query, then `proof-N.json` and, for `code`, `code-N.hex` |

The JSON files are the endpoint's `result`s as the client's JSON writes them. Nothing here is
trusted by the tests: they check every byte through `LeanLight.Driver` as a live run does.
-/

namespace LeanLight.Cli.Record

open LeanLight.Lc

def forkName : Forks.ForkName → String
  | .electra => "electra"
  | .fulu => "fulu"
  | .gloas => "gloas"

/-- Writes a recording of a run against `cfg` to `dir`: the store from `cfg`'s checkpoint (or, when
`cfg.unsafeUntrustedCheckpoint` is set, the node's finalized root) through every period up to the
clock's, the anchored block, and each of `queries`' calls at it. -/
def record (cfg : Config) (dir : System.FilePath)
    (queries : List (String × (ByteArray → List (String × Json)))) : IO Unit := do
  IO.FS.createDirAll dir
  let root ← checkpointOf cfg
  let now ← nowMs
  let lc := s!"{cfg.consensus}/eth/v1/beacon/light_client"
  let (bbs, bv) ← orDie "bootstrap" (← getSsz s!"{lc}/bootstrap/{toHex root}")
  let some bfork := bv.bind forkOfName | die s!"bootstrap: fork {bv} unknown"
  let some s0 := Driver.start cfg.chain root now (.name bfork) bbs
    | die "bootstrap: refused"
  let p := Store.period cfg.chain s0
  let cur := cfg.chain.periodAt (cfg.chain.slotOf now)
  let count := min 128 (cur - p + 1)
  let (ubs, _) ← orDie "updates" (← getSsz s!"{lc}/updates?start_period={p}&count={count}")
  let some chunks := Ssz.parseUpdates ubs | die "updates: bad framing"
  let mut s := s0
  for ch in chunks do
    s := (Driver.feed cfg.chain s now .update (.digest ch.digest) ch.ssz).1
  let mut forks : List (String × Forks.ForkName) := []
  let mut objs : List (String × ByteArray) := []
  for (k, path, file) in [(Codec.Kind.finality, "finality_update", "finality"),
      (.optimistic, "optimistic_update", "optimistic")] do
    let (bs, v) ← orDie path (← getSsz s!"{lc}/{path}")
    let some f := v.bind forkOfName | die s!"{path}: fork {v} unknown"
    s := (Driver.feed cfg.chain s now k (.name f) bs).1
    forks := forks ++ [(file, f)]
    objs := objs ++ [(file, bs)]
  let some a := Store.anchored cfg.chain s now | die "the recorded run does not anchor"
  let hash := a.header.elHash
  let (bm, bp) := blockCall hash
  let block ← orDie "eth_getBlockByHash" (← rpc cfg.execution bm bp)
  let rlp ← orDie "header" (headerRlp block)
  let some el := Anchor.bind cfg.chain a.header rlp | die "header: does not bind to the anchor"
  IO.FS.writeBinFile (dir / "bootstrap.ssz") bbs
  IO.FS.writeBinFile (dir / "updates.ssz") ubs
  for (file, bs) in objs do IO.FS.writeBinFile (dir / s!"{file}.ssz") bs
  IO.FS.writeFile (dir / "block.json") block.compress
  let mut lines : Array String := #[]
  let mut n := 0
  for (q, calls) in queries do
    let mut files : Array String := #[]
    for (m, ps) in calls hash do
      let r ← orDie m (← rpc cfg.execution m ps)
      if m == "eth_getCode" then
        let file := s!"code-{n}.hex"
        IO.FS.writeFile (dir / file) (← orDie "eth_getCode" r.getStr?)
        files := files.push file
      else
        let file := s!"proof-{n}.json"
        IO.FS.writeFile (dir / file) r.compress
        files := files.push file
    lines := lines.push (String.intercalate "\t" (q :: files.toList))
    n := n + 1
  IO.FS.writeFile (dir / "reads.txt") (String.intercalate "\n" lines.toList ++ "\n")
  let network := if cfg.chain.chainId == 1 then "mainnet" else "sepolia"
  let info := [("network", network), ("now_ms", toString now), ("checkpoint", toHex root),
    ("bootstrap_fork", forkName bfork)] ++ forks.map (fun (f, k) => (s!"{f}_fork", forkName k)) ++
    [("anchor_hash", toHex hash), ("block", toString el.number), ("periods", toString count)]
  IO.FS.writeFile (dir / "meta.txt")
    (String.intercalate "\n" (info.map fun (k, v) => s!"{k} {v}") ++ "\n")
  IO.println s!"recorded {dir}: checkpoint {toHex root}, {chunks.size} period updates, block {el.number}, {queries.length} reads"

end LeanLight.Cli.Record
