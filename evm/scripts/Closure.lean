import Lean

/-!
Prints the import closure of the modules named on the command line, one module a line, as
`evm/scripts/check-runtime.sh` reads it: run with `lake env lean --run scripts/Closure.lean M...`
from `evm/`. The closure is the environment's own (`importModules`), not a reading of the
sources' import lines.
-/

open Lean

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules (args.toArray.map fun m => { module := m.toName }) {} (loadExts := false)
  for m in env.header.moduleNames do
    IO.println m
  return 0
