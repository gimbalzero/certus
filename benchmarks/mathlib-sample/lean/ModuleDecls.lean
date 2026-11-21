/-
Print the declarations a module defines itself (not the ones it imports), one per line, in a form
lean4export accepts after `--`. These are the roots of the module's dependency closure.

    lake env lean --run ModuleDecls.lean Mathlib.Logic.Basic
-/
import Lean
open Lean

def main (args : List String) : IO UInt32 := do
  let [arg] := args | IO.eprintln "usage: ModuleDecls.lean <Module.Name>"; return 2
  let mod := arg.toName
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := mod }] {}
  let some idx := env.getModuleIdx? mod | IO.eprintln s!"module {mod} not loaded"; return 1
  let mut skipped := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n != some idx || n.isInternal then continue
    let s := toString n
    -- lean4export parses its arguments with `decodeNameLit`; only print names that round-trip.
    if Syntax.decodeNameLit ("`" ++ s) == some n then IO.println s else skipped := skipped + 1
  if skipped > 0 then IO.eprintln s!"skipped {skipped} names that do not round-trip"
  return 0
