/-
Kernel-only replay of ONE module with Lean's own kernel: load the environment as it was at the top
of the file (from .olean files), then re-check every declaration the module adds. This is what
`leanchecker <Module>` does, except that `leanchecker` also checks every module whose name has
<Module> as a prefix. Prints the time spent in the kernel replay alone.

    lake env lean --run KernelReplay.lean Mathlib.Logic.Basic
-/
import Lean
open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let [arg] := args | IO.eprintln "usage: KernelReplay.lean <Module.Name>"; return 2
  let module := arg.toName
  initSearchPath (← findSysroot)
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    IO.eprintln s!"object file '{mFile}' of module {module} does not exist"; return 1
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then IO.eprintln "failed to read module data"; return 1 else
  let (mod, _) := parts[0]
  let t0 ← IO.monoNanosNow
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let t1 ← IO.monoNanosNow
  let mut newConstants := {}
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  discard <| env.toKernelEnv.replay newConstants
  let t2 ← IO.monoNanosNow
  IO.println s!"replay_ok constants={newConstants.size} import_s={(t1 - t0).toFloat / 1e9} replay_s={(t2 - t1).toFloat / 1e9}"
  env.freeRegions
  return 0
