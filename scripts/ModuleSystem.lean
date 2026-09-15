/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Adapted for this repository from `scripts/ModuleSystem.lean` of the Tau Ceti project
(<https://github.com/TauCetiProject/TauCeti>) at commit `37ae92f8170796e94b66279ea66f8635d9ca2aa0`.
Changes: the audited library root is `ArithmeticHeights` rather than `TauCeti`, and the module
enumeration no longer prepends a root module, because this library has none.
The pristine original is `~/math/TauCeti/scripts/ModuleSystem.lean`; everything else is upstream's.
-/
import Lean

/-!
# `module-system`: enforce that every `ArithmeticHeights` file opts into the module system

The repository's module-system gate. This executable inspects the built `.olean`s of the
`ArithmeticHeights` library and fails unless **every** module in `ArithmeticHeights` was
elaborated with the `module` keyword, i.e. opts into the Lean module system.

The signal is read from the compiled artifact, not the source text: each module's
`ModuleData.isModule` flag is set by the frontend exactly when the file began with
`module`. Reading it back from the `.olean` therefore certifies the real compilation, not a
textual `grep` that a stray `module` in a comment or string could fool. Run via
`lake exe module-system` (after `lake build`).

It reads each module's main `.olean` directly with `readModuleData` rather than importing
the whole environment: we only need one `Bool` per module, so there is no reason to load
the transitive Mathlib closure. This is the same way Lean's own `readModuleDataPartsOfMod`
and Lake's builtin linter obtain `isModule`. A module-system `.olean` is split into parts
(`.olean`, `.olean.private`, `.olean.server`), but `isModule` lives in the main `.olean`
part, which `readModuleData` loads on its own; we copy the `Bool` out and free the region.
-/

open Lean

/-- The library whose modules must opt into the module system (the AI-owned mathematics). -/
def auditedRoot : Name := `ArithmeticHeights

/-- The module name for a `.lean` source path, e.g.
`ArithmeticHeights/Foo/Bar.lean ↦ ArithmeticHeights.Foo.Bar`. -/
def pathToModule (p : System.FilePath) : Name :=
  (p.withExtension "").components.foldl (fun n s => Name.mkStr n s) Name.anonymous

/-- Every `.lean` module under `dir`, recursively. -/
partial def collectLeanModules (dir : System.FilePath) : IO (Array Name) := do
  let mut acc := #[]
  for entry in (← dir.readDir) do
    if (← entry.path.isDir) then
      acc := acc ++ (← collectLeanModules entry.path)
    else if entry.path.extension == some "lean" then
      acc := acc.push (pathToModule entry.path)
  return acc

/-- Every module in the `ArithmeticHeights` library: all of `ArithmeticHeights/**/*.lean`.
Enumerating the source tree, rather than importing a root, is what keeps the audit independent
of the Lake glob: a module orphaned from every root is audited just the same.

Unlike Tau Ceti, this library has no root module at all — `lakefile.lean` globs `.submodules`
and nothing re-exports the library — so the root is not prepended here. Add it back if a root
module is ever introduced. -/
def auditedModules : IO (Array Name) :=
  collectLeanModules (auditedRoot.toString : System.FilePath)

/-- Read `isModule` out of `modData` in its own frame. The `@[noinline]` (mirroring Lake's
builtin linter) ends `modData`'s lifetime here, so the runtime drops its reference into the
mmap'd region *before* the caller frees that region — reading the `Bool` afterwards, or
letting `modData`'s reference outlive the `free`, is a use-after-free that segfaults. -/
@[noinline] def getIsModule (modData : Lean.ModuleData) : BaseIO Bool :=
  return modData.isModule

/-- Did module `m` opt into the module system? Reads `isModule` from its main `.olean`.
Returns `none` if the `.olean` is missing (a build/wiring fault, reported as a violation). -/
def moduleIsOptedIn (m : Name) : IO (Option Bool) := do
  let olean ← findOLean m
  if !(← olean.pathExists) then return none
  let (data, region) ← readModuleData olean
  let isModule ← getIsModule data
  unsafe region.free
  return some isModule

-- Return the exit code rather than calling `IO.Process.exit`, matching `scripts/Axioms.lean`.
def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let modules ← auditedModules
  let mut bad : Array Name := #[]
  for m in modules do
    match ← moduleIsOptedIn m with
    | some true => pure ()
    | some false => bad := bad.push m
    | none => IO.eprintln s!"module-system: no `.olean` for {m} (did `lake build` run?)"
              bad := bad.push m
  if modules.isEmpty then
    IO.eprintln s!"module-system: found 0 modules under {auditedRoot}: the audit is miswired."
    return 1
  if bad.isEmpty then
    IO.println s!"module-system: all {modules.size} {auditedRoot} module(s) opt into the \
      module system."
    return 0
  else
    IO.eprintln s!"module-system: {bad.size} of {modules.size} {auditedRoot} module(s) do not opt \
      into the module system (their compiled `.olean` has isModule = false):"
    for m in bad do IO.eprintln s!"  {m}"
    IO.eprintln "Add `module` as the first line of each (after the copyright header), and make \
      imports `public import` where the import's contents appear in this file's public API."
    return 1
