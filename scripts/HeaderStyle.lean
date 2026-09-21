/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Adapted for this repository from `scripts/HeaderStyle.lean` of the Tau Ceti project
(<https://github.com/TauCetiProject/TauCeti>) at commit `37ae92f8170796e94b66279ea66f8635d9ca2aa0`.
Changes: the audited libraries are `ArithmeticHeights` and `DiophantineApproximation`, neither
of which has a library root at all, so the root exemption upstream needs does not arise. The pristine original is
`~/math/TauCeti/scripts/HeaderStyle.lean`; the code below is upstream's.
-/
import Mathlib.Tactic.Linter.Header

/-!
# Copyright-header audit

Mathlib's `linter.style.header` deliberately skips a module unless the library root imports it.
These libraries have no root module at all, so the ordinary command linter never reaches their
files.
This audit calls the linter's public `copyrightHeaderChecks` function on the validated
source list supplied by `scripts/lint-style.sh`.

This intentionally enforces the copyright block and `Authors:` contract, not the same command
linter's separate broad-import, duplicate-import, directory-dependency, or module-doc checks. The
latter require elaborator state and are outside this text-based check.

Run via `lake env lean --run scripts/HeaderStyle.lean ...`, as part of `scripts/lint-style.sh`.
-/

open Mathlib.Linter

/-- Mathlib's default required license line, also used here. -/
def expectedLicense := Mathlib.Linter.linter.style.header.license.defValue

/-- Audit every supplied source with Mathlib's copyright-header checker. Returns a nonzero exit
code when the source list is empty or at least one file has a malformed header. -/
unsafe def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "header-style: received no validated library source files; \
      the audit is miswired."
    return 1
  let mut failures : UInt32 := 0
  for path in args do
    -- `copyrightHeaderChecks` stops at the end of the first copyright block, so passing the whole
    -- source is equivalent to Mathlib's leading-trivia call while avoiding elaborator state.
    let errors := copyrightHeaderChecks (← IO.FS.readFile path) expectedLicense
    unless errors.isEmpty do
      failures := failures + 1
      for (_, message) in errors do
        IO.eprintln s!"{path}: {message}"
  if failures != 0 then
    IO.eprintln s!"header-style: {failures} source file(s) have malformed copyright headers."
  else
    IO.eprintln s!"header-style: all {args.length} library source file(s) \
      have conforming headers."
  return min failures 125
