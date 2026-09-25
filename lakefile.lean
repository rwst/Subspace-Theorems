/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
import Lake
open Lake DSL

package "SubspaceTheorems" where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

-- Mathlib's `rev` always stays on "master", as in Tau Ceti; `lake-manifest.json` alone carries the
-- exact commit builds use, and pin bumps are forward-only.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

-- `leanprover/comparator`, pinned to the tag of this project's toolchain. It provides the
-- `comparator` executable and, transitively, `lean4export`; `lake build comparator lean4export`
-- builds both, and the `test` driver below runs them. See `COMPARATOR.md`.
require comparator from git
  "https://github.com/leanprover/comparator" @ "v4.35.0-rc3"

-- The libraries: the sorry-free mathematics, held to Tau Ceti's rules so that a finished file
-- moves into `TauCeti/NumberTheory/` unchanged. `globs` is authoritative for what gets built;
-- neither library has a root module and nothing re-exports them.
--
-- There are two, one per roadmap: `ArithmeticHeights/` (heights of polynomials, subspaces and
-- lattices — `ArithmeticHeights/README.md`) and `DiophantineApproximation/` (approximation
-- exponents, the Roth machinery and the Subspace Theorem — `DiophantineApproximation/README.md`),
-- the second standing on the first. They are separate `lean_lib`s rather than one glob because the
-- roadmaps, and so the milestone numbering every docstring cites, are separate documents; every
-- gate in `scripts/` audits both, and `scripts/source-modules.sh` is the single list of roots.
--
-- The lean options are Tau Ceti's: Mathlib's standard linter set, its 1500-line file ceiling
-- (`longFile` and `longFileDefValue` must agree, or the linter nags to remove a `set_option` on
-- every short file), the copyright-header linter, and `warningAsError`, which is what makes a
-- `sorry` — reported as a warning — fail the build here.
@[default_target]
lean_lib ArithmeticHeights where
  globs := #[.submodules `ArithmeticHeights]
  leanOptions := #[
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.longFile, .ofNat 1500⟩,
    ⟨`weak.linter.style.longFileDefValue, .ofNat 1500⟩,
    ⟨`weak.linter.style.header, true⟩,
    ⟨`warningAsError, true⟩
  ]

@[default_target]
lean_lib DiophantineApproximation where
  globs := #[.submodules `DiophantineApproximation]
  leanOptions := #[
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.longFile, .ofNat 1500⟩,
    ⟨`weak.linter.style.longFileDefValue, .ofNat 1500⟩,
    ⟨`weak.linter.style.header, true⟩,
    ⟨`warningAsError, true⟩
  ]

-- The roadmap's target signatures (`Roadmap/Suggested.lean`): human-owned, `sorry`-allowed, and
-- deliberately **not** a default target, so `lake build` never builds it and no audit ever sees
-- it. In Tau Ceti this material lives in a separate repository. Build it on purpose with
-- `lake build Roadmap` to check that the signatures still elaborate against the pinned Mathlib.
lean_lib Roadmap where
  globs := #[.submodules `Roadmap]

-- The two audits, adapted from Tau Ceti (see each file's header). They read the *built* library —
-- `lake build` first — and are the mechanical form of two house rules the source text cannot
-- certify on its own.
--
-- `lake exe axioms` rebuilds both library environments from their `.olean`s and rejects any
-- declaration reaching an axiom outside `propext`, `Classical.choice`, `Quot.sound`; that is what
-- catches `sorry`/`sorryAx`, `native_decide`'s `Lean.ofReduceBool`, and any home-rolled axiom,
-- including one reaching in through an import.
lean_exe axioms where
  root := `scripts.Axioms

-- `lake exe «module-system»` reads `ModuleData.isModule` back out of each built `.olean`, so it
-- certifies that the file really began with `module` — a `grep` would be fooled by the word in a
-- comment or a string.
lean_exe «module-system» where
  root := `scripts.ModuleSystem

/-! ## `lake test`: certify the challenge/solution pair with `leanprover/comparator`

`lake test` runs comparator on the configs in `comparator/`. Each one checks that `Solution`
proves the exact statements of its challenge module, compared constant by constant over the whole
definitional closure (definitions by value), within the axioms the config permits, and that the
resulting environment is re-accepted by the Lean kernel. See `COMPARATOR.md`.

None of the three libraries below is a default target, and neither mathematical library imports
any of them, so plain `lake build` and every gate in `scripts/` are unaffected. -/

/-- The trusted statement of record, one module per module of the development that owns a
compared declaration: each repeats that module's compared definitions verbatim, under that
module's own imports, and states its certified theorems with `sorry`. Generated by
`scripts/make-challenge.py`; do not edit by hand. -/
lean_lib Challenge where
  globs := #[.andSubmodules `Challenge]

/-- The same statements in one module whose transitive imports are Mathlib and Lean core only —
the shape the Palomar registry requires of a Challenge. Generated by `scripts/make-challenge.py`
from the same data as `Challenge/`; do not edit by hand. -/
lean_lib ChallengeFlat where

/-- The development, re-exported for comparator: the modules that own the certified statements. -/
lean_lib Solution where

/-- The comparator configs run by `lake test`, unless overridden by `lake test -- <cfg>…`: the
same theorems against the two challenge shapes. Both lanes permit only Lean's three standard
axioms, which is all the development uses. -/
def comparatorConfigs : Array String :=
  #["comparator/std3.json", "comparator/std3-flat.json"]

/-- Resolve a binary: `$envVar` if set, else the first candidate path that exists, else
whatever `PATH` yields. `none` if it cannot be found at all. -/
def findBinary (envVar name : String) (candidates : Array System.FilePath) :
    IO (Option String) := do
  if let some path ← IO.getEnv envVar then
    return some path
  for candidate in candidates do
    if ← candidate.pathExists then
      return some (← IO.FS.realPath candidate).toString
  let out ← IO.Process.output { cmd := "sh", args := #["-c", s!"command -v {name}"] }
  let path := out.stdout.trimAscii.toString
  return if out.exitCode == 0 && !path.isEmpty then some path else none

@[test_driver]
script test (args) do
  let ws ← getWorkspace
  let root := ws.dir
  let packages := root / ".lake" / "packages"

  let comparator? ← findBinary "COMPARATOR_BIN" "comparator"
    #[packages / "comparator" / ".lake" / "build" / "bin" / "comparator"]
  let lean4export? ← findBinary "COMPARATOR_LEAN4EXPORT" "lean4export"
    #[packages / "lean4export" / ".lake" / "build" / "bin" / "lean4export"]
  let landrun? ← findBinary "COMPARATOR_LANDRUN" "landrun" #[]

  let some comparator := comparator?
    | IO.eprintln "lake test: `comparator` not found. Run `lake build comparator lean4export`."
      return 1
  let some lean4export := lean4export?
    | IO.eprintln "lake test: `lean4export` not found. Run `lake build comparator lean4export`."
      return 1
  let some landrun := landrun?
    | IO.eprintln "lake test: `landrun` not found; comparator sandboxes every build with it."
      IO.eprintln "Install it once (Linux only — it uses Landlock):"
      IO.eprintln "  git clone https://github.com/Zouuup/landrun && cd landrun"
      IO.eprintln "  go build -o ~/.local/bin/landrun cmd/landrun/main.go"
      IO.eprintln "Then re-run, or point COMPARATOR_LANDRUN at the binary."
      return 1

  -- Reproduce `lake env` for the child: comparator shells out to `lake`, `lean` and
  -- `lean4export`, all of which need LEAN_PATH and the toolchain on PATH.
  let env := ws.augmentedEnvVars ++ #[
    ("COMPARATOR_LEAN4EXPORT", some lean4export),
    ("COMPARATOR_LANDRUN", some landrun)]

  let configs := if args.isEmpty then comparatorConfigs else args.toArray
  for config in configs do
    IO.println s!"\n=== comparator {config} ==="
    let child ← IO.Process.spawn { cmd := comparator, args := #[config], env, cwd := root }
    let rc ← child.wait
    if rc != 0 then
      IO.eprintln s!"lake test: comparator rejected {config}"
      return rc
  return 0
