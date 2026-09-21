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
