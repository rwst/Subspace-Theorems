# Subspace-Theorems

A working repository for the **`ArithmeticHeights` roadmap** — arithmetic heights of polynomials,
matrices and linear subspaces, Northcott and Kronecker, successive minima, Siegel's lemma and
Bombieri–Vaaler. The roadmap itself is [`ArithmeticHeights/README.md`](ArithmeticHeights/README.md);
the suggested Lean signatures for the milestones most likely to drift are
[`Roadmap/Suggested.lean`](Roadmap/Suggested.lean).

The work is being done **here rather than in [Tau Ceti](https://github.com/TauCetiProject/TauCeti),
ahead of it, because nothing proceeds there.** The intent is nevertheless that what lands here is
Tau Ceti material: the implementation adheres to Tau Ceti's principles (see below), so that moving a
finished file into `TauCeti/NumberTheory/Height/` is a path change and an import fix, not a rewrite.
`ArithmeticHeights/Arakelov.lean` is written that way already — Apache header, `module`,
`public import`, module docstring with `## Main definitions` / `## Main results` /
`## Implementation notes` / `## References`, closing with its roadmap layer ("This is Layer 0.1 of
the `ArithmeticHeights` roadmap"), sorry-free.

## ⚠ The roadmap is preliminary

**`ArithmeticHeights/README.md` has not finished review.** Treat it as a draft specification:

- Milestone **names and shapes may still change**, including ones already implemented here.
  `Suggested.lean` says so itself: it "is not the roadmap and is not exhaustive", and exists
  precisely for the statements whose shapes are most likely to drift.
- Do not treat a signature in `Suggested.lean` as settled API. It elaborates against the pinned
  Mathlib and is stated with `sorry`; the sorry-free version is what has to be right.
- Expect re-shaping when review lands — especially in the layers that depend on choices review is
  most likely to touch: the Arakelov vs. sup-norm normalisation and the relative/absolute split
  (Layer 0), the Plücker indexing and the `Module.Grassmannian` question (Layer 3), and the
  constants in Layers 5.3–5.4.
- Anything built here should therefore keep the *mathematics* separable from the *naming*: prove
  the statement, keep the docstring citing the book (Bombieri–Gubler, Bombieri–Vaaler), and accept
  that the identifier may be renamed on the way into Tau Ceti.

## Tau Ceti principles this repo follows

From `~/math/TauCeti/AGENTS.md`, its `lakefile.toml`, and its CI. The first three are enforced
mechanically here — by `warningAsError`, `lake exe axioms` and `lake exe module-system`; the rest
are honoured by hand until the corresponding machinery is adapted (see *Still to settle*).

- **No `sorry`, and no axioms beyond `propext`, `Classical.choice`, `Quot.sound`** — hence no
  `native_decide` — in any file that is meant to become Tau Ceti code. `Roadmap/Suggested.lean`
  is exempt: it is a human-owned target file, not library code, and not a default build target.
- **No `set_option`** in library source: it is an escape hatch for `maxHeartbeats`, linters and
  `maxRecDepth`.
- **Mathlib's standard linter set with `warningAsError`**, file length ≤ 1500 lines (≤ 1000 for a
  newly added file).
- **Every file opts into the Lean module system**: a leading `module`, `public import` for imports
  whose contents appear in the file's public API, plain `import` otherwise, and a `public section`.
- **Copyright header** in Mathlib's format (`Copyright (c) 2026 … Released under Apache 2.0 license
  as described in the file LICENSE. / Authors: …`).
- **Fine-grained Mathlib imports, never `import Mathlib`.**
- **Defer to Mathlib's design decisions**; consume Mathlib by name and rebuild nothing it already
  has. Track Mathlib `master`; bumps are forward-only.
- **No backwards-compatibility surface**: no aliases, forwarding modules, or deprecated shims. When
  something is renamed or superseded, update every use and delete the old name in the same change.
- **Improving existing code is always in scope**; adding *new* mathematics is gated by the roadmap.

## Tau Ceti files copied to this repo root

Verbatim copies now sit in two **gitignored** directories, taken from `~/math/TauCeti` at commit
`37ae92f8170796e94b66279ea66f8635d9ca2aa0` on 2026-09-15:

- **`scripts/`** — the governance machinery: the header audit, the source-discovery and lint
  entry points with their baselines, and the mathlib-shim expiry check. Ignored, **except**
  `Axioms.lean` and `ModuleSystem.lean`, which are adapted, tracked and wired (below). See
  `scripts/PROVENANCE.md`.
- **`TauCeti/`** — the contract and configuration, for reading only: `AGENTS.md`, `lakefile.toml`,
  `formalization.yaml`, `mathlib-shims.json`, `.github/workflows/ci.yml`, `docbuild/`, at their
  upstream paths. See `TauCeti/PROVENANCE.md`.

Apart from those two audits, both directories are local references, so **nothing tracked may point
into them** — a fresh clone does not have them. Adopting a file means adapting it, un-ignoring it,
and committing the result. Every one of them hard-codes the library root `TauCeti`, which is
`ArithmeticHeights` here. The table records what each buys and what adoption costs.

| Source (in `~/math/TauCeti/`) | What it gives us | Adaptation |
| --- | --- | --- |
| `scripts/Axioms.lean` | `lake exe axioms`: kernel-level audit that every declaration uses only the three allowlisted axioms — catches `sorry`/`sorryAx`, `native_decide`, home-rolled axioms | point `auditedRoot` at `ArithmeticHeights` |
| `scripts/ModuleSystem.lean` | `lake exe module-system`: reads `ModuleData.isModule` out of each built `.olean`, so every file really opted into `module` | same root change |
| `scripts/HeaderStyle.lean` | copyright/`Authors:` audit via Mathlib's `copyrightHeaderChecks`, which the command linter skips for files absent from the library root | none beyond the file list it is handed |
| `scripts/source-modules.sh` | fail-closed discovery of library sources (rejects symlinks and non-module paths); shared by the two lint entry points so they cannot drift | rename the `TauCeti` path regex and the function name |
| `scripts/lint-style.sh` | runs the header audit plus Mathlib's `lint-style` text linters over the whole library by generating a temporary import-all root | root name; we *have* a real root, so the empty-root workaround can be simplified |
| `scripts/lint-env.sh`, `scripts/lint-baseline.txt` | environment lint: default linters plus a docstring scan against a grandfathered baseline | baseline starts empty here |
| `scripts/lint-dot-notation.py` + `scripts/lean_source.py`, `scripts/lint-dot-notation-baseline.txt` | keeps Mathlib type namespaces at the root (relevant: `Polynomial.mulHeight`, `Matrix.mulHeight`, `Submodule.mulHeight` are exactly such names) | baseline starts empty here |
| `lakefile.toml` (the two `lean_exe` blocks) | wiring for `lake exe axioms` and `lake exe module-system` | the `leanOptions` are **already ported** into our `lakefile.lean`; only the executables are left, and they need the two scripts above |
| `AGENTS.md` (+ `.claude/CLAUDE.md` symlink to it) | the contributor contract itself — the rules above in their authoritative wording | drop the PR/review/roadmap-repo sections; there is no PR pipeline here |
| `formalization.yaml` | repo-root metadata (v0.2) for formalization projects: sources, automation, sorry/axiom status | rewrite for this repo: source = Bombieri–Gubler + the roadmap, single human author |
| `docbuild/` | `doc-gen4` setup for generated API documentation | optional; only if we want docs |
| `.github/workflows/ci.yml` | the gates in one place: import-boundary and no-`set_option` textual guards, build, axiom audit, module-system audit, env lint, dot-notation lint, style lint | heavy; the two textual guards are three lines each and worth lifting even without the workflow |
| `TauCeti/mathlib-shims.json` + `scripts/check-expired-mathlib-shims.py` | tracks declarations vendored from open Mathlib PRs so they are removed once upstream lands | directly relevant: Layer 0.3 shadows [mathlib4#41606](https://github.com/leanprover-community/mathlib4/pull/41606) and Layer 6.5 [mathlib4#40791](https://github.com/leanprover-community/mathlib4/pull/40791) |

Not relevant here: `COORDINATION.md` (the multi-agent claim/lease contract — one repo, one author),
`.github/CODEOWNERS` and everything under `.github/workflows/` to do with review, auto-merge, Zulip
and the Lake cache, and `scripts/` tooling for PR statistics and toolchain tags.

## Layout and building

```
ArithmeticHeights/   the library: sorry-free Lean, Tau Ceti rules, the default build target
  Arakelov.lean      Layer 0.1
  README.md          the roadmap (prose)
Roadmap/
  Suggested.lean     the roadmap's target signatures: sorry-allowed, NOT a default target
scripts/             [gitignored, except:] Tau Ceti's lints, verbatim, to be adapted
  Axioms.lean        tracked: `lake exe axioms`, the axiom allowlist gate
  ModuleSystem.lean  tracked: `lake exe module-system`, the `module` opt-in gate
TauCeti/             [gitignored] Tau Ceti's contract and configuration, verbatim, to read
*.pdf                [gitignored] literature (Bombieri–Gubler)
```

```bash
lake exe cache get        # Mathlib oleans
lake build                # the library only
lake exe axioms           # audit: only propext / Classical.choice / Quot.sound
lake exe module-system    # audit: every library file opted into `module`
lake build Roadmap        # optional: check the target signatures still elaborate
```

`lake build` never touches `Roadmap/`: that library is declared without `@[default_target]`
precisely so its 69 `sorry`s stay out of the library's build and out of any audit. The library
target carries Tau Ceti's lean options, so `warningAsError` turns "declaration uses `sorry`" into
a build error there.

All three gates are live, and each was tested against a violation and not only against a clean
tree: a `sorry` fails the build; a home-rolled `axiom` builds but makes `lake exe axioms` exit `1`
naming the declaration; a file without `module` builds but makes `lake exe module-system` exit `1`
naming the module. On the tree as it stands: 70 declarations audited, all within the allowlist, and
every module opted in. Both audits read the *built* library, so `lake build` comes first.

## Still to settle

1. **Copyright attribution in the Lean files.** `ArithmeticHeights/Arakelov.lean` is authored as
   "The Tau Ceti contributors"; the lakefile now says "Ralf Stephan". Pick one and make the
   headers agree. (The Apache-2.0 header format is Tau Ceti's and stays either way.)
2. **The lints are not wired.** The two audits are done; the copyright-header audit
   (`HeaderStyle.lean` + `lint-style.sh` + `source-modules.sh`), the environment lint
   (`lint-env.sh`) and the dot-notation lint (`lint-dot-notation.py` + `lean_source.py`) are still
   ignored reference copies, so Mathlib's text linters and the `Authors:` contract are honoured by
   hand. They need the `TauCeti` root repointed and empty baselines. Neither guard from
   `ci.yml` — no `set_option`, no import across a boundary — is wired either; each is three lines
   of `grep`.
3. **Pins.** Toolchain `v4.34.0`, Mathlib `1e043bcd5646` on `master` — ahead of Tau Ceti's
   `v4.34.0-rc1` / `653c36f019ec`, which is the allowed direction. Bumps stay forward-only.

Settled on 2026-09-15: the Tau Ceti reference copies are in place (gitignored `scripts/` and
`TauCeti/`, alongside the gitignored Bombieri–Gubler PDF); the axiom and module-system audits are
adapted, tracked and wired into the lakefile; the repo `LICENSE` is Apache-2.0, matching the Lean
file headers and the destination library; `Suggested.lean` moved out of the library glob into
`Roadmap/`; the lakefile carries Tau Ceti's lean options and the package is named
`SubspaceTheorems`; the Mathlib require pins `inputRev` to `master`.
