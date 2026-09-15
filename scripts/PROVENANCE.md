# The gates, and where they came from

`scripts/` holds this repository's quality gates. Most of them are Tau Ceti's, adapted: taken on
**2026-09-15** from `~/math/TauCeti/scripts/` at commit
`37ae92f8170796e94b66279ea66f8635d9ca2aa0` (branch `main`), Apache-2.0, © the Tau Ceti
contributors. Each adapted file carries a header naming its upstream original and listing what was
changed; the pristine originals stay in that clone and are not vendored here.

`scripts/check.sh` runs everything. `scripts/check.sh --quick` runs only the gates that need no
build.

## Tracked: the gates themselves

| File | Gate | Origin |
| --- | --- | --- |
| `check.sh` | runs every gate below, cheapest first, and reports all failures in one round | ours; stands in for upstream's `.github/workflows/ci.yml`, which needs a CI to run |
| `guards.sh` | four textual scans: the library may not import `Roadmap` (the `sorry`-allowed target signatures), may not use `set_option`, may not `import Mathlib`, and may not open a `namespace ArithmeticHeights` | the first two are upstream's CI steps; the last two are ours |
| `Axioms.lean` | `lake exe axioms` — every declaration reaches only `propext`, `Classical.choice`, `Quot.sound`; catches `sorry`/`sorryAx`, `native_decide`'s `Lean.ofReduceBool`, and home-rolled axioms, including ones reaching in through imports | adapted from upstream |
| `ModuleSystem.lean` | `lake exe module-system` — reads `ModuleData.isModule` back out of each built `.olean`, certifying the compilation rather than the source text | adapted from upstream |
| `HeaderStyle.lean` | the copyright/`Authors:` contract, through Mathlib's `copyrightHeaderChecks`; Mathlib's own command linter skips files absent from a library root, and this library has no root | adapted from upstream |
| `source-modules.sh` | fail-closed source discovery shared by the two lint entry points: refuses symlinks and non-module paths, and fails when it finds nothing, so a miswired gate cannot pass vacuously | adapted from upstream |
| `lint-style.sh` | the header audit plus Mathlib's text-based linters (`lake exe lint-style`) over the whole library | adapted from upstream |
| `lint-env.sh` | the environment linters: `#lint` over the built library — simpNF, docBlame, checkType, synTaut, unusedArguments, … | ours; upstream's is a different thing (see below) |
| `nolints-style.txt` | exceptions for `lake exe lint-style`, deliberately empty | the file `lint-style` reads by convention |

## What each gate catches, and where

The three linting stages are not interchangeable; a given violation surfaces in exactly one:

- **`lake build`** — `sorry`, lines over 100 columns, files over 1500 lines, and the rest of
  Mathlib's *syntax* linter set, because the library target sets `warningAsError`.
- **`lint-style.sh`** — trailing whitespace, adaptation notes, unicode, module naming, and the
  copyright header: the *text-based* linters, which read source rather than syntax trees.
- **`lint-env.sh`** — what needs a real environment: a bad `@[simp]` normal form, a statement that
  does not type-check, an undocumented definition.

Each gate was tested against a violation, not only against a clean tree: a `sorry` fails the build;
a 101-column line fails the build (`linter.style.longLine`); trailing whitespace fails
`lint-style`; a wrong licence line fails the header audit; an undocumented `def` fails `lint-env`
(`docBlame`); a home-rolled `axiom` fails `lake exe axioms`; a file without `module` fails
`lake exe module-system`.

## Not ported, and why

- **Upstream's `lint-env.sh`** (~900 lines) carries a grandfathered baseline, a hand-rolled
  docstring scan replacing `docBlame`, and fail-closed sentinels calibrated to a library of
  thousands of declarations. This library has no such history — the baseline would be empty — and a
  probe of the full default set found `docBlame` working correctly from a legacy driver, so it is
  included rather than replaced. Read the upstream file before adding a baseline; its reasoning
  about private declarations and module boundaries is the part worth keeping.
- **`lint-dot-notation.py`** + `lean_source.py` find a Mathlib type's namespace nested inside the
  *project* namespace, where dot notation silently stops elaborating. Tau Ceti wraps its library in
  `namespace TauCeti`, so it needs the full search. Here that wrapper is itself forbidden —
  declarations go into Mathlib's root namespaces, as the roadmap pins them — so guard 4 of
  `guards.sh` settles the same question with one `grep`. Ported as-is the lint would be vacuous: it
  hard-codes `TauCeti` as the wrapper namespace in two places, and nothing here is ever declared
  inside one.
- **`check-expired-mathlib-shims.py`** wants a `mathlib-shims.json` this repository does not keep
  yet. It becomes relevant the moment Layer 0.3 or 6.5 lands, since both deliberately shadow an
  open Mathlib PR (mathlib4#41606, mathlib4#40791).
- **`sandbox-build.sh`**, `lake-cache-get.sh`, the cache/toolchain/PR-statistics tooling and the
  infrastructure unit tests are all tied to Tau Ceti's CI, which this repository does not run.

The still-unadapted upstream copies of the first three are present locally and **gitignored**
(`.gitignore` names them), so they can be read and adapted without a second clone. A fresh clone
will not have them, and nothing tracked may point at them.
