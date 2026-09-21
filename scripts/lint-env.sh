#!/usr/bin/env bash
# Copyright (c) 2026 Ralf Stephan. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Ralf Stephan
#
# The environment linters (`#lint`) over the built library: simpNF, checkType, synTaut, docBlame,
# unusedArguments, structureInType, defsWithUnderscore, … — the checks that need a real environment
# and so cannot be done on source text.
#
# This is NOT Tau Ceti's `scripts/lint-env.sh` ported. That script is ~900 lines because it carries
# a grandfathered baseline, a hand-rolled docstring scan replacing `docBlame`, and fail-closed
# sentinels calibrated to a library of several thousand declarations. This library has none of that
# history: the baseline would be empty, and a probe of the full default set (2026-09-15) reported
# `Found 0 errors in 59 declarations (plus 11 automatically generated ones) … with 15 linters`, so
# `docBlame` is included here rather than replaced. The upstream original is
# `~/math/TauCeti/scripts/lint-env.sh`; read it before adding a baseline, and take its reasoning
# about private declarations and module boundaries with it.
#
# The driver is LEGACY (plain `import`, no `module`), which is upstream's choice and matters: from a
# non-module root Lean loads the closure at the `private` olean level, where docstrings are visible
# and a theorem whose proof is not exposed is not mistaken for an axiom. A module-style driver makes
# `docBlame` report every documented declaration as undocumented.
#
# `#lint … in <root>` selects by MODULE prefix, not by namespace (Batteries'
# `getDeclsInPackage`), which is what we need: declarations here live in Mathlib's root namespaces.
# One `#lint` per library root, so the report says which library each violation is in; the roots
# are `LIBRARY_ROOTS` in `scripts/source-modules.sh`.

set -euo pipefail

PROJECT_ROOT="${PROJECT_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
SCRIPTS="$PROJECT_ROOT/scripts"
cd "$PROJECT_ROOT"

lint_src="$(mktemp -d "$PWD/.lake/lint-env-src.XXXXXX")"
trap 'rm -rf "$lint_src"' EXIT
driver="$lint_src/LintEnvDriver.lean"

. "$SCRIPTS/source-modules.sh"
library_source_modules "$lint_src/files" "$lint_src/modules"
mapfile -d '' files < "$lint_src/files"
sed 's/^/import /' "$lint_src/modules" > "$driver"
for root in "${LIBRARY_ROOTS[@]}"; do
  printf '#lint in %s\n' "$root" >> "$driver"
done

expected_imports="${#files[@]}"
emitted_imports="$(grep -c '^import ' "$driver")"
if ((emitted_imports != expected_imports)); then
  echo 'lint-env: generated driver is incomplete; refusing to run.' >&2
  exit 1
fi

set +e
report="$(lake env lean "$driver" 2>&1)"
lean_status=$?
set -e
printf '%s\n' "$report"

# Fail closed on a vacuous pass. `#lint` reports success identically whether it judged every
# declaration or none at all, so a driver that imported nothing, or a `#lint` that stopped
# selecting our modules, would otherwise read as green.
mapfile -t summaries < <(printf '%s\n' "$report" \
  | grep -E 'Found [0-9]+ errors? in [0-9]+ declarations' || true)
if ((${#summaries[@]} != ${#LIBRARY_ROOTS[@]})); then
  echo "lint-env: expected ${#LIBRARY_ROOTS[@]} linter summaries in the report, got \
${#summaries[@]}; the lint is miswired." >&2
  exit 1
fi
declarations=0
linters=0
for summary in "${summaries[@]}"; do
  d="$(printf '%s\n' "$summary" | sed -E 's/.* in ([0-9]+) declarations.*/\1/')"
  l="$(printf '%s\n' "$summary" | sed -E 's/.* with ([0-9]+) linters.*/\1/')"
  if ((d == 0)); then
    echo 'lint-env: one of the linter runs judged 0 declarations; the lint is miswired.' >&2
    exit 1
  fi
  declarations=$((declarations + d))
  linters="$l"
done
if ((declarations == 0)); then
  echo 'lint-env: the linters judged 0 declarations; the lint is miswired.' >&2
  exit 1
fi
if ((linters == 0)); then
  echo 'lint-env: 0 linters ran; the lint is miswired.' >&2
  exit 1
fi

if ((lean_status != 0)); then
  echo "lint-env: the environment linters reported violations." >&2
  exit 1
fi

echo "lint-env: $linters linter(s) judged $declarations declaration(s); no violations."
