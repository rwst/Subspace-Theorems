#!/usr/bin/env bash
# Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: The Tau Ceti contributors
#
# Adapted for this repository from the "Import-boundary guard" and "No-set_option guard" steps of
# `.github/workflows/ci.yml` of the Tau Ceti project (<https://github.com/TauCetiProject/TauCeti>)
# at commit 37ae92f8170796e94b66279ea66f8635d9ca2aa0, which runs them inline in CI. This repository
# has no CI, so they live in a script that `scripts/check.sh` runs. The forbidden import is
# `Roadmap` rather than `TauCetiRoadmap`/`TauCetiReview`, and the mega-import guard is ours.
#
# These are textual scans: they need no elaboration and no build, so they run first and cost
# nothing. Each is deliberately a `grep`, not a linter — a linter can be silenced from inside the
# file it is judging.
#
# Both library roots are scanned, `ArithmeticHeights` and `DiophantineApproximation`; the list is
# `LIBRARY_ROOTS` in `scripts/source-modules.sh`.

set -euo pipefail

cd "$(dirname "$0")/.."

. "$(dirname "$0")/source-modules.sh"

status=0

for LIB in "${LIBRARY_ROOTS[@]}"; do
  mapfile -t files < <(find "$LIB" -type f -name '*.lean' | LC_ALL=C sort)
  if ((${#files[@]} == 0)); then
    echo "guards: found no $LIB source files; the guard is miswired." >&2
    exit 1
  fi

  # 1. Import boundary. A library may not depend on the roadmap: `Roadmap/Suggested.lean` is
  # `sorry`-allowed and is not a default build target, so an import of it would smuggle those
  # `sorry`s into the library through the back door, where the axiom audit would find them only
  # after the fact. The roadmap states the targets; the libraries prove them.
  if grep -nE '^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+Roadmap\b' "${files[@]}"; then
    echo "guards: $LIB/ must not import Roadmap (the sorry-allowed target signatures)." >&2
    status=1
  fi
  # The same boundary for the comparator statements of record (`Challenge`, `ChallengeFlat`), which
  # are `sorry`-proved by design, and for `Solution`, which exists to import the libraries.
  record_re='^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+'
  record_re+='(Challenge|ChallengeFlat|Solution)\b'
  if grep -nE "$record_re" "${files[@]}"; then
    echo "guards: $LIB/ must not import Challenge, ChallengeFlat or Solution" \
      "(see COMPARATOR.md)." >&2
    status=1
  fi

  # 2. No `set_option` in library source. It is an escape hatch: it can raise `maxHeartbeats`,
  # silence a linter, bump `maxRecDepth`. Upstream's wording, upstream's rule.
  if grep -n '^set_option ' "${files[@]}"; then
    echo "guards: $LIB/ may not use set_option (it can weaken maxHeartbeats, linters, \
maxRecDepth, ...); remove it." >&2
    status=1
  fi

  # 3. No mega Mathlib import. Ours, not upstream's: `import Mathlib` pulls the whole library, makes
  # the build unrepresentative of what the file needs, and hides the dependency the module doc
  # should be stating. Fine-grained imports only. (`Roadmap/Suggested.lean` does use it, and is not
  # scanned.)
  if grep -nE '^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+Mathlib[[:space:]]*$' \
      "${files[@]}"; then
    echo "guards: $LIB/ may not \`import Mathlib\`; import the modules the file actually uses." >&2
    status=1
  fi

  # 4. No wrapper namespace. Declarations go into Mathlib's root namespaces —
  # `Polynomial.mulHeight`, `Submodule.mulHeight`, `NumberField.absMulHeight`, as the roadmaps pin
  # them — never inside a `namespace ArithmeticHeights` or a `namespace DiophantineApproximation`.
  # This is also the local form of Tau Ceti's `lint-dot-notation`, which is NOT ported: that lint
  # finds a Mathlib type's namespace nested inside the *project* namespace, where dot notation
  # silently stops elaborating. Tau Ceti wraps its library in `namespace TauCeti` and therefore
  # needs the full search; here the wrapper itself is the thing forbidden, and one `grep` settles
  # it.
  if grep -nE "^namespace $LIB\b" "${files[@]}"; then
    echo "guards: declarations belong in Mathlib's root namespaces; do not open a \
\`namespace $LIB\`." >&2
    status=1
  fi

  if ((status == 0)); then
    echo "guards: ${#files[@]} $LIB source file(s) pass the import-boundary, set_option, \
mega-import and namespace guards."
  fi
done

exit "$status"
