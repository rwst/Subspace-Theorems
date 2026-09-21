#!/usr/bin/env bash
# Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: The Tau Ceti contributors
#
# Adapted for this repository from `scripts/lint-style.sh` of the Tau Ceti project
# (<https://github.com/TauCetiProject/TauCeti>) at commit 37ae92f8170796e94b66279ea66f8635d9ca2aa0.
# Changes: the library roots are `ArithmeticHeights` and `DiophantineApproximation`
# (`LIBRARY_ROOTS` in `scripts/source-modules.sh`). Upstream passes its real (empty) library root
# `TauCeti` as a second argument, purely so that `lint-style`'s same-package filter keeps the
# generated module's imports; these libraries have no root module to pass, so their own modules
# are passed instead — they put both roots into that filter, and contribute nothing else
# (their own imports are Mathlib's, which the filter drops). The pristine original is
# `~/math/TauCeti/scripts/lint-style.sh`.
#
# Run the source-based style checks over every library source file: Mathlib's
# copyright/`Authors:` contract (scripts/HeaderStyle.lean) and Mathlib's text-based linters
# (`lake exe lint-style`).
#
# `lint-style` treats its module arguments as import roots and lints their imports — not the roots
# themselves — keeping only imports inside the same package. There is no module that imports the
# whole library (nothing re-exports it), so one is generated. It lives under `.lake` because that
# is the writable, ignored area, and `LEAN_SRC_PATH` points there so the name resolves.

set -euo pipefail

PROJECT_ROOT="${PROJECT_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
SCRIPTS="$PROJECT_ROOT/scripts"
cd "$PROJECT_ROOT"

lint_src="$(mktemp -d "$PWD/.lake/lint-style-src.XXXXXX")"
trap 'rm -rf "$lint_src"' EXIT
lint_module="$lint_src/SubspaceTheoremsLint/All.lean"
mkdir -p "$(dirname "$lint_module")"

. "$SCRIPTS/source-modules.sh"
library_source_modules "$lint_src/files" "$lint_src/modules"
mapfile -d '' files < "$lint_src/files"
sed 's/^/import /' "$lint_src/modules" > "$lint_module"
expected_imports="${#files[@]}"
emitted_imports="$(grep -c '^import ' "$lint_module")"
if ((emitted_imports != expected_imports)); then
  echo 'lint-style: generated import root is incomplete; refusing to run.' >&2
  exit 1
fi

# Use the validated discovery list for the copyright/Authors audit. Keep going after a header
# failure so the text-based diagnostics are visible in the same round.
status=0
if ! lake env lean --run "$SCRIPTS/HeaderStyle.lean" "${files[@]}"; then
  status=1
fi

mapfile -t modules < "$lint_src/modules"
if ! LEAN_SRC_PATH="$lint_src${LEAN_SRC_PATH:+:$LEAN_SRC_PATH}" \
    lake exe lint-style "$@" SubspaceTheoremsLint.All "${modules[@]}"; then
  status=1
fi

exit "$status"
