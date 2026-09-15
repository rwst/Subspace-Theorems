#!/usr/bin/env bash
# Copyright (c) 2026 Ralf Stephan. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Ralf Stephan
#
# Every gate, in one command — the local stand-in for Tau Ceti's `.github/workflows/ci.yml`, which
# this repository has no CI to run. Order is cheapest-first, and a failure does not stop the run:
# all gates report, so one round shows everything that is wrong.
#
#   scripts/check.sh            run everything
#   scripts/check.sh --quick    skip the build and the two audits that need it
#
# `LEAN_NUM_THREADS` defaults to 3 here: this machine has been taken down by unbounded Lean builds.

set -uo pipefail

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJECT_ROOT"

export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-3}"

quick=0
case "${1:-}" in
  --quick) quick=1 ;;
  "") ;;
  *) echo "usage: scripts/check.sh [--quick]" >&2; exit 2 ;;
esac

status=0
declare -a failed=()

run() {
  local name="$1"; shift
  printf '\n=== %s ===\n' "$name"
  if "$@"; then
    return 0
  fi
  status=1
  failed+=("$name")
  return 0
}

# Textual guards: no elaboration, no build, so they come first and cost nothing.
run "guards (import boundary, set_option, mega-import, namespace)" bash scripts/guards.sh

# Source style: Mathlib's copyright/Authors contract plus its text-based linters. Needs Mathlib
# built (it is, as a dependency) but not this library.
run "lint-style (copyright headers + text linters)" bash scripts/lint-style.sh

if ((quick == 0)); then
  # The build is itself a gate: the library target carries `warningAsError` with Mathlib's standard
  # linter set, so a `sorry`, a 100-column line or a long file fails here.
  run "build (warningAsError + Mathlib standard linter set)" lake build

  # These three read the *built* library, so they are meaningless if the build failed.
  run "axioms (propext / Classical.choice / Quot.sound only)" lake exe axioms
  run "module-system (every file opts into \`module\`)" lake exe module-system
  run "lint-env (#lint: simpNF, docBlame, checkType, …)" bash scripts/lint-env.sh
fi

printf '\n'
if ((status == 0)); then
  if ((quick == 1)); then
    echo "check: all quick gates pass (build, axioms, module-system and lint-env not run)."
  else
    echo "check: all gates pass."
  fi
else
  echo "check: ${#failed[@]} gate(s) failed:" >&2
  for name in "${failed[@]}"; do echo "  - $name" >&2; done
fi
exit "$status"
