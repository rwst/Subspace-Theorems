#!/usr/bin/env bash
# Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: The Tau Ceti contributors
#
# Adapted for this repository from `scripts/source-modules.sh` of the Tau Ceti project
# (<https://github.com/TauCetiProject/TauCeti>) at commit 37ae92f8170796e94b66279ea66f8635d9ca2aa0.
# Changes: the library roots are `ArithmeticHeights` and `DiophantineApproximation` rather than
# `TauCeti`, and the function is named after what it does rather than after the project. The
# pristine original is `~/math/TauCeti/scripts/source-modules.sh`.
#
# Shared, fail-closed discovery of the Lean modules under the library roots.
#
# `LIBRARY_ROOTS` is the single list of them, and every gate reads it from here: adding a roadmap
# to this repository means adding its directory to this array and nothing else.
#
# library_source_modules FILES MODULES writes the validated source paths as a
# NUL-delimited list to FILES and the corresponding Lean module names, one per
# line, to MODULES. Callers choose their own temporary destinations.

LIBRARY_ROOTS=(ArithmeticHeights DiophantineApproximation CorvajaZannier2004)

library_source_modules() {
  local files_out="$1"
  local modules_out="$2"
  local symlinks_out="${files_out}.symlinks"
  local roots_re
  roots_re="$(IFS='|'; printf '%s' "${LIBRARY_ROOTS[*]}")"
  local module_path_re="^($roots_re)(/[A-Za-z_][A-Za-z0-9_']*)+\.lean$"
  local file module
  local -a files=()
  local -a symlinks=()

  find "${LIBRARY_ROOTS[@]}" -type f -name '*.lean' -print0 | LC_ALL=C sort -z > "$files_out"
  find "${LIBRARY_ROOTS[@]}" -type l -print0 | LC_ALL=C sort -z > "$symlinks_out"
  mapfile -d '' files < "$files_out"
  mapfile -d '' symlinks < "$symlinks_out"
  if ((${#symlinks[@]} != 0)); then
    printf 'source-modules: refusing symlinked source path %q\n' "${symlinks[0]}" >&2
    return 1
  fi
  if ((${#files[@]} == 0)); then
    echo 'source-modules: found no library source files; the audit is miswired.' >&2
    return 1
  fi

  : > "$modules_out"
  for file in "${files[@]}"; do
    if [[ ! $file =~ $module_path_re ]]; then
      printf 'source-modules: refusing non-module source path %q\n' "$file" >&2
      return 1
    fi
    module="${file%.lean}"
    printf '%s\n' "${module//\//.}" >> "$modules_out"
  done
}
