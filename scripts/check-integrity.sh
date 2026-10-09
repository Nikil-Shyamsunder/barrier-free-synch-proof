#!/usr/bin/env bash
# Verify that the proof artifact contains no proof placeholders and report the
# axioms used by its top-level result.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

lean_files=(SemaAlloc.lean)
while IFS= read -r file; do
  lean_files+=("$file")
done < <(find SemaAlloc -type f -name '*.lean' -print)

if grep -nEH '(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)' "${lean_files[@]}"; then
  echo 'Integrity check failed: found a proof placeholder.' >&2
  exit 1
fi

if grep -nEH '^[[:space:]]*axiom([^[:alnum:]_]|$)' "${lean_files[@]}"; then
  echo 'Integrity check failed: found a local axiom declaration.' >&2
  exit 1
fi

printf '%s\n' \
  'import SemaAlloc' \
  '' \
  '#print axioms perScope_bisimulation' \
  | lake env lean /dev/stdin

echo 'Integrity check passed: no sorry, admit, or local axiom declaration found.'
