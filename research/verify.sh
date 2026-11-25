#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "$0")" && pwd)"
cd "${1:?Pass the path to the pinned mathlib checkout}"
pin=b5eba595428809e96f3ed113bc7ba776c5f801ac
if [[ "$(git rev-parse HEAD)" != "$pin" ]]; then
  echo "Expected mathlib commit $pin" >&2
  exit 1
fi
build="$(mktemp -d)"
trap 'rm -rf -- "$build"' EXIT
export LEAN_PATH="$build"
version="$(lake env lean --version)"
printf '%s\n' "$version"
[[ "$version" == *"version 4.8.0,"* && "$version" == *"df668f00e6c0"* ]]
while IFS= read -r module; do
  printf 'Checking %s\n' "$module"
  lake env lean --root="$root/lean" -o "$build/$module.olean" "$root/lean/$module.lean" | tee -a "$build/audits.txt"
done < "$root/lean/modules.txt"
python3 "$root/check_audits.py" "$build/audits.txt"
