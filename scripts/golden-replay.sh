#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PM_ROOT="${PM_ROOT:-$ROOT/../port-matroid}"

fixture="${1:-$ROOT/golden/ulp-producer/mini.input.json}"
want_file="${2:-$ROOT/golden/ulp-producer/mini.replay-hash}"
fixture_perm="${3:-$ROOT/golden/ulp-producer/mini.permuted.input.json}"

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

store="$tmpdir/pm-store-mg"
"$ROOT/scripts/append-to-port-matroid.sh" "$fixture" "$store" >/dev/null
(cd "$PM_ROOT" && cabal -v0 run port-matroid-tool -- audit "$store" >/dev/null)
got="$(cd "$PM_ROOT" && cabal -v0 run port-matroid-tool -- replay-hash "$store" | tr -d '\n')"

if [ ! -f "$want_file" ]; then
  echo "missing expected hash file: $want_file" >&2
  exit 2
fi
want="$(tr -d '\n' <"$want_file")"

if [ "$got" != "$want" ]; then
  echo "golden replay hash mismatch: expected $want got $got" >&2
  exit 1
fi

# Ordering invariance: permuted input must yield the same replay hash.
store2="$tmpdir/pm-store-mg-perm"
"$ROOT/scripts/append-to-port-matroid.sh" "$fixture_perm" "$store2" >/dev/null
(cd "$PM_ROOT" && cabal -v0 run port-matroid-tool -- audit "$store2" >/dev/null)
got2="$(cd "$PM_ROOT" && cabal -v0 run port-matroid-tool -- replay-hash "$store2" | tr -d '\n')"
if [ "$got2" != "$want" ]; then
  echo "permuted fixture replay hash mismatch: expected $want got $got2" >&2
  exit 1
fi

echo "ok mind-git golden replay hash"

