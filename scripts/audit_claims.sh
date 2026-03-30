#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

echo "== Building the full project =="
build_log="$(mktemp -t ic-theory-audit-build.XXXXXX.log)"
if lake build >"${build_log}" 2>&1; then
  echo "Build succeeded."
else
  echo "Build failed. Full log: ${build_log}"
  cat "${build_log}"
  exit 1
fi

scan_must_be_empty() {
  local label="$1"
  local pattern="$2"
  echo
  echo "== ${label} =="
  if rg -n "${pattern}" IcTheory; then
    echo
    echo "Audit failed: unexpected matches found in project source."
    exit 1
  else
    echo "No matches found."
  fi
}

scan_must_be_empty "Scanning for proof holes (sorry / admit)" '\bsorry\b|\badmit\b'
scan_must_be_empty "Scanning for project axioms or constants" \
  '^\s*axiom\s+[A-Za-z_]|^\s*constant\s+[A-Za-z_][A-Za-z0-9_]*\s*:'
scan_must_be_empty "Scanning for opaque declarations" '^\s*opaque\s+[A-Za-z_][A-Za-z0-9_]*\s*:'
scan_must_be_empty "Scanning for unsafe declarations" \
  '^\s*unsafe\s+(def|theorem|abbrev|opaque|axiom|inductive|structure|class|instance)\b'

echo
echo "== Theorem statements and kernel-reported axioms =="
echo "Expected axiom report for the main theorems: [propext, Classical.choice, Quot.sound]"
lake env lean IcTheory/Audit.lean
