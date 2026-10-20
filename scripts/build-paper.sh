#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "$0")/.." && pwd)"
if ! command -v tectonic >/dev/null 2>&1; then
  echo 'Install Tectonic to build the paper: https://tectonic-typesetting.github.io/' >&2
  exit 1
fi

build_dir="$(mktemp -d "${TMPDIR:-/tmp}/matrices-paper.XXXXXX")"
trap 'rm -rf "$build_dir"' EXIT
tectonic --keep-logs --outdir "$build_dir" "$project_root/paper/marchenko-pastur.tex"
if grep -Eq 'Overfull|undefined references|Citation .* undefined' "$build_dir/marchenko-pastur.log"; then
  echo 'Paper build has layout or reference warnings; inspect the TeX output.' >&2
  grep -A 4 -E 'Overfull|undefined references|Citation .* undefined' "$build_dir/marchenko-pastur.log" >&2
  exit 1
fi
cp "$build_dir/marchenko-pastur.pdf" "$project_root/paper/marchenko-pastur.pdf"
echo 'Built paper/marchenko-pastur.pdf'
