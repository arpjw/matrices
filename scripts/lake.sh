#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd "$(dirname "$0")/.." && pwd)"
local_bin="$project_root/../../work/toolchains/lean-4.28.0-darwin_aarch64/bin"
if [[ -d "$local_bin" ]]; then
  export PATH="$local_bin:$PATH"
fi
if ! command -v lake >/dev/null; then
  echo 'Install Lean using elan; lean-toolchain pins the required version.' >&2
  exit 1
fi
cd "$project_root"
exec lake "$@"
