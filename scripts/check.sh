#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$project_root"
python3 - <<'PY'
from pathlib import Path
import re
sources=[Path('RandomMatrix.lean'), *Path('RandomMatrix').glob('*.lean')]
for path in sources:
    text=path.read_text()
    # This conservative source scan supplements, rather than replaces, the axiom audit.
    if re.search(r'\b(sorry|admit|axiom|native_decide)\b',text):
        raise SystemExit(f'Forbidden proof dependency token in {path}')
print('Source scan passed')
PY
scripts/lake.sh build
python3 scripts/audit.py
