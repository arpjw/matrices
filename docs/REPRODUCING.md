# Reproducing the artifact

Run commands from the repository root. The proof requires no paid services or
accelerator hardware. A first build needs network access to fetch the pinned
dependencies and their precompiled cache.

## Lean proof and audit

Prerequisites: Git, Python 3, and [elan](https://github.com/leanprover/elan).
The `lean-toolchain` file selects Lean 4.28.0. The mathlib revision is
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`, with transitive dependencies pinned
by `lake-manifest.json`. Keep these pins when reproducing the recorded results.

```sh
lake exe cache get
bash scripts/check.sh
```

`check.sh` runs the source scan, `lake build`, and `scripts/audit.py`.
The audit checks coverage of exported named theorems, restricts reported axioms
to `propext`, `Classical.choice`, and `Quot.sound`, and verifies eleven negative
controls. Each control must fail with exactly its intended unsolved goal,
not an import or infrastructure error. Logs are written under `docs/validation/`.
Running the checks may update tracked logs; this is expected.

To build without the audit, run `lake build`. The wrapper `scripts/lake.sh`
also works with an installed `lake` on PATH. Generated dependencies and Lean
build artifacts live under `.lake/` and are not tracked.

The [verification record](VALIDATION.md) describes the successful build and its
trust boundary. Lean's kernel and the pinned imported mathematics remain
trusted; no independently implemented second kernel was run.

## Mathematical paper

The editable source is [`paper/marchenko-pastur.tex`](../paper/marchenko-pastur.tex).
Install [Tectonic](https://tectonic-typesetting.github.io/), then run:

```sh
bash scripts/build-paper.sh
```

The script compiles in a temporary directory, rejects overfull boxes and
unresolved references, and copies the final PDF to
`paper/marchenko-pastur.pdf`. Auxiliary files are removed. The included PDF was
built with Tectonic 0.17.0 and visually checked page by page. Tectonic may need
network access on its first run to populate its TeX resource cache. The Lean
proof build does not require Tectonic.

The paper describes the mathematical baseline at commit `7020123`, tagged
`stage-11-marchenko-pastur`. It is an exposition of the formal development,
with definitions, proof arguments, references, and the precise scope of the
main theorem. It does not replace inspection of the Lean statements.

## Supplementary computations

These checks use the Python standard library:

```sh
python3 experiments/exact_moments.py
python3 experiments/tree_patterns.py
python3 experiments/variance.py
python3 experiments/spectral_interface.py
python3 experiments/mp_density.py
```

They write results under `experiments/results/`. Exact enumeration can take
longer than incremental Lean builds. The quadrature script performs numerical
integration, not certified interval arithmetic. The Python code itself is not
formally verified.

Optional simulations and plots use pinned Python requirements:

```sh
python3 -m venv .venv
.venv/bin/pip install -r experiments/requirements.txt
.venv/bin/python experiments/simulate.py
```

The [experiment guide](EXPERIMENTS.md) explains the checks, recorded sample
counts, and evidential limitations. Simulations are illustrations, not part of
the proof of the general theorem.

## File integrity

`SOURCE_SHA256.json` records the SHA-256 hash of each included repository file,
excluding the manifest itself. It covers the Lean sources, documentation,
experiment results, and compiled paper. Verify a checkout with:

```sh
python3 - <<'PY'
import hashlib
import json
from pathlib import Path

manifest = json.loads(Path("SOURCE_SHA256.json").read_text())
for name, expected in manifest.items():
    actual = hashlib.sha256(Path(name).read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f"Hash mismatch: {name}")
print(f"Verified {len(manifest)} files")
PY
```

Rebuilding the PDF or regenerating logs may change their bytes. The manifest
identifies the checked-in artifact; it is not a claim of byte-identical outputs
across arbitrary operating systems or TeX resource versions.
