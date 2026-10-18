# Random matrices in Lean

A research project toward a complete Lean proof of the Marchenko-Pastur law for
sample covariance matrices with independent fair-sign entries.

The first milestone is finite-dimensional: exact sign moments, covariance
identities, and convergence of the expected second trace moment. The full
spectral-distribution theorem is still open in this project.

## Model and conventions

X is p-by-n with independent entries uniform on {-1,+1}. Set

    S = X X^T / n,      M_k = trace(S^k) / p,      gamma = p/n.

Finite expectation is defined as the uniform sum over all 2^(pn) sign
assignments. Both dimensions must be positive in normalized moment theorems.
The flagship target covers gamma > 0, including the zero atom of mass
max(1 - 1/gamma, 0) when gamma > 1.

## Proof modules

| Module | Mathematical content |
| --- | --- |
| FiniteAverage | Uniform expectation and independent-coordinate factorization |
| Rademacher | All-order monomial parity cancellation and rectangle moments |
| WordMoments | Arbitrary coordinate-word moments and mixed moments by multiplicity parity |
| Covariance | Trace expansion, exact first moment, exact expected second moment |
| Geometry | Positive semidefiniteness, rank at most n, nullity at least p-n |
| SecondMomentLimit | Exact second-moment bias and convergence of its expectation |

The central finite identity is

    E[M_2] = 1 + (p-1)/n = 1 + p/n - 1/n.

For sequences with n tending to infinity and p/n tending to gamma, the expected
second moment therefore tends to 1+gamma. This does not by itself establish
concentration or weak convergence of the random spectral measures.

See [the verification record](docs/VALIDATION.md) for actual build and audit
results. The proof sources are required to contain no unfinished proofs, custom
axioms, or compiler-trust evaluation shortcuts. Standard Lean logical axioms are
allowed and reported explicitly by the audit.

## Build and reproduce

Pinned toolchain: Lean 4.28.0.
Pinned mathlib: 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
The lockfile pins all transitive packages. On this workspace the wrapper uses the
local toolchain under work/. On another machine install Lean through elan, which
reads lean-toolchain.

Fetch the relevant precompiled dependency files once:

```sh
scripts/lake.sh exe cache get \
  Mathlib.LinearAlgebra.Matrix.Rank Mathlib.LinearAlgebra.Matrix.PosDef \
  Mathlib.Data.Real.StarOrdered Mathlib.LinearAlgebra.Matrix.Trace \
  Mathlib.Analysis.SpecificLimits.Basic Mathlib.Tactic.Ring \
  Mathlib.Tactic.NormNum Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith \
  Mathlib.Algebra.BigOperators.Group.List.Basic
scripts/check.sh
```

The exact experiment uses only the Python standard library:

```sh
python3 experiments/exact_moments.py
```

The optional plots use the pinned requirements:

```sh
python3 -m venv .venv
.venv/bin/pip install -r experiments/requirements.txt
.venv/bin/python experiments/simulate.py
```

Dependencies and generated compiler artifacts live in .lake/, which is excluded
from source archives. No paid compute is required for this milestone.

## Experiments and their evidential status

The exact checker enumerates 4,774 sign matrices over eight small dimension
pairs, independently comparing direct matrix multiplication with alternating
walk counts for the first four moments. It also checks leading Narayana
coefficients through order seven using exact integers. These finite checks do
not prove the all-order counting theorem.

The spectral figure uses 105 reproducible simulated matrices. It preserves
structural zero eigenvalues for p > n and shows the finite -1/n bias in the
second moment. Its histograms and error bars are illustrations, not formal
proofs or evidence of a new mathematical result.

![Spectral experiment](experiments/results/spectral-experiment.png)

## The substantial work ahead

[BLUEPRINT.md](docs/BLUEPRINT.md) gives the exact theorem and dependency graph.
The next major step is the all-order alternating-walk expansion and the bound
r+c <= k+1 on surviving row/column patterns. Subsequent bottlenecks are the
Narayana counting theorem, variance estimates, formal spectral measures,
identification of the MP density plus atom, and moment-to-measure convergence.

[PRIOR_ART.md](docs/PRIOR_ART.md) records the inspected existing projects and their
limitations. This is a formalization of a classical result. No claim of novelty
or first formalization has been established.
