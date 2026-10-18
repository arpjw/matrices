# Verification record

Verified locally on 2026-10-18. This record covers the finite-dimensional
milestone and the all-order walk expansion and vertex bound, not the full
Marchenko-Pastur theorem. The initial stage is retained at Git tag
`stage-1-finite-moments` (`0523463`).

## Lean

- Lean 4.28.0, arm64-apple-darwin, release commit
  7e01a1bf5c70fc6167d49c345d3bf80596e9a79b.
- Mathlib revision 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
- `scripts/check.sh`: passed.
- `lake build`: passed, with dependency build products largely obtained from
  the official mathlib cache.
- Eight mathematical source modules, 42 exported named theorems and one private
  helper, plus the aggregate import and audit module. No new mathematical
  result is claimed from the theorem count.
- Source scan: no unfinished-proof tokens, custom axiom declarations, or
  `native_decide` calls in the project Lean sources.
- Thirty-two theorem dependency audits passed. Audited dependencies are confined
  to `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`, custom
  domain axiom, `Lean.ofReduceBool`, or `Lean.trustCompiler` was reported.
- Negative control passed: the claim that the 1-by-1 finite second moment equals
  2 was rejected with an unsolved mathematical goal. The actual moment is 1.
  The audit checks that rejection was not caused by a missing import or file.

Logs: [build and audit](validation/lean-check.log),
[axioms](validation/axioms.log),
[negative control](validation/negative-control.log).

The standard Lean kernel and the pinned imported mathematics remain trusted.
We did not run a second independently implemented proof checker.

The final build ran in a temporary local directory after iCloud offloading
caused reads of generated artifacts in the original workspace to fail. Lean
and all dependency sources were restored at the pinned versions. Hashes of all
16 Lean source, check-script, and dependency-pin files matched the deliverable
before that clean build. The logs below the validation directory are from
this successful validation run.

## Exact computational checks

`python3 experiments/exact_moments.py`: passed.

- 4,774 complete sign matrices across dimensions (1,1), (1,4), (2,1), (2,2),
  (2,3), (3,2), (3,3), and (3,4).
- 32 exact rational comparisons of normalized moments, orders 1 through 4,
  between direct matrix multiplication and independent partition enumeration.
- 40 comparisons of rooted labeled walk enumeration with partition counts at
  orders 0 through 4 across the same eight dimension pairs. Normalized counts
  also agree with direct sign-matrix moments, with zeroth moments checked as 1.
- The first, second and proposed third moment formulas agree with enumeration.
  Only the first and second moment formulas are currently proved in Lean.
- For every order 1 through 7, computed surviving patterns satisfy r+c <= k+1,
  and the coefficients at equality agree with the Narayana formula.
  The vertex bound is now proved for every order in Lean. The canonical pattern
  grouping and arbitrary-order Narayana enumeration are not yet Lean proofs.

Data: [exact-moments.json](../experiments/results/exact-moments.json).

## Numerical illustration

`experiments/simulate.py`: passed positivity and first-trace checks on 105
seeded matrices, with all raw second-moment observations retained. The plot was
rendered and visually inspected. Zero eigenvalues for p>n are retained in the
normalization. Error bars are sample standard deviations across eight seeds,
not confidence intervals or formal guarantees.

Data: [simulation.json](../experiments/results/simulation.json).
Plot: [PNG](../experiments/results/spectral-experiment.png),
[SVG](../experiments/results/spectral-experiment.svg).

## Remaining proof obligations

The arbitrary-order labeled trace expansion, exact parity-filtered expectation
formula, vertex bound, and double occurrence at maximal vertex count are proved.
The project does not yet prove canonical partition grouping, the tree
classification and Narayana formula, all expected-moment limits, variance
bounds, the spectral-measure moment bridge, normalization and moments of the MP
measure, or weak convergence in probability. The expected-second-moment limit
is not a substitute for these steps. See [BLUEPRINT.md](BLUEPRINT.md).
