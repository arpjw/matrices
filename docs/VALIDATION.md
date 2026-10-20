# Verification record

Verified locally on 2026-10-20. This record covers the finite-dimensional
milestone, all-order walk expansion, partition-coefficient formula,
coefficient boundary cases, doubled-tree graph classification, the general
rooted ordered tree bijection, and the Narayana coefficient formula,
not the full Marchenko-Pastur theorem. Earlier
stages are retained at `stage-1-finite-moments` (`0523463`) and
`stage-2-walk-counting` (`b23f33c`), and `stage-3-pattern-coefficients` (`40eeb1d`).
The doubled-tree checkpoint is `stage-4-doubled-trees` (`e2cb215`).
The bijection checkpoint is `stage-5-ordered-tree-bijection` (`1943198`).
The current checkpoint is `stage-6-narayana`.

## Lean

- Lean 4.28.0, arm64-apple-darwin, release commit
  7e01a1bf5c70fc6167d49c345d3bf80596e9a79b.
- Mathlib revision 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
- `scripts/check.sh`: passed.
- `lake build`: passed, with dependency build products largely obtained from
  the official mathlib cache.
- Thirty-two mathematical source modules, 195 exported named theorems and seven private
  helpers, plus the aggregate import and audit module. No new mathematical
  result is claimed from the theorem count.
- Source scan: no unfinished-proof tokens, custom axiom declarations, or
  `native_decide` calls in the project Lean sources.
- 197 declaration dependency audits passed, including the central labeling,
  walk, ordered-tree, and refined coefficient equivalences, plus the formal
  series recurrence and general Narayana coefficient theorem. Audited dependencies are confined
  to `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`, custom
  domain axiom, `Lean.ofReduceBool`, or `Lean.trustCompiler` was reported.
  Two definitional selector lemmas report no axioms at all. The audit parser
  now recognizes that explicit Lean output as well as nonempty dependency lists;
  the allowed dependency set is unchanged.
- Negative control passed: the claim that the 1-by-1 finite second moment equals
  2 was rejected with an unsolved mathematical goal. The actual moment is 1.
  The audit checks that rejection was not caused by a missing import or file.
- A second negative control passed: A_(3,2,2)=4 was rejected after applying
  the general Narayana theorem. The actual coefficient is 3. It failed with
  the intended unsolved mathematical goal, not an infrastructure error.

Logs: [build and audit](validation/lean-check.log),
[axioms](validation/axioms.log),
[normalization negative control](validation/negative-control.log),
[Narayana negative control](validation/narayana-negative-control.log).

The standard Lean kernel and the pinned imported mathematics remain trusted.
We did not run a second independently implemented proof checker.

The final build ran in a temporary local directory after iCloud offloading
caused reads of generated artifacts in the original workspace to fail. Lean
and all dependency sources were restored at the pinned versions. Hashes of all
40 Lean source, check-script, and dependency-pin files matched the deliverable
for the final validation. The logs in the validation directory are from this
successful run. The pinned Lean and mathlib versions were retained throughout.

## Exact computational checks

`python3 experiments/exact_moments.py`: passed again on 2026-10-20.

- 4,774 complete sign matrices across dimensions (1,1), (1,4), (2,1), (2,2),
  (2,3), (3,2), (3,3), and (3,4).
- 32 exact rational comparisons of normalized moments, orders 1 through 4,
  between direct matrix multiplication and independent partition enumeration.
- 40 comparisons of rooted labeled walk enumeration with partition counts at
  orders 0 through 4 across the same eight dimension pairs. Normalized counts
  also agree with direct sign-matrix moments, with zeroth moments checked as 1.
- 120 equality-pattern labeling fibers checked by exhaustively enumerating
  499 assignments across 25 domain/label-size combinations. Empty domains and
  cases with too few labels are included.
- Coefficient tables from the position-partition encoding, with k+1 row
  positions and k column positions, agree with the earlier cyclic encoding
  at orders 0 through 7. The order-zero coefficient table has one entry,
  A_(0,1,0)=1, in the exact computation.
- The first, second and proposed third moment formulas agree with enumeration.
  Only the first and second moment formulas are currently proved in Lean.
- For every order 1 through 7, computed surviving patterns satisfy r+c <= k+1,
  and the coefficients at equality agree with the Narayana formula.
  The vertex bound, partition grouping, and falling-factorial coefficient
  formula are proved for every order in Lean. The general Narayana enumeration
  is now proved as well, with rational and exact integer versions. The Python
  enumerator itself has not been formally verified against the Lean pattern type.

Data: [exact-moments.json](../experiments/results/exact-moments.json).

## Graph and ordered-tree checks

`python3 experiments/tree_patterns.py`: passed on 2026-10-20.

- 189,455 partition graphs at orders 0 through 6, including nonsurviving patterns.
  Traversal checks connectivity and detects cycles independently of edge counts.
- Every surviving pattern in that range satisfies the equivalence between
  maximal block count and a tree with each entry occurring exactly twice.
- Explicit counterexamples check that neither tree structure alone nor double
  occurrence alone implies maximality.
- All 626 rooted ordered trees at orders 0 through 7: the contour map is injective,
  its image equals the independently enumerated leading patterns, both inverse
  identities hold, and row-refined counts agree with Narayana numbers.
- The same 626 trees also check the first-child / remaining-children encoding,
  its inverse to child lists, canonical sum-type contour labels, and the
  color-reversing count recurrence used in the Lean representation.

The doubled-tree graph characterization and ordered-tree bijection are now
proved in Lean at every order, including both inverse identities and both
color counts. `patternCoefficient_eq_treeCount` identifies the original
leading coefficients with refined tree counts. The Narayana closed formula
is now proved at every positive order, and the Catalan total count at every
order. Both independent Python checkers were rerun for this stage. Their
mathematical checks are unchanged; their status descriptions now reflect the
formal result. The Python code is not formally verified.

Data: [tree-patterns.json](../experiments/results/tree-patterns.json).

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

The arbitrary-order labeled trace expansion, exact partition-coefficient
formula, coefficient boundary and support results, and doubled-tree graph
classification are proved. The general rooted ordered tree bijection is also
proved, preserving the visit order, root, and both color counts; it is linked
to the original leading moment coefficients by a cardinality theorem.
The general Narayana closed formula and Catalan total are now proved, completing
the leading-pattern counting stage. The project does not yet prove all
expected-moment limits, finite-size remainder bounds, variance bounds, the
spectral-measure moment bridge, normalization and moments of the MP measure, or weak convergence in probability. The expected-second-moment limit
is not a substitute for these steps. See [BLUEPRINT.md](BLUEPRINT.md).
