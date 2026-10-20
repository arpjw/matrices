# Verification record

## Paper and documentation package

Prepared on 2026-10-20. The 10-page paper is included as editable LaTeX and a
compiled PDF, with a portable Tectonic build script. The final build used
Tectonic 0.17.0 and completed without TeX warnings. All ten pages were rendered
and visually reviewed; text extraction found no unresolved references or
replacement characters. The author metadata is Arya Somu.

All relative links in the revised README and added reader guides resolve.
The module map covers all 62 mathematical modules. The existing tracked text
files were checked for local user paths, email addresses, and common credential
patterns, with no matches. No repository visibility change was made.

All 70 Lean source, proof-check script, and dependency-pin files are unchanged
from the validated mathematical baseline and match the verified build tree
byte for byte. The Lean build and supplementary mathematical experiments were
not rerun for this documentation-only package. Their recorded validation is
below. The new paper build script passed a shell syntax check and was executed
successfully. `SOURCE_SHA256.json` covers the new documentation and PDF as well.

## Mathematical baseline

Verified locally on 2026-10-20. This record covers the finite-dimensional
milestone, all-order walk expansion, partition-coefficient formula,
coefficient boundary cases, doubled-tree graph classification, the general
rooted ordered tree bijection, the Narayana coefficient formula, all fixed-order
expected-moment limits, explicit finite-size bounds, and fixed-order moment
concentration, empirical spectral measures, their moment bridge, and the
normalization and all moments of the explicit MP density plus atom, uniform
tightness, moment determinacy, and the full Marchenko-Pastur weak-convergence
in probability theorem for independent fair-sign entries. Earlier
stages are retained at `stage-1-finite-moments` (`0523463`) and
`stage-2-walk-counting` (`b23f33c`), and `stage-3-pattern-coefficients` (`40eeb1d`).
The doubled-tree checkpoint is `stage-4-doubled-trees` (`e2cb215`).
The bijection checkpoint is `stage-5-ordered-tree-bijection` (`1943198`).
The Narayana checkpoint is `stage-6-narayana` (`dce93b9`).
The expected-moment checkpoint is `stage-7-expected-moments` (`abaabe1`).
The concentration checkpoint is `stage-8-moment-concentration`.
The spectral checkpoint is `stage-9-spectral-interface` (`734a212`).
The density checkpoint is `stage-10-mp-density` (`d5888c1`).
The current checkpoint is `stage-11-marchenko-pastur`.

## Lean

- Lean 4.28.0, arm64-apple-darwin, release commit
  7e01a1bf5c70fc6167d49c345d3bf80596e9a79b.
- Mathlib revision 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
- `scripts/check.sh`: passed.
- `lake build`: passed, 2,954 jobs, with dependency build products largely
  obtained from the official mathlib cache. No warnings were emitted.
- Sixty-two mathematical source modules, 358 exported named theorems and twenty
  private helpers, plus the aggregate import and audit module. No new mathematical
  result is claimed from the theorem count.
- Source scan: no unfinished-proof tokens, custom axiom declarations, or
  `native_decide` calls in the project Lean sources.
- 372 declaration dependency audits passed, including the central labeling,
  walk, ordered-tree, and refined coefficient equivalences, plus the formal
  series recurrence, general Narayana coefficient theorem, explicit finite-size
  bounds, all fixed-order expected-moment limits, the paired-labeling equivalence,
  variance bounds, convergence in probability, the full spectral interface,
  density normalization, all MP moments, the exact atom, compact support, and
  identification of the random-matrix moment limits with the explicit law,
  global polynomial bounds, the general compact moment method, moment
  determinacy, uniform tightness, and the complete weak-convergence theorem.
  Every exported named theorem is now explicitly audited, with a source-coverage
  check enforced by the audit script. This includes ten foundational helper
  lemmas from the initial stage that were previously absent from the individual
  audit list. Audited dependencies are
  confined to `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`, custom
  domain axiom, `Lean.ofReduceBool`, or `Lean.trustCompiler` was reported.
  Some definitional selector lemmas report no axioms at all. The audit parser
  now recognizes that explicit Lean output as well as nonempty dependency lists;
  the allowed dependency set is unchanged.
- Negative control passed: the claim that the 1-by-1 finite second moment equals
  2 was rejected with an unsolved mathematical goal. The actual moment is 1.
  The audit checks that rejection was not caused by a missing import or file.
- A second negative control passed: A_(3,2,2)=4 was rejected after applying
  the general Narayana theorem. The actual coefficient is 3. It failed with
  the intended unsolved mathematical goal, not an infrastructure error.
- A third negative control passed: discarding the finite bias at p=n=1 for
  k=2 was rejected with the goal False. The actual absolute bias from P_2(1)
  is 1. This likewise failed for mathematics, not missing infrastructure.
- A fourth negative control passed: the claim that a fair sign has zero
  variance was rejected with the goal False. The proved variance is one.
- A fifth negative control passed: zero total empirical mass was rejected by
  the proved zeroth-moment identity, with the goal False.
- A sixth negative control passed: zero mass at zero for a two-by-one covariance
  matrix was rejected with the proved lower bound 1/2 in the context. Both
  spectral controls fail on their mathematical claims, not missing infrastructure.
- A seventh negative control passed: assigning continuous mass one at gamma=2
  was rejected. The proved mass is 1/2, with the missing mass at zero.
- An eighth negative control passed: assigning MP second moment two at gamma=2
  was rejected. The proved moment is three.
- A ninth negative control passed: assigning zero-atom mass 1/2 at gamma=1 was
  rejected. The proved atom is zero. All three new controls reduce to False,
  and the audit confirms that no infrastructure error caused rejection.
- A tenth negative control passed: delta_1 and (delta_0+delta_2)/2 have equal
  first moments, but the bounded continuous clipped identity distinguishes them.
  The control proves unit mass, the common first moment, and continuity and
  boundedness of the test before the incorrect integral equality reduces to False.
- An eleventh negative control passed: the constant-one test rejects equating
  full empirical mass with the continuous MP mass at gamma=2. It reduces to False.
  This detects omission of the atom in a proposed weak limit.
- The audit now requires exactly one diagnostic error per negative control,
  specifically the unsolved intended goal. All eleven controls passed this
  stricter check, ruling out incidental elaboration or auxiliary-proof failures.

Logs: [build and audit](validation/lean-check.log),
[axioms](validation/axioms.log),
[normalization negative control](validation/negative-control.log),
[Narayana negative control](validation/narayana-negative-control.log),
[finite-bias negative control](validation/finite-bias-negative-control.log),
[variance negative control](validation/variance-negative-control.log),
[spectral mass negative control](validation/spectral-mass-negative-control.log),
[spectral zero-atom negative control](validation/spectral-atom-negative-control.log),
[MP continuous-mass negative control](validation/mp-mass-negative-control.log),
[MP second-moment negative control](validation/mp-moment-negative-control.log),
[MP critical-atom negative control](validation/mp-critical-atom-negative-control.log),
[first-moment-only negative control](validation/first-moment-only-negative-control.log),
[weak-limit mass negative control](validation/weak-mass-negative-control.log).

The standard Lean kernel and the pinned imported mathematics remain trusted.
We did not run a second independently implemented proof checker.

The final build ran in a temporary local directory after iCloud offloading
caused reads of generated artifacts in the original workspace to fail. Lean
and all dependency sources were restored at the pinned versions. Hashes of all
70 Lean source, check-script, and dependency-pin files matched the deliverable
for the final validation. The logs in the validation directory are from this
successful run. The pinned Lean and mathlib versions were retained throughout.

## Exact computational checks

`python3 experiments/exact_moments.py`: passed at the expected-moment checkpoint
on 2026-10-20. Its source and results are unchanged in the weak-convergence checkpoint.

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
- 40 exact finite-bias comparisons at orders 0 through 4 across the same eight
  dimension pairs. Positive-order moments come from direct matrix enumeration;
  zeroth moments are the normalized identity trace. The compact ratio interval
  is [1/4,4].
- 56 additional finite-bias comparisons at orders 0 through 7, with moments
  computed by the independent partition enumerator. Dimensions include (1,7),
  (7,1), (16,64), (64,16), (8,8), (4,16), and (16,4), in the interval [1/7,7].
- Six exact ratio-rate controls use n=m^2 and p=m^2+m. The second-moment bias
  at the current ratio is -1/n; the absolute error to the gamma=1 limit,
  multiplied by n, is m-1. Thus ratio convergence alone does not give the
  O(1/n) rate to the limiting polynomial.

Data: [exact-moments.json](../experiments/results/exact-moments.json).
Run: [exact checker log](validation/exact-check.log).

## Variance and concentration checks

`python3 experiments/variance.py`: passed on 2026-10-20.

- Enumerated the same eight finite ensembles, totaling 4,774 sign matrices.
  Computed 40 exact rational variances at orders 0 through 4 and checked the
  explicit variance bound. Orders zero and one have zero variance.
- The second-moment variances agree with 4(p-1)(n-1)/(p n^3); for p=n=2 the
  variance is 1/4. This closed formula is independently checked in Python,
  not separately proved as an exported Lean theorem.
- 32 comparisons at orders 0 through 3 connect actual paired labeled walks,
  independent joint-partition enumeration, and directly computed variances.
  The paired-walk upper-bound count drops closure and includes all jointly
  even pairs sharing a row; the covariance count retains closed walks and
  matching nonzero parity profiles.
- 797,438 shared-row partition candidates were examined. The surviving counts
  at orders 0,1,2,3 are 1,4,113,6545. Independent traversal confirms connectedness
  of each surviving quotient graph and the vertex bound r+c<=2k+1.
- 160 exact event probabilities were checked against the actual mean-square
  Chebyshev bound and the explicit formal bound. Positive-variance examples
  and examples with strict Chebyshev inequality are retained.

Data: [variance.json](../experiments/results/variance.json).
Run: [variance checker log](validation/variance-check.log).
The general all-order results are Lean theorems; this Python code is not formally verified.

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
order. The graph and ordered-tree checker was last run at the Narayana stage
on the same date; its code and proof modules are unchanged in this checkpoint.
The exact-moment checker was extended and rerun for the expected-moment stage.
The concentration checkpoint adds and runs a separate variance checker.
The Python code is not formally verified.

Data: [tree-patterns.json](../experiments/results/tree-patterns.json).

## Exact spectral-interface checks

`python3 experiments/spectral_interface.py`: passed on 2026-10-20.

- Exhaustively checked 2,826 sign matrices over all 16 dimension pairs with
  1<=p,n<=5 and min(p,n)<=2. Four additional matrices cover a zero matrix,
  distinct diagonal values, rank one with non-sign entries, and repeated
  positive eigenvalues.
- 19,810 exact rational moment comparisons at orders zero through six, using
  direct matrix multiplication and separately obtained eigenvalue lists.
- 12,215 exact determinant evaluations certify the characteristic polynomials
  at p+1 distinct points for each matrix. Every eigenvalue multiplicity is retained.
- 2,830 independent rank eliminations check that zero multiplicity equals
  nullity and that the zero atom meets the rectangular lower bound.
- Three incorrect-measure controls fail: dropping zeros loses total mass,
  normalizing over only positive values changes the first moment, and
  deduplicating repeated eigenvalues loses multiplicity.

Data: [spectral-interface.json](../experiments/results/spectral-interface.json).
Run: [spectral checker log](validation/spectral-check.log).
The general spectral results are Lean theorems; the exact Python checker is
independent finite evidence, not formally verified code.

## Explicit MP density checks

`python3 experiments/mp_density.py`: passed on 2026-10-20.

- Numerically integrated 165 density moments at orders zero through ten over
  15 aspect ratios: 1/100, 1/10, 1/4, 1/2, 9/10, 99/100, 999/1000, 1,
  1001/1000, 101/100, 11/10, 2, 4, 10, and 100.
- The checker evaluates the explicit density with x=a+(b-a)u^2 and adaptive
  Simpson quadrature, refining the panel with the largest estimated error.
  It uses a global error budget and compares to the exact rational Narayana
  values. It does not reuse the formal proof's angular recurrence to obtain
  the integrals.
- Every continuous mass agrees with min(1,1/gamma). Adding the specified atom
  gives mass one. All positive full-measure moments agree with the moment formula.
- Requested quadrature tolerance was 1e-11 after scaling by max(1,expected).
  Acceptance tolerance was 1e-8; the largest observed scaled error was 1.58e-12.
  These are numerical diagnostics, not certified error enclosures.
- Twelve refinement checks compare quadrature tolerances 1e-8 and 1e-11 at
  gamma=999/1000, 1, 1001/1000, and 4, for orders zero, two, and ten.
- 450 exact rational recurrence checks cover the same 15 ratios and recurrence
  indices zero through 29, involving moments through order 32.
- Two normalization controls reject treating the continuous part alone as a
  probability law at gamma=4 and renormalizing that part to mass one. The latter
  changes the first moment from one to four.

Data: [mp-density.json](../experiments/results/mp-density.json).
Run: [MP density checker log](validation/mp-density-check.log).
The quadrature is numerical evidence and its code is not formally verified.
Normalization, integrability, and the moment formula at every natural order
and every positive real aspect ratio are independently proved in Lean.

## Numerical illustration

`experiments/simulate.py`: passed positivity and first-trace checks on 105
seeded matrices, with all raw second-moment observations retained. The plot was
rendered and visually inspected. Zero eigenvalues for p>n are retained in the
normalization. Error bars are sample standard deviations across eight seeds,
not confidence intervals or formal guarantees.

Data: [simulation.json](../experiments/results/simulation.json).
Plot: [PNG](../experiments/results/spectral-experiment.png),
[SVG](../experiments/results/spectral-experiment.svg).

## Completed flagship scope

The arbitrary-order labeled trace expansion, exact partition-coefficient
formula, coefficient boundary and support results, and doubled-tree graph
classification are proved. The general rooted ordered tree bijection is also
proved, preserving the visit order, root, and both color counts; it is linked
to the original leading moment coefficients by a cardinality theorem.
The general Narayana closed formula and Catalan total are now proved, completing
the leading-pattern counting stage. All fixed-order expected-moment limits
and explicit finite-size bias bounds are proved. Explicit variance bounds,
vanishing mean-square error, and convergence in probability of each fixed
random moment are proved as well. The empirical spectral probability measure,
all-order trace-moment bridge, nonnegative support, exact nullity atom, and
transfer of concentration to empirical moments are proved. The explicit MP
density plus atom is now proved normalized, compactly supported, and to have
all natural moments, including gamma=1. The random-matrix moment limits are
identified with the moments of this actual law. Uniform tightness, compact
moment determinacy, and weak convergence in probability against every bounded
continuous real test are now proved as well. `marchenkoPastur_theorem` closes
the entire chain for independent fair-sign entries and every positive finite
limiting aspect ratio. No proof obligation remains for the original flagship
scope. General entry distributions, almost-sure convergence, spectral-edge
limits, and individual-atom convergence are outside that scope.
See [BLUEPRINT.md](BLUEPRINT.md) and [WEAK_CONVERGENCE.md](WEAK_CONVERGENCE.md).
