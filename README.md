# Random matrices in Lean

A research project toward a complete Lean proof of the Marchenko-Pastur law for
sample covariance matrices with independent fair-sign entries.

The current milestone constructs the explicit Marchenko-Pastur density plus
zero atom and proves its normalization and all natural moments for every gamma>0:

    mu_gamma = max(1-1/gamma,0) delta_0 + rho_gamma(x) dx,
    integral x^k d mu_gamma = P_k(gamma), including k=0.

The continuous density has mass min(1,1/gamma). The full measure is a probability
measure with compact nonnegative support, and its zero atom has exactly the
displayed mass. The proof includes the singular endpoint case gamma=1.

The established empirical moment theorem is now identified with this actual law:

    Pr(|integral x^k d mu_(X_m) - integral x^k d mu_gamma| > epsilon) -> 0,
    n_m -> infinity, p_m/n_m -> gamma > 0, epsilon > 0.

Weak convergence against all bounded continuous test functions remains open.
See [the MP density proof guide](docs/MP_DENSITY.md) for the analytic proof and
[the spectral proof guide](docs/SPECTRAL_MEASURES.md) for the empirical measure.

The initial finite-moment stage is preserved at the Git tag
`stage-1-finite-moments` (commit `0523463`).
The all-order walk stage is preserved at `stage-2-walk-counting` (`b23f33c`).
The exact coefficient stage is preserved at `stage-3-pattern-coefficients`
(`40eeb1d`). The doubled-tree stage is preserved at `stage-4-doubled-trees`.
The general bijection is preserved at `stage-5-ordered-tree-bijection` (`1943198`).
The Narayana formula is preserved at `stage-6-narayana` (`dce93b9`).
The expected-moment stage is preserved at `stage-7-expected-moments` (`abaabe1`).
The concentration stage is preserved at `stage-8-moment-concentration`.
The spectral interface stage is preserved at `stage-9-spectral-interface`.
The density and moment stage is preserved at `stage-10-mp-density`.

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
| Walks | Deterministic expansion at every order; exact expected moments as counts of even closed walks |
| WalkBounds | r+c <= k+1 for even walks; every used entry occurs twice at equality |
| Labelings | Equality-pattern fibers are injective block labelings; exact falling-factorial multiplicities |
| WalkPositions | Bijection between rooted walks and position-indexed row/column assignments |
| WalkPatterns | Closure and parity depend only on partitions; exact partition-weighted count |
| PatternCoefficients | Dimension-independent coefficients and the exact finite moment expansion |
| PatternBounds | Abstract pattern vertex bound and coefficient vanishing above r+c=k+1 |
| PatternBoundary | Exact zeroth-order coefficients and exclusion of empty row/column blocks |
| PatternGraph | Connected bipartite graph on quotient blocks; exact vertex and edge counts |
| PatternTrees | Leading patterns are precisely closed doubled trees, in both directions |
| PatternContour | Genuine graph walks preserving entry order, closure, length, and double occurrence |
| TreeWalkSplit | Bridge-based split into the first child excursion and remaining root excursions |
| OrderedContours | Recursive ordered contours, unique shape, and reconstruction of doubled tree walks |
| CanonicalContours | Canonical distinct vertex labels and injective relabeling of every contour |
| ContourPositions | Even/odd positions and the color-reversing row/column count recurrence |
| ContourEdges | Contour closure and even edge multiplicities |
| ContourLabelings | Fin-indexed row/column label functions, block counts, and ordered entry word |
| ContourPatterns | Every ordered tree produces a surviving maximal original pattern |
| ContourRoundTrip | Recovering the original partitions and full contour through quotient labels |
| LeadingTreeBijection | General bijection, both inverse identities, and preservation of both block counts |
| TreeCoefficients | Fixed-order and refined equivalences; exact leading coefficient as a tree count |
| TreeGeneratingSeries | Finite tree-counting polynomials, two color series, and the quadratic equation |
| TreePolynomialRecurrence | Formal differential identity and the three-term polynomial recurrence |
| NarayanaArithmetic | Binomial expression satisfies the same recurrence, including support boundaries |
| NarayanaTreeCount | Every tree-polynomial coefficient equals the Narayana expression |
| NarayanaCoefficients | Closed formula for the original leading coefficients; exact division and Catalan total |
| FallingFactorialBounds | Distinct-label fractions and explicit collision losses |
| MomentPolynomials | Leading diagonal equals the Narayana moment polynomial, including order zero |
| PatternBudget | Explicit dimension-independent upper bound on all coefficient counts |
| LabelWeightBounds | Leading collision errors and suppression of lower-order patterns |
| ExpectedMomentBounds | Uniform C_k(a,B)/n bound relative to the polynomial at p/n |
| ExpectedMomentLimit | Every fixed expected moment converges at a positive finite aspect-ratio limit |
| FiniteVariance | Exact finite covariance, variance, event probabilities, Chebyshev, and disjoint-word cancellation |
| PairPatterns | Joint partition graph, shared-row connectedness, and the 2k+1 vertex bound |
| PairCounting | Paired walks are joint label assignments; exact falling-factorial pattern counts |
| PairCountBounds | Explicit partition budget and uniformly bounded normalized pair count |
| WalkCovariance | Exact trace-variance expansion and the overlapping-pair upper bound |
| VarianceBounds | Uniform O(1/n) variance bounds at fixed order |
| MomentConcentration | Quantitative tail bounds, vanishing mean-square error, and convergence in probability |
| SpectralGeometry | Eigenvalues with multiplicities, trace powers, and zero multiplicity equal to nullity |
| EmpiricalMeasure | Empirical probability measure, integral formula, nonnegative support, and forced zero atom |
| SpectralConcentration | Expected moments, mean-square convergence, and concentration of empirical spectral moments |
| MPParameters | Explicit MP density, endpoints, atom, and angular parametrization |
| MPPolynomialRecurrence | Real MP polynomial recurrence inherited from the tree count |
| MPMomentRecurrence | Integration-by-parts recurrence and all angular moments |
| MPTrigNormalization | Arctangent evaluation of reciprocal trigonometric integrals |
| MPAngularNormalization | Continuous mass for every positive aspect ratio, including one |
| MPDensityIntegrals | Lebesgue substitution, integrability, normalization, and all positive density moments |
| MPMeasure | Explicit probability measure, exact atom, all moments, and compact support |
| MPIdentification | Empirical moment concentration toward the moments of the explicit MP law |

The general finite identity, for every k >= 0 and p,n > 0, is

    E[M_k] = C_k(p,n) / (p n^k),

where C_k counts labeled rooted closed alternating walks with 2k entry visits,
each entry appearing an even number of times. This is a Lean theorem about the
actual finite sign ensemble. In particular, C_0=p and E[M_0]=1.
See [the walk proof guide](docs/WALKS.md) for the encoding and proof chain.

The new partition grouping proves, for every k >= 0,

    C_k(p,n) = sum_(r,c) A_(k,r,c) (p)_r (n)_c,
    A_(k,r,c) = 0 whenever r+c > k+1.

Here A counts surviving equality patterns and (p)_r is the falling factorial.
The coefficients depend on k,r,c only, independently of p and n. See
[the partition proof guide](docs/PATTERNS.md) for the formal bijections.

The new graph characterization is

    surviving pattern with r+c=k+1
      iff closed pattern on a tree with every entry used exactly twice.

This holds at every order, including the empty walk. See
[the doubled-tree proof guide](docs/TREES.md) for the graph constructions.
The new bijection strengthens this to the exact coefficient identity

    A_(k,r,c) = #{ordered rooted trees with k edges, r row and c column vertices},
                                                        whenever r+c=k+1.

The root is a row vertex, and colors alternate with depth. See
[the ordered-tree proof guide](docs/ORDERED_TREES.md) for both inverse maps and
the connection to the original moment coefficients. The refined tree count is
now evaluated by the formula choose(k,r) choose(k,r-1)/k, and the total number
of leading patterns is the Catalan number. See [the counting proof guide](docs/NARAYANA.md)
for the generating-function argument and boundary cases.

The previously proved second-moment specialization is

    E[M_2] = 1 + (p-1)/n = 1 + p/n - 1/n.

For every fixed k>0, the expectation now tends to

    P_k(gamma) = sum_(r=1)^k choose(k,r) choose(k,r-1) gamma^(r-1) / k

at a positive limiting aspect ratio; P_0=1 is handled separately. The explicit
finite-size constant and the distinction between bias at the current ratio
and error to the limiting ratio are in [the expected-moment proof guide](docs/EXPECTED_MOMENTS.md).
The additional covariance argument now proves vanishing mean-square error and
convergence in probability of each fixed random moment. See
[the concentration proof guide](docs/CONCENTRATION.md) for the pair graph,
explicit constants and the finite probability bound. The new
[spectral proof guide](docs/SPECTRAL_MEASURES.md) connects these results to
integrals against the empirical eigenvalue probability measure. The
[MP density proof guide](docs/MP_DENSITY.md) identifies their limiting moments
with the explicitly normalized density plus atom, at every order.
Weak convergence of the random spectral measures remains open.

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
  Mathlib.Algebra.BigOperators.Group.List.Basic \
  Mathlib.Data.Fintype.CardEmbedding Mathlib.Data.Setoid.Basic \
  Mathlib.Data.Fintype.Powerset Mathlib.Data.Finite.Card Mathlib.Data.Fin.Tuple.Basic \
  Mathlib.Combinatorics.SimpleGraph.Acyclic Mathlib.Data.Tree.Basic \
  Mathlib.Combinatorics.Enumerative.Catalan \
  Mathlib.RingTheory.PowerSeries.Derivative Mathlib.Tactic.LinearCombination \
  Mathlib.Analysis.Matrix.PosDef Mathlib.MeasureTheory.Integral.Bochner.Basic \
  Mathlib.MeasureTheory.Measure.ProbabilityMeasure Mathlib.MeasureTheory.Measure.Support \
  Mathlib.Analysis.SpecialFunctions.Integrals.Basic \
  Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv \
  Mathlib.MeasureTheory.Function.JacobianOneDim \
  Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
scripts/check.sh
```

The finite checks and density quadrature use only the Python standard library:

```sh
python3 experiments/exact_moments.py
python3 experiments/tree_patterns.py
python3 experiments/variance.py
python3 experiments/spectral_interface.py
python3 experiments/mp_density.py
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
pairs, independently comparing direct matrix multiplication with partition
counts for the first four moments. Another 40 checks compare the rooted walk
encoding with partition counts, including the empty-walk case. It also checks
leading Narayana coefficients through order seven using exact integers.
The position-partition encoding is independently checked at orders 0 through 7,
and exhaustive assignments check 120 labeling fibers, including empty domains
and insufficient label counts. The general partition grouping and coefficient
support bound and general Narayana formula are proved in Lean. The checker now
also validates 40 finite-bias bounds against these direct moments, another 56
against partition counts through order seven, and six examples distinguishing
current-ratio bias from convergence to a limiting ratio. The general bound and
all fixed-order expected-moment limits are proved in Lean.

The graph checker independently verifies 189,455 partition graphs at orders
0 through 6. An independent implementation checks both bijection inverses on all 626 trees
at orders 0 through 7, as well as the first-child representation, canonical
contour, and color-count recurrence. The graph classification, general
bijection, and Narayana enumeration are now proved in Lean. The Python implementation itself is not
formally verified.

The variance checker independently enumerates 4,774 sign matrices, checks 40
exact variances and 160 tail bounds, and compares 32 paired-walk counts against
joint partition enumeration through order three. It checks 797,438 shared-row
partition candidates and retains cases with positive variance. The general
variance and convergence-in-probability theorems are proved in Lean.

The exact spectral checker verifies 2,826 small sign matrices and four additional
matrices. It compares 19,810 spectral moments to direct matrix powers, certifies
characteristic polynomials by 12,215 exact determinant evaluations, and checks
2,830 ranks and zero atoms. Controls reject dropping zeros, renormalizing only
the positive spectrum, and discarding multiplicities. These finite computations
supplement the general Lean spectral-measure theorems.

The density checker numerically integrates 165 moments at 15 aspect ratios,
including values on both sides of gamma=1 and the critical value itself. It
also performs 450 exact rational recurrence checks, twelve quadrature refinement
comparisons, and controls for omitted atoms and incorrect renormalization.
The quadrature is numerical evidence; normalization and all moments are proved
in Lean for every positive real aspect ratio.

The spectral figure uses 105 reproducible simulated matrices. It preserves
structural zero eigenvalues for p > n and shows the finite -1/n bias in the
second moment. Its histograms and error bars are illustrations, not formal
proofs or evidence of a new mathematical result.

![Spectral experiment](experiments/results/spectral-experiment.png)

## The substantial work ahead

[BLUEPRINT.md](docs/BLUEPRINT.md) gives the exact theorem and dependency graph.
The leading-pattern classification, ordered-tree bijection, and Narayana
count and all fixed-order expected-moment limits with explicit finite-size
bounds are complete. Explicit variance bounds and convergence in probability
of each fixed random moment are complete. The empirical eigenvalue probability
measure, trace-moment bridge, nonnegative support, forced zero atom, and transfer
of concentration to spectral moments are complete. The explicit MP density plus
atom is now proved normalized, compactly supported, and to have all the required
moments, including the gamma=1 case. The remaining stage is tightness,
moment-to-measure convergence, and weak convergence in probability.

[PRIOR_ART.md](docs/PRIOR_ART.md) records the inspected existing projects and their
limitations. This is a formalization of a classical result. No claim of novelty
or first formalization has been established.
