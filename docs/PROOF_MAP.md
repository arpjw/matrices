# Proof map

The development contains 62 mathematical modules. The table follows the proof
from finite sign averages to the final spectral limit. Start with the
[paper](../paper/marchenko-pastur.pdf) for the mathematical argument, or with
[MarchenkoPastur.lean](../RandomMatrix/MarchenkoPastur.lean) for its exact Lean statement.

| Module | Mathematical content |
| --- | --- |
| [FiniteAverage](../RandomMatrix/FiniteAverage.lean) | Uniform expectation and independent-coordinate factorization |
| [Rademacher](../RandomMatrix/Rademacher.lean) | All-order monomial parity cancellation and rectangle moments |
| [WordMoments](../RandomMatrix/WordMoments.lean) | Arbitrary coordinate-word moments and mixed moments by multiplicity parity |
| [Covariance](../RandomMatrix/Covariance.lean) | Trace expansion, exact first moment, exact expected second moment |
| [Geometry](../RandomMatrix/Geometry.lean) | Positive semidefiniteness, rank at most n, nullity at least p-n |
| [SecondMomentLimit](../RandomMatrix/SecondMomentLimit.lean) | Exact second-moment bias and convergence of its expectation |
| [Walks](../RandomMatrix/Walks.lean) | Deterministic expansion at every order; exact expected moments as counts of even closed walks |
| [WalkBounds](../RandomMatrix/WalkBounds.lean) | r+c <= k+1 for even walks; every used entry occurs twice at equality |
| [Labelings](../RandomMatrix/Labelings.lean) | Equality-pattern fibers are injective block labelings; exact falling-factorial multiplicities |
| [WalkPositions](../RandomMatrix/WalkPositions.lean) | Bijection between rooted walks and position-indexed row/column assignments |
| [WalkPatterns](../RandomMatrix/WalkPatterns.lean) | Closure and parity depend only on partitions; exact partition-weighted count |
| [PatternCoefficients](../RandomMatrix/PatternCoefficients.lean) | Dimension-independent coefficients and the exact finite moment expansion |
| [PatternBounds](../RandomMatrix/PatternBounds.lean) | Abstract pattern vertex bound and coefficient vanishing above r+c=k+1 |
| [PatternBoundary](../RandomMatrix/PatternBoundary.lean) | Exact zeroth-order coefficients and exclusion of empty row/column blocks |
| [PatternGraph](../RandomMatrix/PatternGraph.lean) | Connected bipartite graph on quotient blocks; exact vertex and edge counts |
| [PatternTrees](../RandomMatrix/PatternTrees.lean) | Leading patterns are precisely closed doubled trees, in both directions |
| [PatternContour](../RandomMatrix/PatternContour.lean) | Genuine graph walks preserving entry order, closure, length, and double occurrence |
| [TreeWalkSplit](../RandomMatrix/TreeWalkSplit.lean) | Bridge-based split into the first child excursion and remaining root excursions |
| [OrderedContours](../RandomMatrix/OrderedContours.lean) | Recursive ordered contours, unique shape, and reconstruction of doubled tree walks |
| [CanonicalContours](../RandomMatrix/CanonicalContours.lean) | Canonical distinct vertex labels and injective relabeling of every contour |
| [ContourPositions](../RandomMatrix/ContourPositions.lean) | Even/odd positions and the color-reversing row/column count recurrence |
| [ContourEdges](../RandomMatrix/ContourEdges.lean) | Contour closure and even edge multiplicities |
| [ContourLabelings](../RandomMatrix/ContourLabelings.lean) | Fin-indexed row/column label functions, block counts, and ordered entry word |
| [ContourPatterns](../RandomMatrix/ContourPatterns.lean) | Every ordered tree produces a surviving maximal original pattern |
| [ContourRoundTrip](../RandomMatrix/ContourRoundTrip.lean) | Recovering the original partitions and full contour through quotient labels |
| [LeadingTreeBijection](../RandomMatrix/LeadingTreeBijection.lean) | General bijection, both inverse identities, and preservation of both block counts |
| [TreeCoefficients](../RandomMatrix/TreeCoefficients.lean) | Fixed-order and refined equivalences; exact leading coefficient as a tree count |
| [TreeGeneratingSeries](../RandomMatrix/TreeGeneratingSeries.lean) | Finite tree-counting polynomials, two color series, and the quadratic equation |
| [TreePolynomialRecurrence](../RandomMatrix/TreePolynomialRecurrence.lean) | Formal differential identity and the three-term polynomial recurrence |
| [NarayanaArithmetic](../RandomMatrix/NarayanaArithmetic.lean) | Binomial expression satisfies the same recurrence, including support boundaries |
| [NarayanaTreeCount](../RandomMatrix/NarayanaTreeCount.lean) | Every tree-polynomial coefficient equals the Narayana expression |
| [NarayanaCoefficients](../RandomMatrix/NarayanaCoefficients.lean) | Closed formula for the original leading coefficients; exact division and Catalan total |
| [FallingFactorialBounds](../RandomMatrix/FallingFactorialBounds.lean) | Distinct-label fractions and explicit collision losses |
| [MomentPolynomials](../RandomMatrix/MomentPolynomials.lean) | Leading diagonal equals the Narayana moment polynomial, including order zero |
| [PatternBudget](../RandomMatrix/PatternBudget.lean) | Explicit dimension-independent upper bound on all coefficient counts |
| [LabelWeightBounds](../RandomMatrix/LabelWeightBounds.lean) | Leading collision errors and suppression of lower-order patterns |
| [ExpectedMomentBounds](../RandomMatrix/ExpectedMomentBounds.lean) | Uniform C_k(a,B)/n bound relative to the polynomial at p/n |
| [ExpectedMomentLimit](../RandomMatrix/ExpectedMomentLimit.lean) | Every fixed expected moment converges at a positive finite aspect-ratio limit |
| [FiniteVariance](../RandomMatrix/FiniteVariance.lean) | Exact finite covariance, variance, event probabilities, Chebyshev, and disjoint-word cancellation |
| [PairPatterns](../RandomMatrix/PairPatterns.lean) | Joint partition graph, shared-row connectedness, and the 2k+1 vertex bound |
| [PairCounting](../RandomMatrix/PairCounting.lean) | Paired walks are joint label assignments; exact falling-factorial pattern counts |
| [PairCountBounds](../RandomMatrix/PairCountBounds.lean) | Explicit partition budget and uniformly bounded normalized pair count |
| [WalkCovariance](../RandomMatrix/WalkCovariance.lean) | Exact trace-variance expansion and the overlapping-pair upper bound |
| [VarianceBounds](../RandomMatrix/VarianceBounds.lean) | Uniform O(1/n) variance bounds at fixed order |
| [MomentConcentration](../RandomMatrix/MomentConcentration.lean) | Quantitative tail bounds, vanishing mean-square error, and convergence in probability |
| [SpectralGeometry](../RandomMatrix/SpectralGeometry.lean) | Eigenvalues with multiplicities, trace powers, and zero multiplicity equal to nullity |
| [EmpiricalMeasure](../RandomMatrix/EmpiricalMeasure.lean) | Empirical probability measure, integral formula, nonnegative support, and forced zero atom |
| [SpectralConcentration](../RandomMatrix/SpectralConcentration.lean) | Expected moments, mean-square convergence, and concentration of empirical spectral moments |
| [MPParameters](../RandomMatrix/MPParameters.lean) | Explicit MP density, endpoints, atom, and angular parametrization |
| [MPPolynomialRecurrence](../RandomMatrix/MPPolynomialRecurrence.lean) | Real MP polynomial recurrence inherited from the tree count |
| [MPMomentRecurrence](../RandomMatrix/MPMomentRecurrence.lean) | Integration-by-parts recurrence and all angular moments |
| [MPTrigNormalization](../RandomMatrix/MPTrigNormalization.lean) | Arctangent evaluation of reciprocal trigonometric integrals |
| [MPAngularNormalization](../RandomMatrix/MPAngularNormalization.lean) | Continuous mass for every positive aspect ratio, including one |
| [MPDensityIntegrals](../RandomMatrix/MPDensityIntegrals.lean) | Lebesgue substitution, integrability, normalization, and all positive density moments |
| [MPMeasure](../RandomMatrix/MPMeasure.lean) | Explicit probability measure, exact atom, all moments, and compact support |
| [MPIdentification](../RandomMatrix/MPIdentification.lean) | Empirical moment concentration toward the moments of the explicit MP law |
| [FiniteConvergence](../RandomMatrix/FiniteConvergence.lean) | Convergence in probability under finite linear combinations on separate finite spaces |
| [PolynomialSandwich](../RandomMatrix/PolynomialSandwich.lean) | Global polynomial bounds with arbitrarily small gap on the target support |
| [PolynomialIntegrals](../RandomMatrix/PolynomialIntegrals.lean) | Integrability and moment expansion of polynomials, and convergence of their integrals |
| [CompactMomentMethod](../RandomMatrix/CompactMomentMethod.lean) | Weak convergence from moments and compact moment determinacy |
| [SpectralTightness](../RandomMatrix/SpectralTightness.lean) | Uniform deterministic spectral tail bound and tightness |
| [MarchenkoPastur](../RandomMatrix/MarchenkoPastur.lean) | The complete independent fair-sign Marchenko-Pastur theorem |

## Detailed guides

1. [Trace walks](WALKS.md) and [equality patterns](PATTERNS.md).
2. [Doubled trees](TREES.md), [ordered contours](ORDERED_TREES.md), and [Narayana enumeration](NARAYANA.md).
3. [Expected moments](EXPECTED_MOMENTS.md) and [concentration](CONCENTRATION.md).
4. [Empirical spectral measures](SPECTRAL_MEASURES.md).
5. [Density normalization and moments](MP_DENSITY.md).
6. [Weak convergence and moment determinacy](WEAK_CONVERGENCE.md).
