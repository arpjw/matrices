# Empirical spectral measures

## Completed statement

For every real p-by-n matrix X with p,n positive, let S=XX^T/n. The project now
constructs the actual empirical eigenvalue probability measure

    mu_X = (1/p) sum_(i=1)^p delta_(lambda_i(S)).

The list contains every eigenvalue with its multiplicity, including zero.
For every natural k, including k=0, Lean proves

    integral x^k d mu_X = trace(S^k)/p.

Consequently the existing fixed-moment mean-square and convergence-in-probability
results now apply directly to moments of these empirical probability measures.
The limiting values are the Narayana polynomials P_k(gamma). The subsequent
[MP density stage](MP_DENSITY.md) now identifies them with moments of the
explicitly normalized Marchenko-Pastur density and atom.

## Eigenvalues and trace powers

`SpectralGeometry.lean` uses the pinned mathlib Hermitian spectral theorem.
`covarianceEigenvalues X` is the eigenvalue list supplied by the covariance's
positive-semidefinite proof, indexed by Fin p. It is not a set of distinct values.

- `covariance_eigenvalues_nonneg` proves every entry is nonnegative.
- `covariance_trace_pow` diagonalizes S by a unitary matrix, carries powers
  through the algebra equivalence, and uses cyclic invariance of trace.
  This proves the identity for all k with the same eigenvalue list, including
  the identity matrix at k=0.
- `covariance_rank_eq_nonzero_count` identifies rank with the number of nonzero
  eigenvalues. Rank-nullity then gives `covariance_zero_count_eq_nullity`.
- `covariance_zero_count_ge` transfers the existing nullity lower bound p-n
  to the eigenvalue list.

## Measure construction and the zero atom

`EmpiricalMeasure.lean` defines a finite sum of Dirac measures scaled by
`ENNReal.ofReal ((p : Real)^(-1))`. `empiricalMeasure_isProbabilityMeasure`
requires p>0; `empiricalProbabilityMeasure` bundles that proof in mathlib's
`ProbabilityMeasure Real`, which already carries the topology of weak convergence.
The general algebraic identities also make sense in zero dimensions; the
zero-row construction is the zero measure, not a probability measure. All
random-matrix limit results retain the positive-dimension hypotheses.

`empiricalMeasure_apply` counts eigenvalue indices in a measurable set and
multiplies by 1/p. Every real-valued function is integrable for this finite
atomic measure. `empiricalMeasure_integral` evaluates its integral as the full
list average, and `empiricalMeasure_moment` gives the trace-moment bridge.
`empiricalMeasure_moment_zero` records unit mass explicitly.

The negative half-line has measure zero, almost every point is nonnegative,
and the topological support is contained in [0,infinity). These are separate
exported conclusions, ending with `empiricalMeasure_support_nonneg`.

The zero atom is identified exactly:

    mu_X({0}) = nullity(S)/p.

Its real-valued mass satisfies

    mu_X({0}) >= (p-n)_+/p = max(1 - n/p, 0)
                               = max(1 - 1/(p/n), 0).

Here `(p-n)_+` is natural-number subtraction. The aspect-ratio form requires
both positive dimensions. This is a lower bound: additional rank deficiency
can make the finite zero atom larger. No equality with the limiting MP atom
or convergence of finite zero-atom masses is asserted.

## Concentration of actual spectral moments

`SpectralConcentration.lean` transfers the established trace results through
the exact integral identity. Its main theorem is
`empirical_moment_converges_in_probability`, stated using the bundled empirical
probability measures. For n_m tending to infinity and p_m/n_m tending to
gamma>0, for every fixed k and epsilon>0,

    Pr(|integral x^k d mu_(X_m) - P_k(gamma)| > epsilon) -> 0.

The probability remains the exact uniform fraction of sign assignments in
each finite ensemble. No coupling across sizes is required.

The module also exports convergence of expected spectral moments, mean-square
convergence, and the quantitative finite deviation bound at the current ratio.
`empiricalMeasure_sign_first_moment` proves integral x d mu_X=1 for every sign
matrix with positive dimensions.

This does not yet prove weak convergence against all bounded continuous test
functions. It supplies the concrete measure and exact bridge that such an
argument needs.

## Validation

All 25 new exported theorems are included in the dependency audit. Two new
negative controls reject zero total spectral mass and an absent zero atom for
a two-by-one covariance matrix. The latter uses the proved lower bound 1/2.

`experiments/spectral_interface.py` uses only exact integer and rational
arithmetic. It checks every sign matrix with 1<=p,n<=5 and min(p,n)<=2:
2,826 matrices in 16 dimension pairs. Their spectra are obtained from a one-
or two-dimensional Gram matrix, retaining every structural zero. Four further
matrices include a zero matrix, distinct diagonal values, a rank-one matrix,
and repeated positive eigenvalues.

For each matrix it checks the candidate characteristic polynomial at p+1
distinct points using exact determinant elimination. Equality at those points
certifies equality of the degree-p polynomials. An independent row elimination
checks rank and zero multiplicity. Direct matrix powers check moments 0 through
6, totaling 19,810 comparisons. In total, 12,215 polynomial evaluations and
2,830 rank/atom checks pass. Three regression controls detect dropped zeros,
renormalization over only positive values, and discarded multiplicities.
These finite computations supplement the general Lean proof; the Python code
itself has not been formally verified. See [VALIDATION.md](VALIDATION.md).

## Analytic handoff

The explicit MP density plus atom is now normalized and its moments identified
at every order, including the critical aspect ratio gamma=1. See
[MP_DENSITY.md](MP_DENSITY.md) for the completed proof.

Tightness, moment determinacy, and the passage from moment concentration to
weak convergence in probability remain. See [BLUEPRINT.md](BLUEPRINT.md).
