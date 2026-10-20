# Variance and concentration of every fixed trace moment

For the actual p-by-n independent fair-sign ensemble, with
M_k = trace((X X^T/n)^k)/p, Lean now proves

    E[(M_k(p_m,n_m) - P_k(gamma))^2] -> 0,
    Pr(|M_k(p_m,n_m) - P_k(gamma)| > epsilon) -> 0

for every fixed natural k and epsilon>0, provided both dimensions are positive,
n_m tends to infinity, and p_m/n_m tends to gamma>0. Here P_k is the Narayana
moment polynomial defined in [EXPECTED_MOMENTS.md](EXPECTED_MOMENTS.md).

The exported theorems are `moment_mean_square_tendsto` and
`moment_converges_in_probability`. They cover the separate uniform finite
ensemble at each size; no coupling across different sizes is assumed.

## Explicit finite-size bounds

For p,n>0, a>0, B>=1 and a<=p/n<=B, define

    Q_k = [2(k+1)]^[2(k+1)] (2k)^(2k),
    V_k(a,B) = Q_k B^(2k) / a.

Natural-number powers use 0^0=1. The two variance bounds are

    Var(M_k) <= Q_k B^(2k)/p,
    Var(M_k) <= V_k(a,B)/n.

They are `moment_variance_le_rows` and `moment_variance_bound`. The first only
needs the upper ratio bound. These constants are deliberately conservative;
they prove a vanishing bound at fixed k, not a sharp finite-sample estimate.

Combining this with the preceding bias bound C_k(a,B)/n gives the finite
probability estimate `moment_deviation_bound`:

    Pr(|M_k - P_k(p/n)| > epsilon)
      <= [V_k(a,B)/n + (C_k(a,B)/n)^2] / epsilon^2.

This comparison uses the current aspect ratio. The convergence theorem at
gamma additionally uses p/n -> gamma, without assuming a rate for that limit.

## Proof chain

1. `FiniteVariance` defines covariance, variance and finite event probability
   directly from the existing uniform average. `finiteProbability_eq_card`
   identifies event probability with the exact event cardinality divided by
   the cardinality of the sample space. Nonnegativity, the upper bound one,
   Chebyshev's inequality and the variance-plus-squared-bias identity are proved.
2. For two sign-entry words, `word_covariance_eq` computes covariance exactly:
   it is one if their combined counts are even and they are not both
   individually even; it is zero otherwise. `word_covariance_disjoint` proves
   exact cancellation for words sharing no matrix entry.
3. `WalkCovariance` expands the variance of the actual normalized trace into
   the sum of covariances of closed-walk monomials. A nonzero term requires
   overlapping words with even combined multiplicities. The bound enlarges
   this collection to all jointly even walk pairs sharing a row. It deliberately
   drops closure and does not require a shared column in this upper-bound set.
4. `PairPatterns` represents the two walks by 2(k+1) row positions and 2k
   column positions. A shared row connects their two position walks in the
   quotient-block graph. The combined word has length 4k; even multiplicities
   imply at most 2k distinct edges. Connectedness then gives at most 2k+1
   vertices. The argument covers order zero as well.
5. `PairCounting` gives an actual equivalence between paired rooted walks and
   joint position-label assignments. Regrouping by their row and column
   kernels gives exact multiplicities (p)_r(n)_c for each surviving partition
   pair. `PairCountBounds` bounds the number of all joint partition pairs by
   Q_k, using canonical representative functions. For r+c<=2k+1, each weight
   divided by p n^(2k) is at most B^(2k).
6. The variance denominator is p^2 n^(2k), so one factor 1/p remains. With
   a<=p/n this is at most 1/(an). `VarianceBounds` records the explicit bounds.
7. `MomentConcentration` combines the variance limit with the already proved
   expected-moment limit. The exact mean-square decomposition gives vanishing
   error to P_k(gamma); finite Chebyshev then gives convergence in probability.

No variance estimate or concentration conclusion is assumed in this chain.
The argument proves an O(1/n) upper bound, with no claim that this rate is sharp.

## Independent checks

`python3 experiments/variance.py` uses exact integer and rational arithmetic:

- Enumerates 4,774 sign matrices over eight dimension pairs and checks 40
  variances at orders 0 through 4. Zeroth and first moments have zero variance.
  The computed second-moment variance agrees with
  4(p-1)(n-1)/(p n^3); this closed formula is a computational check, not a
  separately exported Lean theorem.
- Compares 32 paired-walk counts with independently enumerated joint partitions
  at orders 0 through 3. The exact covariance count divided by p^2 n^(2k)
  also agrees with the directly computed variance.
- Examines 797,438 joint partition candidates sharing a row. Surviving patterns
  pass an independent graph traversal for connectedness and the vertex bound.
- Checks 160 exact deviation probabilities against both Chebyshev's actual
  mean-square bound and the conservative formal bound, including strict
  inequalities where Chebyshev is not an equality.

A fourth Lean negative control rejects the claim that a fair sign has zero
variance; the formal variance is one. All new exported theorems and the joint
labeling equivalence are included in the dependency audit.

These computations supplement the all-order proof. The Python enumerator is
not itself formally verified. See [VALIDATION.md](VALIDATION.md) for the saved
build, audit and experiment records.

## Next session

The next stage is the spectral interface: define the empirical probability
measure from the Hermitian eigenvalues, prove its moments equal normalized
traces, transfer positive semidefiniteness to nonnegative support, and translate
the existing nullity bound into the forced zero-eigenvalue mass for p>n.

The MP density and atom still need normalization and moment proofs. Tightness,
moment determinacy, and weak convergence in probability of the empirical
spectral measures also remain. Random-moment convergence alone does not finish
the full Marchenko-Pastur theorem; see [BLUEPRINT.md](BLUEPRINT.md).
