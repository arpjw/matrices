# Marchenko-Pastur weak convergence in probability

## Completed flagship theorem

Let p_m and n_m be positive natural numbers, with n_m tending to infinity and
p_m/n_m tending to a real gamma>0. At each size, sample every entry of the
p_m-by-n_m matrix X_m independently and uniformly from {-1,+1}. Define

    S_m = X_m X_m^T / n_m,
    mu_m = (1/p_m) sum_i delta_(lambda_i(S_m)).

For every bounded continuous real function f and every epsilon>0, Lean proves

    Pr(|integral f d mu_m - integral f d mu_gamma| > epsilon) -> 0,

where mu_gamma is the explicit probability measure

    max(1-1/gamma,0) delta_0 + rho_gamma(x) dx,
    rho_gamma(x) = sqrt((b-x)(x-a)) / (2*pi*gamma*x) for a<x<b,
    a = (1-sqrt(gamma))^2,       b = (1+sqrt(gamma))^2,

and the density is zero elsewhere. All p_m eigenvalues are retained, with
multiplicities and zeros. The theorem includes gamma=1 and gamma>1.

The main declaration is `RandomMatrix.marchenkoPastur_theorem` in
[MarchenkoPastur.lean](../RandomMatrix/MarchenkoPastur.lean). Its test function
is an ordinary `f : Real -> Real` with `Continuous f` and an explicit global
bound. `empirical_weak_converges_to_mp` states the same result with mathlib's
bundled bounded continuous functions and probability measures.

Probability is the exact uniform fraction of sign assignments at each size.
The sample spaces can differ with m; the theorem does not require a coupling
or a joint distribution across sizes. This completes the flagship target in
[BLUEPRINT.md](BLUEPRINT.md).

## Uniform tightness

The empirical measure is nonnegative and its first moment is exactly one for
every sign matrix. Markov's inequality therefore gives the deterministic bound

    mu_X([0,R]^c) <= 1/R,       R>0.

`empirical_sign_tail_bound` proves this for every positive pair of dimensions
and every sign assignment. `empirical_sign_uniform_tightness` chooses the
single compact interval [0,1/epsilon] for all of them. Tightness holds for the
entire family, without an exceptional event or an asymptotic restriction.

## Polynomial bounds on the whole half-line

Uniform approximation on a compact interval alone does not control the
integral of the approximating polynomial outside that interval. The new proof
addresses those tails explicitly.

Fix a bounded continuous f, a support bound B>=0, and epsilon>0. Set R=B+1.
Weierstrass approximation gives a polynomial p approximating f(R*t) within
epsilon/4 on [0,1]. Put

    C = norm(f) + sum_i |coeff_i(p)|.

For t>=1 and N>=degree(p), direct coefficient bounds give

    |p(t)| <= (sum_i |coeff_i(p)|) t^N.

Since B/R<1, choose N>=degree(p) with C(B/R)^N<epsilon/4. Define

    q(x) = p(x/R),
    e(x) = epsilon/4 + C(x/R)^N,
    l(x) = q(x)-e(x),       u(x) = q(x)+e(x).

For every x>=0, l(x)<=f(x)<=u(x). On [0,B], u(x)-l(x)<=epsilon.
The local approximation handles x<=R; the coefficient bound and the high power
handle x>R. These are polynomial bounds everywhere on the nonnegative
half-line, so no unproved truncation or exchange of limits is needed.

`exists_polynomial_sandwich` proves this construction. The approximation order
can depend on f and epsilon, but is fixed before taking the matrix-size limit.

## From moments to bounded continuous tests

`FiniteConvergesInProbability` permits a different finite sample space at every
index. The finite union bound proves closure under addition and scalar
multiplication, and then under any fixed finite sum. Since a polynomial
integral is a finite linear combination of natural moments, all-order moment
convergence implies convergence in probability of every polynomial integral.

Apply the polynomial bounds with gap epsilon/2 on the target support. Their
integrals bound the test integral for every empirical measure and the target
measure. If the test-integral error exceeds epsilon, at least one of the two
polynomial-integral errors exceeds epsilon/2. Thus

    Pr(test error > epsilon)
      <= Pr(lower polynomial error > epsilon/2)
         + Pr(upper polynomial error > epsilon/2) -> 0.

`compact_moment_method` proves this for any sequence of random nonnegative
probability measures on separate finite spaces, provided all moments are
integrable and converge in probability to those of a compactly supported law.
The final MP theorem supplies each hypothesis from the earlier matrix,
concentration, spectral, and density modules.

## Moment determinacy

The same polynomial bounds also prove `compact_moments_determine`: a
compactly supported nonnegative probability measure is uniquely determined by
its natural moments among nonnegative probability measures with all moments
integrable. The competing measure need not have compact support.

Equal moments imply equal polynomial integrals. The upper and lower bounds
then force equal integrals of every bounded continuous function. Mathlib's
measure extensionality theorem gives equality of the measures.
`marchenkoPastur_moment_determinate` specializes this to the MP/Narayana moments.

## Modules and validation

| Module | Role |
| --- | --- |
| FiniteConvergence | Event monotonicity, union bound, and convergence under finite linear combinations |
| PolynomialSandwich | Polynomial growth bound and global upper/lower approximation |
| PolynomialIntegrals | Integrability, exact moment expansion, and convergence of polynomial integrals |
| CompactMomentMethod | Passage to bounded continuous tests and compact moment determinacy |
| SpectralTightness | Uniform deterministic spectral tail bound and compact tightness |
| MarchenkoPastur | Complete theorem for the actual independent fair-sign matrix ensemble |

The 21 new exported named theorems and the finite-convergence definition are
included in the dependency audit. Two additional negative controls reject
inference from the first moment alone and omission of the zero atom in a weak
limit. In the first, delta_1 and (delta_0+delta_2)/2 have the same first moment
but different integrals of the bounded continuous clipped identity. In the
second, the constant-one test detects the missing mass of the density at gamma=2.
Both fail only on the intended false mathematical conclusion.

See [VALIDATION.md](VALIDATION.md) for the full build and audit receipts.
The weak-convergence result is a general Lean proof, rather than a numerical
convergence experiment. The earlier exact enumerations and numerical density
checks remain supplementary evidence with their recorded scopes.

## Scope

The original independent fair-sign, positive finite aspect-ratio,
weak-convergence-in-probability target is complete. This formalizes a classical
theorem; no novelty or first-formalization claim is established. General entry
distributions, almost-sure convergence, sharp spectral-edge limits, and
convergence of the mass of individual atoms are outside this theorem's scope.
