# Marchenko-Pastur for independent fair signs

## Precise flagship target

Let p_m and n_m be positive integers with n_m tending to infinity and
p_m/n_m tending to gamma in (0, infinity). For each m, let X_m be uniform on
all p_m-by-n_m matrices with entries in {-1,+1}. Define

    S_m = X_m X_m^T / n_m,
    mu_m = (1/p_m) sum_i delta_(lambda_i(S_m)).

Prove weak convergence in probability of mu_m to the Marchenko-Pastur measure

    mu_gamma = max(1 - 1/gamma, 0) delta_0 + rho_gamma(x) dx,
    rho_gamma(x) = sqrt((b-x)(x-a)) / (2 pi gamma x),  a < x < b,
    a = (1-sqrt(gamma))^2,  b = (1+sqrt(gamma))^2,

with density zero elsewhere. For every bounded continuous f : R -> R and every
epsilon > 0, the uniform probability of

    |integral f d mu_m - integral f d mu_gamma| > epsilon

tends to zero. There is no assumption about joint dependence across different m;
convergence in probability here uses each finite ensemble separately.

This is a planned theorem. The current Lean modules do not prove this limit.
It is a classical theorem, not a new mathematical claim or a claim of first
formalization. Beginning with signs is a substantive special case, not a proof
for all independent-entry distributions.

## Dependency graph and acceptance criteria

1. Finite probability and sign moments. Define uniform expectation over the
   actual finite cube. Prove factorization and parity cancellation for every
   coordinate exponent. No external random-number generator enters these proofs.
2. Finite covariance algebra. Define S and normalized trace moments, prove
   positivity and trace formulas, and evaluate the first two moments exactly.
3. All-order alternating-walk formula. Expand tr((XX^T)^k), group by partitions
   of row and column positions, and prove that precisely the even-edge patterns
   survive. This stage is complete for every k, including zero: the labeled
   expansion, partition grouping, falling-factorial label multiplicities, and
   dimension-independent coefficient formula are proved in Lean. The Python
   enumerator supplies independent finite checks.
4. Leading patterns. Prove r+c <= k+1 for surviving connected patterns. Identify
   equality with doubled bipartite trees and count them by Narayana numbers.
   The bound is now proved for all even walks and all surviving abstract
   patterns. Coefficients with r+c>k+1 vanish. The graph on quotient blocks is
   now proved connected and bipartite, with exact vertex and edge counts.
   A pattern is surviving and maximal exactly when it is closed, its graph is
   a tree, and every used entry occurs twice. A genuine graph walk retains
   the entry order and distinguished root. The rooted ordered tree bijection,
   both inverses, preservation of both color counts, and equality of the
   original leading coefficients with refined tree counts are now proved
   for every order. The Narayana formula and exact divisibility are now proved,
   completing this counting stage. The total leading-pattern count is Catalan.
5. Expected moments. Prove convergence for every fixed k to

       sum_(r=1)^k (1/k) choose(k,r) choose(k,r-1) gamma^(r-1).

   Produce explicit finite-size remainder bounds for fixed k. Keep constants
   and the assumption that gamma stays away from zero visible.
6. Fluctuations. Expand the covariance of two trace moments. Disjoint-coordinate
   terms cancel, and the remaining overlap patterns yield a variance bound
   tending to zero. Expectation convergence alone is insufficient.
7. Spectral interface. Use Hermitian eigenvalues to define the empirical
   probability measure and connect its moments to normalized matrix traces.
   Prove support is nonnegative; address the forced nullspace for p > n.
8. Identify the target measure. Prove positivity, total mass, and the moment
   formula for the displayed density plus atom. Do not assume normalization.
9. Moment-to-measure convergence. Prove tightness, moment determinacy and the
   relevant convergence-in-probability argument. This is the main analytic
   bottleneck. A theorem assuming spectral convergence would not close it.

## Finite identities used as normalization checks

For every p,n > 0 and every sign matrix, the first normalized trace moment is 1.
The exact ensemble second moment is

    E[(1/p) tr(S^2)] = 1 + (p-1)/n = 1 + p/n - 1/n.

Thus the limiting second moment is 1+gamma, with finite bias exactly -1/n.
A further exact-computation target, not yet a Lean theorem, is

    E[(1/p) tr(S^3)] = 1 + 3(p-1)/n + (p-1)(p-2)/n^2.

When p > n the matrix has at least p-n zero eigenvalues. Simulations must keep
those zeros in the empirical measure, rather than renormalizing the nonzero
spectrum to total mass one. All finite moments in the project use 1/p for the
trace normalization and 1/n for the covariance normalization.

## Working order

Stages 1 through 4 are complete, including the general Narayana count linked
to the original finite moment coefficients. Next, prove convergence of all
fixed expected moments and finite-size remainder bounds. The finite coefficient
expansion and its exact leading diagonal are available for this step. No
concentration or spectral-measure convergence follows from counting alone.
The complete flagship chain is substantial; no completion date is inferred from
the first finite proofs.

See [WALKS.md](WALKS.md), [PATTERNS.md](PATTERNS.md), [TREES.md](TREES.md),
[ORDERED_TREES.md](ORDERED_TREES.md), and [NARAYANA.md](NARAYANA.md) for the completed
statements and their boundary with the remaining combinatorics.

## References

- Fleermann and Kirsch, *Proof Methods in Random Matrix Theory* (2022):
  https://arxiv.org/abs/2203.02551. Pedagogical reference for the moment-method route.
- The original Marchenko-Pastur theorem (1967) supplies the mathematical target;
  this project uses the unit-variance sample-covariance convention above.
- See PRIOR_ART.md for the pinned Lean sources inspected before implementation.
