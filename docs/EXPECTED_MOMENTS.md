# All fixed-order expected moments

For the actual uniform p-by-n independent-sign ensemble, write

    M_k = trace((X X^T / n)^k) / p,
    P_0(x) = 1,
    P_k(x) = sum_(r=1)^k choose(k,r) choose(k,r-1) x^(r-1) / k,  k > 0.

For positive integer sequences p_m,n_m, if n_m tends to infinity and
p_m/n_m tends to gamma > 0, Lean now proves

    E[M_k(p_m,n_m)] -> P_k(gamma)

for every fixed natural k. The theorem is `expected_moment_tendsto`.
The expectation is the finite average over all sign assignments, not an
abstract quantity postulated to have the desired expansion.

## Explicit finite-size bound

Let p,n > 0, a > 0, B >= 1 and a <= p/n <= B. Define

    H_k = (k+2)(k+1)(k+1)^(k+1) k^k,
    C_k(a,B) = H_k B^k ((k+1)^2 (1/a + 1) + 1).

As usual for natural-number powers, 0^0=1 in H_0. The constant is deliberately
conservative; it is not intended to predict useful sample sizes.
`expected_moment_error_bound` proves

    |E[M_k(p,n)] - P_k(p/n)| <= C_k(a,B)/n.

The comparison is with the polynomial at the current ratio. Without a rate
for p/n -> gamma, this does not give an O(1/n) rate to P_k(gamma). For example,
with n=m^2, p=m^2+m and k=2, the latter error is 1/m-1/m^2, whereas the bias
relative to P_2(p/n) is exactly -1/n. The exact checker records this distinction.

The intermediate theorem `expected_moment_error_dimensions` only needs
p/n <= B and B >= 1. Its bound is

    H_k B^k ((k+1)^2 (1/p + 1/n) + 1/n).

This also exposes the separate row and column contributions before a lower
bound on the aspect ratio is imposed.

## Proof chain

1. `FallingFactorialBounds` controls the fraction of assignments with distinct
   labels: D(p,r)=(p)_r/p^r lies in [0,1] for p>0, and
   1-D(p,r) <= r^2/p. The proof includes r>p, where the falling factorial
   vanishes. Combining row and column labels gives
   1-D(p,r)D(n,c) <= r^2/p+c^2/n.
2. `MomentPolynomials` defines the leading diagonal of the original coefficient
   expansion and proves it equals P_k. This uses the general Narayana formula,
   the vanishing zero-row and positive-order zero-column coefficients, and a
   separate order-zero case. It also checks P_1=1 and P_2=1+x.
3. `PatternBudget` injects partitions of an m-element set into its m^m label
   functions using canonical representatives. Bounding each surviving-pattern
   subtype and summing over all coefficient slots gives sum_(r,c) A_(k,r,c)
   <= H_k. This avoids any dimension-dependent constant.
4. `LabelWeightBounds` factors each normalized falling-factorial term into
   its power weight and the two distinct-label fractions. For a surviving
   pattern, let d=k+1-r-c >= 0. Its power weight is
   (p/n)^(r-1) n^(-d). If d=0, the error is the collision loss. If d>0,
   the whole term has an extra 1/n factor. Both are bounded uniformly by
   B^k ((k+1)^2(1/p+1/n)+1/n).
5. `ExpectedMomentBounds` multiplies by the nonnegative pattern coefficients,
   applies the triangle inequality to the exact finite sum, and uses H_k.
   From a <= p/n one gets 1/p <= 1/(an), giving the displayed constant.
6. `ExpectedMomentLimit` places the ratio eventually in
   [gamma/2, max(1,gamma+1)]. The bound tends to zero as n tends to infinity;
   continuity of P_k supplies convergence at gamma. No convergence rate for
   p/n, separate hypothesis that p tends to infinity, or coupling across
   different matrix sizes is needed.

## Validation and scope

All six modules are included in the aggregate build. Every new exported
theorem is included in the proof-dependency audit. A third negative control
asks Lean to discard the finite second-moment bias at p=n=1 and is rejected
with the intended false mathematical goal.

The exact checker compares the bound with 40 moments at orders 0 through 4
over eight dimension pairs, using the exhaustive sign-matrix calculations
for positive orders and the identity zeroth moment. It adds 56 checks at
orders 0 through 7 from independent partition enumeration, including too few
labels, rectangular dimensions in both orientations, and square dimensions.
These finite checks supplement the general Lean proof; the Python code is
not formally verified. See [VALIDATION.md](VALIDATION.md) for the recorded run.

This completes the expected-moment stage. The subsequent stage now also proves
explicit variance bounds, vanishing mean-square error, and convergence in
probability of each fixed random moment; see [CONCENTRATION.md](CONCENTRATION.md).
The spectral-measure interface, identification of the MP density plus atom,
and weak convergence of the empirical spectral measures remain in
[BLUEPRINT.md](BLUEPRINT.md).
