# The general Narayana coefficient formula

The leading moment coefficients are now evaluated in Lean:

    A_(k,r,k+1-r) = choose(k,r) choose(k,r-1) / k,   1 <= r <= k.

The theorem is `leadingCoefficient_narayana`. It concerns the original
`patternCoefficient` defined by surviving row and column equality partitions,
so it is connected to the exact finite sign-matrix moment expansion.
The division is exact. `mul_patternCoefficient_narayana` proves the stronger
integer identity

    k A_(k,r,c) = choose(k,r) choose(k,r-1),
    whenever k>0, r>0, and r+c=k+1.

The rational version is `patternCoefficient_narayana_rat`. The zeroth-order
coefficient remains A_(0,1,0)=1, with all other order-zero coefficients zero.
No division by zero enters the positive-order theorem. The total number of
leading patterns at every order, including zero, is the Catalan number;
this is `leadingPatterns_card_catalan`.

## Counting the actual tree shapes

The preceding stage proved a bijection with rooted ordered trees, preserving
both color counts. Write R(t) and C(t) for those counts, with a row-colored root.
Define finite polynomials over the rationals by

    A_k(u) = sum_(t with k edges) u^R(t),
    B_k(u) = sum_(t with k edges) u^C(t).

`rowTreePoly` and `colTreePoly` sum over mathlib's exhaustive finite set
`treesOfNumNodesEq`. A coefficient therefore counts actual tree shapes, not a
sequence introduced by declaring a recurrence. `rowTreePoly_coeff_card`
proves this connection to the finite subtype cardinality.

The first-child decomposition changes the child's root color. It gives

    A_0=u, B_0=1,
    A_(k+1) = sum_(i+j=k) B_i A_j,
    B_(k+1) = sum_(i+j=k) A_i B_j.

These identities follow by splitting the finite tree set into disjoint pairs
of child and remaining-root trees.

## Formal generating functions

Let A(z)=sum A_k z^k and B(z)=sum B_k z^k, viewed as formal power series over
Q[u]. No analytic convergence or interchange of infinite limits is involved.
The two decompositions become

    A = u + z B A,
    B = 1 + z A B.

Subtracting proves A-B=u-1. In particular, positive-order row and column
polynomials are equal. Eliminating A gives

    B = 1 + z B (B+u-1).

`colTreeSeries_quadratic` proves this equation for the series constructed
from the finite tree sums. There is no assumption that its solution has
Narayana coefficients.

## A linear recurrence

Formal differentiation and polynomial algebra yield

    z [1-2(u+1)z+(u-1)^2 z^2] B'
      + [1-(u+1)z] B = 1+(u-1)z.

Extracting coefficients gives, for every n>=0,

    (n+3) B_(n+2) = (2n+3)(u+1) B_(n+1) - n(u-1)^2 B_n.

The initial polynomials are B_0=1, B_1=u, and B_2=u+u^2.
`TreePolynomialRecurrence.lean` proves the differential identity and recurrence.
All manipulations occur in the formal power-series and polynomial rings.

## Verifying the binomial expression

`narayanaQ` is the proposed rational coefficient expression, with explicit
zero-order and zero-index boundary cases. It is an arithmetic definition;
it is not used to redefine the tree count or the original moment coefficient.

`NarayanaArithmetic.lean` proves that this expression satisfies the same
three-term coefficient recurrence. The key binomial step is the signed identity

    choose(n,j+1) = choose(n,j) (n-j)/(j+1),

interpreted over the rationals. It remains valid when j lies beyond the
binomial support. The proof handles coefficient indices zero, one, and two
separately, then uses Pascal's identity and rational algebra for all larger
indices. Denominator nonvanishing is proved explicitly.

Strong induction identifies every coefficient of B_n with `narayanaQ`.
The positive-order equality A_n=B_n transfers this to row counts. Finally,
`patternCoefficient_cast_eq_rowTreePoly` returns to the original two-partition
coefficient: on the leading diagonal, the row count determines the column
count because every tree has k+1 vertices. Clearing the positive denominator
proves the natural-number identity and exact quotient formula.

## Verification and remaining scope

The five new modules are part of the aggregate build and dependency audit.
A negative control asks Lean to prove A_(3,2,2)=4 using the general theorem;
it is rejected because the actual coefficient is 3. The existing normalization
negative control is retained. See [VALIDATION.md](VALIDATION.md) for the full
build and independent enumeration records.

This completes the leading-pattern counting stage. Convergence of every fixed
expected moment and explicit finite-size bounds have now also been proved; see
[EXPECTED_MOMENTS.md](EXPECTED_MOMENTS.md). Variance estimates, the spectral-measure
interface, identification of the density plus zero atom, and weak convergence
in probability are still unproved. The full target remains in
[BLUEPRINT.md](BLUEPRINT.md).
