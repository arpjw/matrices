# Partition coefficients for every moment order

The project now proves the exact identities

    C_k(p,n) = sum_(r=0)^(k+1) sum_(c=0)^k A_(k,r,c) (p)_r (n)_c,
    E[M_k] = C_k(p,n) / (p n^k),                         p,n>0,
    A_(k,r,c) = 0 when r+c>k+1.

These hold at every natural order k, including zero. The coefficients are
natural numbers defined independently of the matrix dimensions. The finite
moment formula is `expected_moment_by_coefficients`; the support bound is
`patternCoefficient_eq_zero_of_large`.

## What is a pattern?

A walk has k+1 row positions and k column positions. Its row pattern records
which row positions receive the same label; its column pattern does the same
for column positions. Lean represents each pattern as an equivalence relation
(`Setoid`), so renaming block labels does not produce another pattern.

The row positions include both endpoints. Closure requires the final row to
be equivalent to the initial row. The entry-position word is

    (0,0), (1,0), (1,1), (2,1), ..., (k-1,k-1), (k,k-1).

`PatternSurvives` requires closure and even multiplicity for every pair of
row and column blocks. It expresses this directly by filtering the position
word with the two equivalence relations. Neither p nor n appears in the
definition. `patternCoefficient k r c` counts surviving pattern pairs with
exactly r row blocks and c column blocks.

At k=0, there is one row position and no column positions. The position word
is empty, and the endpoint closure condition is reflexive. The general
construction therefore includes the zeroth moment without a special-case
replacement of the moment theorem.
`patternCoefficient_zero` now proves that A_(0,1,0)=1 and all other
order-zero coefficients vanish. Empty row blocks are impossible at every
order, and empty column blocks are impossible at positive orders.

## Why the multiplicity is a falling factorial

For any finite position set and any equivalence relation s on it,
`kernelFiberEquiv` constructs a bijection between:

1. Functions to a label set whose equality pattern is exactly s.
2. Injective maps from the blocks of s into that label set.

The forward direction descends a function to the quotient by s. Equality of
its kernel with s proves that the descended function is injective. The inverse
composes an injection with the quotient map. Both inverse identities are proved.

Mathlib's embedding-cardinality theorem then gives `(p)_r` labelings for r
row blocks and `(n)_c` labelings for c column blocks. These factors are zero
when too few distinct labels are available. Using ordinary powers p^r and n^c
would incorrectly allow different blocks to merge.

## Connection to the matrix theorem

`walkLabelsEquiv` proves that the existing rooted-walk type is equivalent to
the pair of row-position and column-position assignment functions. The source
and target words agree under this equivalence, as do the initial and final rows.

`even_map_iff_fibers` proves that multiplicity parity depends only on equality
of labels. This yields `isEvenClosedWalk_iff_pattern`, connecting the original
sign-expectation survival condition to the abstract pattern condition.

The finite sums are then regrouped first by equality patterns and then by
their block counts. No pattern counts are inserted from Python, and no
asymptotic statement is assumed. The complete chain ends at the original
uniform expectation of the normalized covariance trace.

## Why higher-degree coefficients vanish

Every equivalence relation can be realized by choosing one representative
position from each block. Applying this to a surviving pattern constructs an
actual finite labeled walk. The proofs identify the numbers of quotient blocks
with the cardinalities of its visited row and column sets.

The earlier all-order walk bound therefore gives r+c<=k+1 for every surviving
pattern. If r+c>k+1, the subtype counted by A_(k,r,c) is empty. This proves
coefficient vanishing independently of the matrix dimensions.

## Verification and the remaining bottleneck

The independent Python checks compare the k+1-row position representation
with the earlier cyclic representation at orders 0 through 7. Exhaustive
function enumeration checks 120 labeling fibers over 499 assignments, including
empty domains and insufficient labels. The matrix and labeled-walk checks remain
in place. The Python representation uses first-occurrence block numbers;
Lean uses equivalence relations. The Python implementation itself is not verified.

The graph on quotient blocks is now proved connected and bipartite. Leading
patterns are characterized in both directions as closed doubled trees, with
the original visit order preserved by an actual graph walk. See
[TREES.md](TREES.md) for this completed structural stage.

The general bijection with rooted ordered trees is now proved, preserving
both block counts. `patternCoefficient_eq_treeCount` identifies the original
coefficients on r+c=k+1 with the corresponding refined tree counts. See
[ORDERED_TREES.md](ORDERED_TREES.md). The Narayana formula now evaluates those
counts for every order; [NARAYANA.md](NARAYANA.md) gives the proof. These finite
results do not by themselves prove
expected-moment limits or concentration.
The full Marchenko-Pastur convergence theorem remains unfinished.
