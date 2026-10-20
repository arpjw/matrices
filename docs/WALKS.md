# All-order walk counting

The results in this document are proved in `RandomMatrix/Walks.lean` and
`RandomMatrix/WalkBounds.lean`. They apply at arbitrary natural moment order.

## The exact formula

For a p-by-n matrix of independent uniform signs, write S=XX^T/n and
M_k=tr(S^k)/p. For p,n>0, the theorem `expected_moment_eq_walk_count` proves

    E[M_k] = C_k(p,n) / (p n^k).

C_k is the cardinality of a finite subtype, not an assumed coefficient or an
external program's answer. An element consists of an initial row i_0 and k
transitions (i_1,a_1), ..., (i_k,a_k), with two conditions:

1. The walk closes: i_k=i_0.
2. Every pair (row,column) appears an even number of times in the word

       (i_0,a_1), (i_1,a_1), (i_1,a_2), (i_2,a_2), ...,
       (i_(k-1),a_k), (i_k,a_k).

The order and starting row are retained. These are rooted, labeled walks;
there is no division by rotations or by a graph's automorphisms.

At order zero, the word is empty and the endpoint is the initial row. There
are exactly p such walks, formally proved by `evenClosedWalkCount_zero`.
Thus the formula has the correct zeroth-moment normalization.

## Proof chain

`WalkSteps p n k` is a nested finite product. Each transition records one next
row and one column. This avoids cyclic-index arithmetic at k=0 while retaining
the ordinary row-column-row interpretation.

`gram_pow_walks` proves the entrywise expansion of (XX^T)^k for every real X
by induction on k. The endpoint indicator selects precisely the walks ending
at the requested matrix index. `trace_covariance_pow_walks` sums diagonal
entries and extracts the factor n^(-k).

`average_word` supplies exact parity cancellation on the finite sign cube.
Applying it to every closed word gives `average_trace_pow_walks`. Dividing
the trace by p yields `expected_moment_eq_walk_count`.

All of this uses the original uniform average over all 2^(pn) sign assignments.
There is no assumed independence formula, unverified enumeration result, or
limiting argument in the walk-count theorem.

## The vertex bound

Let r and c be the numbers of distinct rows and columns visited by a walk,
and let e be the number of distinct matrix-entry coordinates in its word.
The starting row counts as visited, including at order zero.

`walk_vertices_le_edges_add_one` proves

    r+c <= e+1.

Its induction follows the walk itself: extending it by a row-column-row
segment cannot introduce more new vertices than new edges. This is the
cardinality inequality for a connected bipartite graph, established directly
from finite sets without assuming a graph-connectivity theorem.

`even_walk_edges_le` proves e<=k when every entry multiplicity is even.
The word has length 2k, and each used entry consumes at least two positions.
Together these prove `even_walk_vertices_le`:

    r+c <= k+1.

This bound does not require the endpoint condition, so it also applies to
every surviving closed walk counted by C_k.

Finally, `maximal_even_walk_edges_twice` proves that r+c=k+1 forces each used
entry to occur exactly twice. The proof forces e=k, then uses equality in
the sum of the multiplicity lower bounds.

## Partition grouping and remaining work

The coefficient formula is now proved, including order zero:

    C_k(p,n) = sum_(r,c) A_(k,r,c) (p)_r (n)_c,       k>=0,

where (p)_r is a falling factorial and A counts canonical row and column
partition patterns. The bijection, label multiplicities, and grouping by block
counts are proved in Lean. [PATTERNS.md](PATTERNS.md) describes the new proof chain.

The vertex bound now formally rules out surviving patterns with r+c>k+1, and
the corresponding coefficients are proved to vanish. The doubled-tree
classification, rooted ordered tree bijection, and general Narayana enumeration
are now proved as well. See [NARAYANA.md](NARAYANA.md) for the closed coefficient
formula and its connection to this walk expansion.
The project therefore does not yet prove all expected-moment limits,
concentration, or the Marchenko-Pastur spectral-distribution theorem.

## Independent computational checks

`experiments/exact_moments.py` compares three routes: exhaustive sign matrices,
cyclic partition patterns, and rooted labeled transitions. The third route
tracks parity with integer bit masks. There are 40 rooted-walk comparisons
across eight dimension pairs at orders 0 through 4, including p=1, n=1, and
p>n cases. These checks all pass. They validate the experiment's encodings;
Lean supplies the arbitrary-order mathematical proof.
