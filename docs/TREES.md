# Leading patterns are doubled trees

The all-order graph classification is now proved in Lean. For row and column
partitions r and c at order k,

    PatternSurvives k r c and blockCount r + blockCount c = k+1

is equivalent to all three of the following:

1. The last row block equals the initial row block.
2. The graph on row and column blocks is a tree.
3. Every visited entry occurs exactly twice in the ordered entry word.

The theorem is `leading_pattern_iff_closed_doubled_tree`. It includes k=0:
the graph is a single row vertex and the closed walk is empty.
This graph classification is strengthened by the now-proved arbitrary-order
bijection with rooted ordered trees. See [ORDERED_TREES.md](ORDERED_TREES.md)
for both inverse identities and the preserved color counts. The general
Narayana formula is also proved; see [NARAYANA.md](NARAYANA.md).

## Boundary coefficients

`PatternBoundary.lean` proves

    A_(0,r,c) = 1 if (r,c)=(1,0), and 0 otherwise,
    A_(k,0,c) = 0,
    A_(k,r,0) = 0 for k>0.

These are statements about the cardinalities in the original coefficient
definition. They are not replacement definitions or imported numerical values.

## The graph and its counts

`PatternGraph.lean` constructs a simple graph on

    Quotient r + Quotient c.

The sum type keeps a row block distinct from a column block even when numerical
representatives would coincide. An entry is an edge between its row and column
blocks. `entryGraphEdgeEquiv` proves that distinct entry pairs correspond
bijectively to undirected graph edges.

The vertex cardinality is exactly `blockCount r + blockCount c`. The edge
cardinality is exactly the number of distinct entries in `patternWord r c`.
The graph is bipartite and connected for every pattern, including patterns
that fail parity or endpoint closure. Connectivity follows from the successive
row-column-row transitions, which reach every block from the initial row block.
No representative labeling is chosen for these constructions.

## Why maximal patterns are trees

Write v for the vertex count and e for the edge count. Connectivity gives
v <= e+1. For a surviving pattern, each used entry has positive even
multiplicity and the word has length 2k, so e <= k.

If v=k+1, both inequalities are equalities. Thus e=k and v=e+1.
Mathlib's finite-graph criterion proves that a connected graph with v=e+1
is a tree. Since k distinct entries fill 2k positions with even positive
multiplicities, every entry occurs twice.

Conversely, if a pattern graph is a tree and each entry occurs twice, the
word length forces e=k and the tree cardinality gives v=k+1. Endpoint closure
and double occurrence then imply the original sign-expectation survival
predicate. `PatternTrees.lean` proves both implications.

Neither tree structure alone nor double occurrence alone suffices:

- At order two, repeatedly traversing a single edge four times gives a
  surviving tree pattern with only two vertices, below k+1=3.
- At order four, traversing a four-cycle twice uses each entry twice but
  has four vertices, below k+1=5.

## Retaining the traversal order

`PatternContour.lean` constructs `patternGraphWalk` in mathlib's graph-walk
type. Its endpoints are the initial and final row blocks. Its edge list is
exactly the original position word mapped to undirected graph edges, in order.
Its length is 2k.

For surviving patterns, `patternClosedGraphWalk` closes this walk at the
distinguished initial row block. For leading patterns, the actual graph walk
uses every edge in its edge list exactly twice. This gives the next bijection
proof a concrete rooted traversal, preserving its start and ordering.

The subsequent `acyclic_walk_orderedContour` and `IsOrderedContour.unique`
now prove that this traversal is the contour of a unique rooted ordered tree.
The bridge split and the resulting equivalence are described in
[ORDERED_TREES.md](ORDERED_TREES.md).

## Independent finite checks

Run:

```sh
python3 experiments/tree_patterns.py
```

The checker traverses 189,455 partition graphs at orders 0 through 6,
including open and odd-multiplicity patterns. It checks connectivity and
detects cycles by graph traversal, independently of the edge-cardinality
criterion. For every surviving pattern in that range, it checks the doubled
tree characterization. Both counterexamples above are explicit checks.

A separate prototype represents a rooted ordered tree by its ordered tuple
of child trees. It generates the depth-first contour and assigns separate
first-occurrence labels to row and column vertices. The inverse reconstructs
children with a stack: a new vertex creates the next child, and a previously
seen vertex must be the current vertex's parent.

For all 626 rooted ordered trees at orders 0 through 7, the image equals
the independently enumerated set of leading patterns. Both inverse identities
pass, and the refined counts by row vertices agree with the Narayana formula.
The arbitrary-order bijection and Narayana enumeration are now proved
separately in Lean. The Python implementation is not formally
verified. It also checks that its child-list representation agrees with the
first-child / remaining-children representation used by the Lean proof.

Results: [tree-patterns.json](../experiments/results/tree-patterns.json).

## Bijection checklist

All five items below are now complete in Lean. The counting proof uses formal
generating functions and a three-term recurrence, as described in
[NARAYANA.md](NARAYANA.md).

1. Define rooted ordered trees with an explicit first-child and remaining-child
   decomposition, together with their row and column vertex counts.
2. Turn each ordered contour into its two position partitions. Prove endpoint
   closure, double occurrence, and the required block counts.
3. Recover the first child excursion of a leading pattern. The first tree edge
   is a bridge and is used twice; prove that the excursion cannot leave its
   subtree before returning across that edge.
4. Recurse over the child excursion and the remaining root excursions. Prove
   both inverse identities and preservation of the number of row vertices.
   The root and child order must be retained, with no quotient by rotations.
5. Derive the refined finite counting recurrence and prove

       A_(k,r,k+1-r) = choose(k,r) choose(k,r-1) / k,   1<=r<=k.

The color refinement accounts for the first child's root having the
opposite color. If that subtree has l edges and a row vertices relative to its
own root, and the remaining-root tree has b row vertices, the assembled tree
has b+(l+1-a) row vertices. Ordinary Dyck-path peak counts cannot simply be
substituted for this statistic without a proved correspondence.

All fixed-order expected-moment limits and explicit finite-size bounds are
now proved in [EXPECTED_MOMENTS.md](EXPECTED_MOMENTS.md). Variance bounds and
fixed-order moment concentration are now proved in [CONCENTRATION.md](CONCENTRATION.md).
The spectral-measure bridge and the analytic Marchenko-Pastur identification
remain open. See [BLUEPRINT.md](BLUEPRINT.md).
