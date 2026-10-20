# Leading patterns and rooted ordered trees

The general bijection is proved in Lean, including both inverse identities,
the empty-walk case, and preservation of the row and column block counts.
For every k,r,c with r+c=k+1, the original moment coefficient satisfies

    A_(k,r,c) = number of rooted ordered trees with
                k edges, r even-depth vertices, and c odd-depth vertices.

The root has depth zero and is a row vertex. The equality is
`patternCoefficient_eq_treeCount`; the stronger type equivalence is
`coefficientTreeEquiv`. These use the original `patternCoefficient` definition,
so the result connects to the exact finite sign-matrix moment expansion.
The refined tree count is now evaluated by the general Narayana formula;
see [NARAYANA.md](NARAYANA.md).

## Tree representation

`OrderedTree` is mathlib's `Tree Unit`, interpreted as first child and remaining
children. Here `nil` means one root with no children. A node `(l,r)` attaches
the tree l as the first child of the root of r. Thus `numNodes` counts edges
of the corresponding rooted ordered tree, not its vertices.

The two color counts are defined recursively:

    R(nil)=1, C(nil)=0,
    R(node(l,r))=C(l)+R(r),
    C(node(l,r))=R(l)+C(r).

The child changes color on attachment. `tree_vertex_counts` proves that
R(t)+C(t)=numNodes(t)+1. The root and the order of children are retained;
there is no quotient by rotations, unrooted isomorphism, or child permutation.

`TreeVertex` gives every tree vertex a distinct canonical label using nested
sum types. `treeContour` records the depth-first vertex sequence after its
initial root, so its length is twice the number of edges. No numerical
first-occurrence labeling algorithm is assumed.

## Splitting a leading graph walk

The earlier doubled-tree theorem supplies an acyclic graph and a closed walk
with exactly two visits to each used edge. Its first edge is a bridge.
`tree_walk_first_child_split` proves that the walk has the form

    root -> child, closed child walk, child -> root, closed remaining walk.

The two closed walks have disjoint vertex supports and inherit the upper bound
of two visits per edge. Acyclicity forces a return across the first edge;
an additional crossing would violate the multiplicity bound. A shared vertex
between the two supports would create a bridge-avoiding route between its ends.

Strong induction on walk length then proves `acyclic_walk_orderedContour`.
The intermediate proposition `IsOrderedContour` records exactly this recursive
split and its disjointness condition. The first return to the root identifies
the split uniquely, giving `IsOrderedContour.unique`.

## From a contour to the original partitions

Even positions in the full vertex sequence are row positions, and odd
positions are column positions. Their equality kernels form `contourPattern`.
The proofs establish closure, even edge multiplicities, disjoint color classes,
and the exact block counts R(t), C(t). Thus every canonical tree contour gives
a surviving leading pattern.

Injective relabeling leaves these two kernels unchanged. Conversely, the
quotient blocks embed into the original vertex labels. Mapping the pattern's
graph walk through this embedding recovers the full contour in its original
order. Extracting partitions from an original pattern walk returns precisely
the original equivalence relations, without replacing their definition.

## Both inverses and the coefficient identity

`LeadingPattern` packages an order, the two partitions, survival, and maximal
block count. `treeToLeading` reads the canonical contour; `leadingToTree`
chooses the unique shape obtained from the graph walk. Its use of classical
choice is explicit. The Lean inverse is noncomputable; the Python stack
reconstruction remains a separately checked finite implementation.

The main results are:

- `leadingToTree_treeToLeading`: reconstruction returns the original tree.
- `treeToLeading_leadingToTree`: reading the reconstructed tree returns the
  original pattern.
- `orderedTreeLeadingEquiv`: the all-order equivalence.
- `orderedTreeLeadingEquiv_counts`: preservation of order and both color counts.
- `leadingPatternsTreeEquiv k`: the equivalence at each fixed order, including zero.
- `coefficientTreeEquiv k r c h`: the equivalence restricted to the subtype in
  the original coefficient definition, when h states r+c=k+1.
- `patternCoefficient_eq_treeCount`: the resulting cardinality equality.

These proofs are in `LeadingTreeBijection.lean` and `TreeCoefficients.lean`.
The preceding eight modules provide the walk split, canonical contours,
position selectors, edge parity, label kernels, and round-trip identities.
All ten modules are included in the aggregate build and dependency audit.

## Verification and next step

The independent Python checker still compares all 626 trees through order
seven with separately enumerated leading patterns. It now also checks the
first-child / remaining-children representation, the canonical sum-type
contour, and the color-reversing count recurrence against its ordered-child
list representation. The Python implementation is not formally verified.
See [VALIDATION.md](VALIDATION.md) for build, audit, and finite-check records.

The subsequent counting stage now proves the refined enumeration

    A_(k,r,k+1-r) = choose(k,r) choose(k,r-1) / k,   1<=r<=k.

The statistic is the number of even-depth vertices. The counting proof works
directly with the two color-counting series, so it does not require an
identification with Dyck-path peaks. The remaining stages are expected-moment
limits, fluctuations, the spectral-measure bridge, and the analytic steps in
[BLUEPRINT.md](BLUEPRINT.md).
