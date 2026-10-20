"""Independent finite checks for doubled trees and the ordered-tree bijection.

The graph characterization and general bijection are proved separately in Lean.
This Python implementation is not formally verified. The general Narayana count
is now also proved separately in Lean.
"""
from __future__ import annotations

import itertools
import json
import math
from collections import Counter
from functools import cache
from pathlib import Path

from exact_moments import partitions

Vertex = tuple[int, int]
Pattern = tuple[tuple[int, ...], tuple[int, ...]]
Tree = tuple["Tree", ...]
BinaryTree = tuple["BinaryTree", "BinaryTree"] | None
Address = tuple[int, ...]


def entry_counts(rows: tuple[int, ...], cols: tuple[int, ...]) -> Counter[tuple[int, int]]:
    return Counter((rows[t + offset], col)
                   for t, col in enumerate(cols) for offset in (0, 1))


def graph_properties(rows: tuple[int, ...], cols: tuple[int, ...]) -> tuple[bool, bool]:
    """Check connectivity and cycles by graph traversal, independently of edge counts."""
    vertices = {(0, row) for row in rows} | {(1, col) for col in cols}
    adjacency: dict[Vertex, set[Vertex]] = {vertex: set() for vertex in vertices}
    for row, col in entry_counts(rows, cols):
        u, v = (0, row), (1, col)
        adjacency[u].add(v)
        adjacency[v].add(u)
    root = (0, rows[0])
    seen = {root}
    pending: list[tuple[Vertex, Vertex | None]] = [(root, None)]
    acyclic = True
    while pending:
        vertex, parent = pending.pop()
        for neighbor in adjacency[vertex]:
            if neighbor == parent:
                continue
            if neighbor in seen:
                acyclic = False
            else:
                seen.add(neighbor)
                pending.append((neighbor, vertex))
    return seen == vertices, acyclic


@cache
def ordered_trees(edges: int) -> tuple[Tree, ...]:
    """A tree is its ordered tuple of child trees; split off the first child."""
    if edges == 0:
        return ((),)
    return tuple((child,) + rest
                 for child_edges in range(edges)
                 for child in ordered_trees(child_edges)
                 for rest in ordered_trees(edges - 1 - child_edges))



def to_binary(tree: Tree) -> BinaryTree:
    """First child / remaining children, matching Lean's Tree Unit interpretation."""
    return None if not tree else (to_binary(tree[0]), to_binary(tree[1:]))


def from_binary(tree: BinaryTree) -> Tree:
    return () if tree is None else (from_binary(tree[0]),) + from_binary(tree[1])


def binary_statistics(tree: BinaryTree) -> tuple[int, int, int]:
    """Edges, row vertices, column vertices; the child reverses colors."""
    if tree is None:
        return (0, 1, 0)
    left_edges, left_rows, left_cols = binary_statistics(tree[0])
    right_edges, right_rows, right_cols = binary_statistics(tree[1])
    return (1 + left_edges + right_edges, left_cols + right_rows, left_rows + right_cols)


def binary_contour(tree: BinaryTree) -> tuple[Address, list[Address]]:
    """Distinct sum-type addresses and the contour tail used by the Lean construction."""
    if tree is None:
        return (), []
    left_root, left_tail = binary_contour(tree[0])
    right_root, right_tail = binary_contour(tree[1])
    return ((1,) + right_root,
            [(0,) + vertex for vertex in [left_root] + left_tail] +
            [(1,) + vertex for vertex in [right_root] + right_tail])


def label_partition(vertices: list[Address]) -> tuple[int, ...]:
    labels: dict[Address, int] = {}
    return tuple(labels.setdefault(vertex, len(labels)) for vertex in vertices)

def tree_to_pattern(tree: Tree) -> Pattern:
    """Depth-first contour, with separate first-occurrence row and column labels."""
    next_label = [1, 0]
    contour: list[Vertex] = [(0, 0)]

    def visit(subtree: Tree, vertex: Vertex) -> None:
        for child in subtree:
            color = 1 - vertex[0]
            child_vertex = (color, next_label[color])
            next_label[color] += 1
            contour.append(child_vertex)
            visit(child, child_vertex)
            contour.append(vertex)

    visit(tree, (0, 0))
    assert all(vertex[0] == t % 2 for t, vertex in enumerate(contour))
    return (tuple(v[1] for v in contour[::2]), tuple(v[1] for v in contour[1::2]))


def pattern_to_tree(pattern: Pattern) -> Tree:
    """Reconstruct ordered children; revisiting a vertex must return to the parent."""
    rows, cols = pattern
    contour = list(itertools.chain.from_iterable(
        ((0, rows[t]), (1, col)) for t, col in enumerate(cols))) + [(0, rows[-1])]
    root = contour[0]
    children: dict[Vertex, list[Vertex]] = {root: []}
    stack = [root]
    for vertex in contour[1:]:
        if vertex not in children:
            children[vertex] = []
            children[stack[-1]].append(vertex)
            stack.append(vertex)
        else:
            assert len(stack) > 1 and vertex == stack[-2], (pattern, stack, vertex)
            stack.pop()
    assert stack == [root], (pattern, stack)

    def freeze(vertex: Vertex) -> Tree:
        return tuple(freeze(child) for child in children[vertex])

    return freeze(root)


def graph_checks() -> list[dict[str, int]]:
    checks = []
    for k in range(7):
        candidates = surviving = leading = nonleading_trees = 0
        col_patterns = tuple(partitions(k))
        for rows in partitions(k + 1):
            for cols in col_patterns:
                candidates += 1
                connected, acyclic = graph_properties(rows, cols)
                assert connected, (rows, cols)
                counts = entry_counts(rows, cols)
                vertices = len(set(rows)) + len(set(cols))
                assert acyclic == (len(counts) + 1 == vertices)
                if rows[0] != rows[-1] or any(count % 2 for count in counts.values()):
                    continue
                surviving += 1
                doubled = all(count == 2 for count in counts.values())
                maximal = vertices == k + 1
                assert maximal == (acyclic and doubled), (rows, cols)
                leading += maximal
                nonleading_trees += acyclic and not maximal
        checks.append({"order": k, "all_patterns_checked": candidates,
                       "surviving_patterns": surviving, "leading_patterns": leading,
                       "nonleading_surviving_trees": nonleading_trees})
    # Each condition is necessary: these are closed, even, nonleading patterns.
    repeated_edge: Pattern = ((0, 0, 0), (0, 0))
    doubled_cycle: Pattern = ((0, 1, 0, 1, 0), (0, 1, 0, 1))
    assert graph_properties(*repeated_edge) == (True, True)
    assert set(entry_counts(*repeated_edge).values()) == {4}
    assert graph_properties(*doubled_cycle) == (True, False)
    assert set(entry_counts(*doubled_cycle).values()) == {2}
    return checks


def bijection_checks() -> list[dict[str, int | dict[int, int]]]:
    checks = []
    for k in range(8):
        leading: set[Pattern] = set()
        column_patterns = tuple((cols, len(set(cols))) for cols in partitions(k))
        for rows in partitions(k + 1):
            if rows[-1] != rows[0]:
                continue
            row_blocks = len(set(rows))
            for cols, col_blocks in column_patterns:
                if row_blocks + col_blocks != k + 1:
                    continue
                if all(count % 2 == 0 for count in entry_counts(rows, cols).values()):
                    leading.add((rows, cols))
        trees = ordered_trees(k)
        for tree in trees:
            binary = to_binary(tree)
            assert from_binary(binary) == tree
            root, tail = binary_contour(binary)
            contour = [root] + tail
            rows, cols = tree_to_pattern(tree)
            assert (label_partition(contour[::2]), label_partition(contour[1::2])) == (rows, cols)
            assert binary_statistics(binary) == (k, len(set(rows)), len(set(cols)))
            assert len(tail) == 2 * k and contour[-1] == root
        images = {tree_to_pattern(tree) for tree in trees}
        assert len(images) == len(trees)
        assert images == leading, k
        assert all(pattern_to_tree(tree_to_pattern(tree)) == tree for tree in trees)
        assert all(tree_to_pattern(pattern_to_tree(pattern)) == pattern for pattern in leading)
        by_rows = Counter(len(set(rows)) for rows, _ in images)
        narayana = ({1: 1} if k == 0 else
                    {r: math.comb(k, r) * math.comb(k, r - 1) // k for r in range(1, k + 1)})
        assert by_rows == narayana
        assert len(trees) == math.comb(2 * k, k) // (k + 1)
        checks.append({"order": k, "trees": len(trees), "leading_patterns": len(leading),
                       "binary_encoding_checks": len(trees),
                       "counts_by_row_vertices": dict(sorted(by_rows.items()))})
    return checks


def main() -> None:
    graphs = graph_checks()
    bijections = bijection_checks()
    result = {
        "status": "finite independent checks; graph characterization and general ordered-tree "
                  "bijection and Narayana enumeration proved separately in Lean",
        "graph_checks": graphs,
        "ordered_tree_bijection_checks": bijections,
        "counterexamples": {
            "tree_without_double_traversal": {"rows": [0, 0, 0], "cols": [0, 0]},
            "double_traversal_without_tree": {"rows": [0, 1, 0, 1, 0], "cols": [0, 1, 0, 1]},
        },
    }
    out = Path(__file__).parent / "results" / "tree-patterns.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(f"PASS: {sum(c['all_patterns_checked'] for c in graphs)} partition graphs; "
          f"{sum(c['trees'] for c in bijections)} ordered trees with both inverse checks; "
          "binary encoding and color recurrence; orders 0..7 refined counts; "
          "both necessary-condition counterexamples")


if __name__ == "__main__":
    main()
