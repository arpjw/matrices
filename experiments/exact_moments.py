"""Exact Rademacher covariance moments. Computational evidence, not a Lean proof."""
from __future__ import annotations

import itertools
import json
import math
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Iterator


def partitions(k: int) -> Iterator[tuple[int, ...]]:
    """Canonical restricted-growth encodings of set partitions of [k]."""
    if k == 0:
        yield ()
        return

    def extend(prefix: tuple[int, ...], largest: int) -> Iterator[tuple[int, ...]]:
        if len(prefix) == k:
            yield prefix
        else:
            for label in range(largest + 2):
                yield from extend(prefix + (label,), max(largest, label))

    yield from extend((0,), 0)


def pattern_counts(k: int) -> Counter[tuple[int, int]]:
    """Count even-edge alternating closed walks, grouped by row/column blocks."""
    result: Counter[tuple[int, int]] = Counter()
    ps = list(partitions(k))
    for rows in ps:
        for cols in ps:
            edges: Counter[tuple[int, int]] = Counter()
            for t in range(k):
                edges[rows[t], cols[t]] += 1
                edges[rows[(t + 1) % k], cols[t]] += 1
            if all(count % 2 == 0 for count in edges.values()):
                result[max(rows) + 1, max(cols) + 1] += 1
    return result


def falling(n: int, k: int) -> int:
    return math.prod(n - j for j in range(k)) if k <= n else 0


def exact_moment(p: int, n: int, k: int, counts: Counter | None = None) -> Fraction:
    if p <= 0 or n <= 0 or k <= 0:
        raise ValueError("positive dimensions and moment order required")
    if counts is None:
        counts = pattern_counts(k)
    total = sum(c * falling(p, r) * falling(n, s) for (r, s), c in counts.items())
    return Fraction(total, p * n**k)


def matmul(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def enumerate_moments(p: int, n: int, max_k: int) -> list[Fraction]:
    if p * n > 12:
        raise ValueError("exhaustive enumeration is capped at 12 independent signs")
    totals = [0] * max_k
    for signs in itertools.product((-1, 1), repeat=p * n):
        x = [list(signs[i * n : (i + 1) * n]) for i in range(p)]
        gram = matmul(x, list(map(list, zip(*x))))
        power = [[int(i == j) for j in range(p)] for i in range(p)]
        for k in range(1, max_k + 1):
            power = matmul(power, gram)
            totals[k - 1] += sum(power[i][i] for i in range(p))
    return [Fraction(t, 2 ** (p * n) * p * n**k) for k, t in enumerate(totals, 1)]


def main() -> None:
    counts = {k: pattern_counts(k) for k in range(1, 8)}
    checks = []
    for p, n in [(1, 1), (1, 4), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3), (3, 4)]:
        brute = enumerate_moments(p, n, 4)
        combinatorial = [exact_moment(p, n, k, counts[k]) for k in range(1, 5)]
        assert brute == combinatorial, (p, n, brute, combinatorial)
        assert brute[0] == 1
        assert brute[1] == 1 + Fraction(p - 1, n)
        assert brute[2] == 1 + Fraction(3 * (p - 1), n) + Fraction((p - 1) * (p - 2), n**2)
        checks.append({"p": p, "n": n, "worlds": 2 ** (p * n), "moments": list(map(str, brute))})
    leading_checks = []
    for k, table in counts.items():
        assert all(r + s <= k + 1 for r, s in table)
        leading = {r: table[r, k + 1 - r] for r in range(1, k + 1)}
        narayana = {r: math.comb(k, r) * math.comb(k, r - 1) // k for r in range(1, k + 1)}
        assert leading == narayana, (k, leading, narayana)
        leading_checks.append({"order": k, "leading_coefficients": leading})
    result = {
        "status": "exact finite computations; general counting theorem remains unproved in Lean",
        "normalization": "p^-1 trace((X X^T / n)^k)",
        "exhaustive_checks": checks,
        "leading_term_checks": leading_checks,
        "pattern_counts": {str(k): [{"row_blocks": r, "column_blocks": s, "count": c}
                                    for (r, s), c in sorted(table.items())]
                           for k, table in counts.items()},
    }
    out = Path(__file__).parent / "results" / "exact-moments.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(f"PASS: {sum(c['worlds'] for c in checks)} matrices; 32 moment comparisons; orders 1..7 leading coefficients")


if __name__ == "__main__":
    main()
