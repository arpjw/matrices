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


def position_pattern_counts(k: int) -> Counter[tuple[int, int]]:
    """Use k+1 row positions and k column positions, as in the Lean definition.

    Partitions are encoded by first-occurrence labels. Closure identifies the
    final row with the initial row. An integer mask tracks multiplicity parity.
    """
    result: Counter[tuple[int, int]] = Counter()
    column_patterns = list(partitions(k))
    for rows in partitions(k + 1):
        if rows[-1] != rows[0]:
            continue
        for cols in column_patterns:
            width = max(cols, default=-1) + 1
            parity = 0
            for t, col in enumerate(cols):
                parity ^= 1 << (rows[t] * width + col)
                parity ^= 1 << (rows[t + 1] * width + col)
            if parity == 0:
                result[len(set(rows)), width] += 1
    return result


def labeling_fiber_checks() -> list[dict[str, int]]:
    """Compare exhaustive assignments with each partition's falling-factorial count."""
    checks: list[dict[str, int]] = []
    for positions in range(5):
        for labels in range(5):
            fibers: Counter[tuple[int, ...]] = Counter()
            for assignment in itertools.product(range(labels), repeat=positions):
                names: dict[int, int] = {}
                pattern = tuple(names.setdefault(value, len(names)) for value in assignment)
                fibers[pattern] += 1
            expected = {pattern: falling(labels, len(set(pattern)))
                        for pattern in partitions(positions)}
            assert all(fibers[pattern] == count for pattern, count in expected.items())
            assert sum(fibers.values()) == labels**positions
            checks.append({"positions": positions, "labels": labels,
                           "assignments": labels**positions, "patterns_checked": len(expected)})
    return checks


def falling(n: int, k: int) -> int:
    return math.prod(n - j for j in range(k)) if k <= n else 0


def labeled_walk_counts(p: int, n: int, k: int) -> Counter[tuple[int, int]]:
    """Enumerate the rooted transition encoding used in Lean, retaining closure.

    An integer bit mask tracks entry multiplicity parity. This is independent
    of the cyclic set-partition enumeration in pattern_counts.
    """
    result: Counter[tuple[int, int]] = Counter()
    transitions = list(itertools.product(range(p), range(n)))
    for start in range(p):
        for steps in itertools.product(transitions, repeat=k):
            row = start
            rows, cols = {start}, set()
            parity = 0
            for next_row, col in steps:
                parity ^= 1 << (row * n + col)
                parity ^= 1 << (next_row * n + col)
                rows.add(next_row)
                cols.add(col)
                row = next_row
            if row == start and parity == 0:
                result[len(rows), len(cols)] += 1
    return result


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


def mp_moment(k: int, ratio: Fraction) -> Fraction:
    """Closed Narayana polynomial, independent of the partition enumerator."""
    if k == 0:
        return Fraction(1)
    return sum((Fraction(math.comb(k, r) * math.comb(k, r - 1), k) * ratio**(r - 1)
                for r in range(1, k + 1)), Fraction(0))


def remainder_check(p: int, n: int, k: int, actual: Fraction,
                    a: Fraction, b: Fraction) -> dict[str, int | str]:
    ratio = Fraction(p, n)
    assert 0 < a <= ratio <= b and b >= 1
    budget = (k + 2) * (k + 1) * (k + 1)**(k + 1) * k**k
    constant = budget * b**k * ((k + 1)**2 * (1 / a + 1) + 1)
    target = mp_moment(k, ratio)
    error = abs(actual - target)
    bound = constant / n
    assert error <= bound, (p, n, k, actual, target, bound)
    return {"p": p, "n": n, "order": k, "a": str(a), "B": str(b),
            "moment": str(actual), "mp_at_current_ratio": str(target),
            "absolute_error": str(error), "bound": str(bound)}


def main() -> None:
    counts = {k: pattern_counts(k) for k in range(1, 8)}
    fiber_checks = labeling_fiber_checks()
    position_checks = []
    for k in range(8):
        table = position_pattern_counts(k)
        expected = Counter({(1, 0): 1}) if k == 0 else counts[k]
        assert table == expected, (k, table, expected)
        position_checks.append({"order": k, "surviving_patterns": sum(table.values()),
                                "nonzero_coefficients": len(table)})
    checks = []
    walk_checks = []
    direct_remainder_checks = []
    for p, n in [(1, 1), (1, 4), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3), (3, 4)]:
        brute = enumerate_moments(p, n, 4)
        combinatorial = [exact_moment(p, n, k, counts[k]) for k in range(1, 5)]
        assert brute == combinatorial, (p, n, brute, combinatorial)
        direct_remainder_checks.extend(
            remainder_check(p, n, k, value, Fraction(1, 4), Fraction(4))
            for k, value in enumerate([Fraction(1), *brute]))
        assert brute[0] == 1
        assert brute[1] == 1 + Fraction(p - 1, n)
        assert brute[2] == 1 + Fraction(3 * (p - 1), n) + Fraction((p - 1) * (p - 2), n**2)
        checks.append({"p": p, "n": n, "worlds": 2 ** (p * n), "moments": list(map(str, brute))})
        for k in range(5):
            labeled = labeled_walk_counts(p, n, k)
            grouped = (Counter({(1, 0): p}) if k == 0 else
                       Counter({(r, s): c * falling(p, r) * falling(n, s)
                                for (r, s), c in counts[k].items()}))
            assert labeled == grouped, (p, n, k, labeled, grouped)
            moment = Fraction(sum(labeled.values()), p * n**k)
            assert moment == (1 if k == 0 else brute[k - 1])
            assert all(r + s <= k + 1 for r, s in labeled)
            walk_checks.append({"p": p, "n": n, "order": k,
                                "candidate_walks": p * (p * n)**k,
                                "even_closed_walks": sum(labeled.values()),
                                "moment": str(moment)})
    leading_checks = []
    for k, table in counts.items():
        assert all(r + s <= k + 1 for r, s in table)
        leading = {r: table[r, k + 1 - r] for r in range(1, k + 1)}
        narayana = {r: math.comb(k, r) * math.comb(k, r - 1) // k for r in range(1, k + 1)}
        assert leading == narayana, (k, leading, narayana)
        leading_checks.append({"order": k, "leading_coefficients": leading})
    higher_remainder_checks = [
        remainder_check(p, n, k, Fraction(1) if k == 0 else exact_moment(p, n, k, counts[k]),
                        Fraction(1, 7), Fraction(7))
        for p, n in [(1, 7), (7, 1), (16, 64), (64, 16), (8, 8), (4, 16), (16, 4)]
        for k in range(8)
    ]
    # Ratio convergence alone supplies no O(1/n) rate to the polynomial at gamma.
    ratio_rate_checks = []
    for m in [2, 4, 8, 16, 32, 64]:
        n, p = m*m, m*m + m
        actual = exact_moment(p, n, 2, counts[2])
        assert actual - mp_moment(2, Fraction(p, n)) == -Fraction(1, n)
        scaled_limit_error = n * abs(actual - mp_moment(2, Fraction(1)))
        assert scaled_limit_error == m - 1
        ratio_rate_checks.append({"m": m, "p": p, "n": n,
                                  "n_times_error_to_gamma_one": str(scaled_limit_error)})
    result = {
        "status": "exact finite computations; all-order partition grouping, falling-factorial multiplicities, coefficient formula and support bound proved in Lean; general Narayana formula, all fixed-order expected-moment limits and explicit finite-size bounds proved separately in Lean",
        "normalization": "p^-1 trace((X X^T / n)^k)",
        "labeling_fiber_checks": fiber_checks,
        "position_partition_checks": position_checks,
        "exhaustive_checks": checks,
        "labeled_walk_checks": walk_checks,
        "leading_term_checks": leading_checks,
        "direct_remainder_checks": direct_remainder_checks,
        "higher_order_remainder_checks": higher_remainder_checks,
        "ratio_rate_checks": ratio_rate_checks,
        "pattern_counts": {str(k): [{"row_blocks": r, "column_blocks": s, "count": c}
                                    for (r, s), c in sorted(table.items())]
                           for k, table in counts.items()},
    }
    out = Path(__file__).parent / "results" / "exact-moments.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(f"PASS: {sum(c['worlds'] for c in checks)} matrices; 32 moment comparisons; "
          f"{len(walk_checks)} labeled walk comparisons (including order zero); "
          f"{sum(c['patterns_checked'] for c in fiber_checks)} labeling fibers; "
          "position partition coefficients at orders 0..7; "
          "orders 1..7 leading coefficients; "
          f"{len(direct_remainder_checks)} direct finite-bias bounds; "
          f"{len(higher_remainder_checks)} coefficient-based finite-bias bounds; "
          f"{len(ratio_rate_checks)} ratio-rate controls")


if __name__ == "__main__":
    main()
