"""Exact finite variance and concentration checks, independent of Lean's proof kernel."""
from __future__ import annotations

import itertools
import json
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path

from exact_moments import falling, matmul, mp_moment, partitions

DIMENSIONS = [(1, 1), (1, 4), (2, 1), (2, 2), (2, 3), (3, 2), (3, 3), (3, 4)]


def matrix_moment_histograms(p: int, n: int, max_order: int) -> list[Counter[Fraction]]:
    histograms: list[Counter[Fraction]] = [Counter() for _ in range(max_order + 1)]
    for signs in itertools.product((-1, 1), repeat=p * n):
        x = [list(signs[i*n:(i+1)*n]) for i in range(p)]
        gram = matmul(x, list(map(list, zip(*x))))
        power = [[int(i == j) for j in range(p)] for i in range(p)]
        histograms[0][Fraction(1)] += 1
        for k in range(1, max_order + 1):
            power = matmul(power, gram)
            histograms[k][Fraction(sum(power[i][i] for i in range(p)), p*n**k)] += 1
    return histograms


def walk_pair_counts(p: int, n: int, k: int) -> tuple[int, int]:
    """Group actual labeled walks by parity and row support, retaining open walks."""
    all_walks: dict[int, Counter[int]] = defaultdict(Counter)
    closed_odd: Counter[int] = Counter()
    transitions = list(itertools.product(range(p), range(n)))
    for start in range(p):
        for steps in itertools.product(transitions, repeat=k):
            row, row_mask, parity = start, 1 << start, 0
            for next_row, col in steps:
                parity ^= 1 << (row*n + col)
                parity ^= 1 << (next_row*n + col)
                row_mask |= 1 << next_row
                row = next_row
            all_walks[parity][row_mask] += 1
            if row == start and parity:
                closed_odd[parity] += 1
    covariance_count = sum(count*count for count in closed_odd.values())
    upper_count = sum(a*b for rows in all_walks.values()
                      for r, a in rows.items() for s, b in rows.items() if r & s)
    assert covariance_count <= upper_count
    return covariance_count, upper_count


def joint_pattern_counts(k: int) -> tuple[Counter[tuple[int, int]], int]:
    """Joint partitions use separate initial/final positions; no closure is imposed."""
    columns = [(c, len(set(c))) for c in partitions(2*k)]
    counts: Counter[tuple[int, int]] = Counter()
    candidates = 0
    for rows in partitions(2*(k+1)):
        if not set(rows[:k+1]).intersection(rows[k+1:]):
            continue
        for cols, width in columns:
            candidates += 1
            edges: Counter[tuple[int, int]] = Counter()
            for side in range(2):
                for t in range(k):
                    col = cols[side*k+t]
                    edges[rows[side*(k+1)+t], col] += 1
                    edges[rows[side*(k+1)+t+1], col] += 1
            if any(multiplicity % 2 for multiplicity in edges.values()):
                continue
            r, c = len(set(rows)), width
            assert len(edges) <= 2*k and r+c <= 2*k+1
            adjacency = {('r', i): set() for i in set(rows)}
            adjacency.update({('c', i): set() for i in set(cols)})
            for i, j in edges:
                adjacency['r', i].add(('c', j))
                adjacency['c', j].add(('r', i))
            seen = {('r', rows[0])}
            todo = list(seen)
            while todo:
                for vertex in adjacency[todo.pop()] - seen:
                    seen.add(vertex)
                    todo.append(vertex)
            assert len(seen) == r+c
            counts[r, c] += 1
    return counts, candidates


def main() -> None:
    tables = {k: joint_pattern_counts(k) for k in range(4)}
    variance_checks = []
    pair_checks = []
    tail_checks = []
    a, b = Fraction(1, 4), Fraction(4)
    for p, n in DIMENSIONS:
        worlds = 2**(p*n)
        for k, histogram in enumerate(matrix_moment_histograms(p, n, 4)):
            mean = sum(value*count for value, count in histogram.items()) / worlds
            variance = sum((value-mean)**2*count for value, count in histogram.items()) / worlds
            target = mp_moment(k, Fraction(p, n))
            mean_square = sum((value-target)**2*count for value, count in histogram.items()) / worlds
            assert mean_square == variance + (mean-target)**2
            q = (2*(k+1))**(2*(k+1)) * (2*k)**(2*k)
            v_constant = q*b**(2*k)/a
            variance_bound = v_constant/n
            assert 0 <= variance <= variance_bound
            if k in (0, 1):
                assert variance == 0
            if k == 2:
                assert variance == Fraction(4*(p-1)*(n-1), p*n**3)
            variance_checks.append({"p": p, "n": n, "order": k, "mean": str(mean),
                                    "variance": str(variance), "bound": str(variance_bound)})
            h = (k+2)*(k+1)*(k+1)**(k+1)*k**k
            bias_bound = h*b**k*((k+1)**2*(1/a+1)+1)/n
            for epsilon in [Fraction(1, 4), Fraction(1, 2), Fraction(1), Fraction(2)]:
                probability = Fraction(sum(count for value, count in histogram.items()
                                           if abs(value-target) > epsilon), worlds)
                tight_bound = mean_square/epsilon**2
                formal_bound = (variance_bound+bias_bound**2)/epsilon**2
                assert 0 <= probability <= tight_bound <= formal_bound
                tail_checks.append({"p": p, "n": n, "order": k, "epsilon": str(epsilon),
                                    "probability": str(probability), "chebyshev": str(tight_bound),
                                    "formal_bound": str(formal_bound)})
            if k <= 3:
                cov_count, upper_count = walk_pair_counts(p, n, k)
                grouped_count = sum(count*falling(p, r)*falling(n, c)
                                    for (r, c), count in tables[k][0].items())
                assert upper_count == grouped_count
                assert variance == Fraction(cov_count, p*p*n**(2*k))
                pair_checks.append({"p": p, "n": n, "order": k,
                                    "covariance_pairs": cov_count, "upper_bound_pairs": upper_count})
    # Negative controls: covariance really occurs, and Chebyshev need not be equality.
    assert any(Fraction(row['variance']) > 0 for row in variance_checks)
    assert any(Fraction(row['probability']) < Fraction(row['chebyshev']) for row in tail_checks)
    result = {
        "status": "exact finite checks; general variance bounds and fixed-order convergence in probability proved separately in Lean",
        "normalization": "p^-1 trace((X X^T/n)^k)",
        "worlds": sum(2**(p*n) for p, n in DIMENSIONS),
        "variance_checks": variance_checks,
        "pair_count_checks": pair_checks,
        "tail_checks": tail_checks,
        "joint_patterns": [{"order": k, "candidates_with_shared_row": candidates,
                            "surviving_patterns": sum(table.values()),
                            "coefficients": [{"rows": r, "columns": c, "count": count}
                                             for (r, c), count in sorted(table.items())]}
                           for k, (table, candidates) in tables.items()],
    }
    out = Path(__file__).parent / 'results' / 'variance.json'
    out.write_text(json.dumps(result, indent=2)+'\n')
    print(f"PASS: {result['worlds']} sign matrices; {len(variance_checks)} exact variances; "
          f"{len(pair_checks)} paired-walk/partition comparisons; {len(tail_checks)} tail bounds; "
          f"{sum(c for _, c in tables.values())} shared-row partition candidates")


if __name__ == '__main__':
    main()
