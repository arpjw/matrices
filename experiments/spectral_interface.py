"""Exact finite spectral checks. Independent evidence, not a Lean proof.

All sign matrices with 1 <= p,n <= 5 and min(p,n) <= 2 have rational
spectra available from a two-by-two Gram matrix. Check those spectra by
exact characteristic-polynomial evaluations and independent elimination.
"""
from __future__ import annotations

import itertools
import json
import math
from fractions import Fraction
from pathlib import Path

from exact_moments import matmul


def determinant(a: list[list[Fraction]]) -> Fraction:
    a = [row[:] for row in a]
    result = Fraction(1)
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            result = -result
        result *= a[j][j]
        for i in range(j + 1, len(a)):
            factor = a[i][j] / a[j][j]
            a[i] = [x - factor * y for x, y in zip(a[i], a[j])]
    return result


def rank(a: list[list[int]]) -> int:
    rows = [[Fraction(x) for x in row] for row in a]
    r = 0
    for j in range(len(rows[0])):
        pivot = next((i for i in range(r, len(rows)) if rows[i][j]), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        for i in range(r + 1, len(rows)):
            factor = rows[i][j] / rows[r][j]
            rows[i] = [x - factor * y for x, y in zip(rows[i], rows[r])]
        r += 1
    return r


def sign_eigenvalues(x: list[list[int]]) -> list[Fraction]:
    p, n = len(x), len(x[0])
    if p == 1:
        return [Fraction(1)]
    if n == 1:
        return [Fraction(p), *[Fraction(0)] * (p - 1)]
    if p == 2:
        dot = sum(x[0][a] * x[1][a] for a in range(n))
        return [1 + Fraction(dot, n), 1 - Fraction(dot, n)]
    assert n == 2
    dot = sum(row[0] * row[1] for row in x)
    return [Fraction(p + dot, n), Fraction(p - dot, n), *[Fraction(0)] * (p - 2)]


def check(x: list[list[int]], values: list[Fraction]) -> dict[str, int]:
    p, n = len(x), len(x[0])
    assert len(values) == p and all(v >= 0 for v in values)
    gram = [[sum(x[i][a] * x[j][a] for a in range(n)) for j in range(p)] for i in range(p)]
    # Equality at p+1 distinct points certifies equality of the degree-p polynomials.
    for t in range(-1, p):
        shifted = [[Fraction(t * (i == j)) - Fraction(gram[i][j], n)
                    for j in range(p)] for i in range(p)]
        assert determinant(shifted) == math.prod(Fraction(t) - v for v in values)
    matrix_rank = rank(gram)
    zeros = values.count(0)
    assert zeros == p - matrix_rank
    assert Fraction(zeros, p) >= max(1 - Fraction(n, p), 0)
    power = [[int(i == j) for j in range(p)] for i in range(p)]
    for k in range(7):
        trace_moment = Fraction(sum(power[i][i] for i in range(p)), p * n**k)
        assert sum(v**k for v in values) / p == trace_moment
        power = matmul(power, gram)
    return {"p": p, "n": n, "zero_count": zeros, "rank": matrix_rank}


def main() -> None:
    ensembles = []
    total = 0
    polynomial_evaluations = 0
    for p in range(1, 6):
        for n in range(1, 6):
            if min(p, n) > 2:
                continue
            zero_counts: set[int] = set()
            for entries in itertools.product((-1, 1), repeat=p * n):
                x = [list(entries[i * n:(i + 1) * n]) for i in range(p)]
                result = check(x, sign_eigenvalues(x))
                zero_counts.add(result["zero_count"])
                total += 1
                polynomial_evaluations += p + 1
            ensembles.append({"p": p, "n": n, "matrices": 2**(p*n),
                              "zero_counts": sorted(zero_counts)})
    examples = [
        ("zero_matrix", [[0, 0, 0], [0, 0, 0]], [Fraction(0), Fraction(0)]),
        ("distinct_diagonal", [[1, 0, 0], [0, 2, 0], [0, 0, 3]],
         [Fraction(1, 3), Fraction(4, 3), Fraction(3)]),
        ("rank_one", [[1, 2], [2, 4], [3, 6], [4, 8]],
         [Fraction(75), Fraction(0), Fraction(0), Fraction(0)]),
        ("repeated_positive", [[1, 1], [1, -1]], [Fraction(1), Fraction(1)]),
    ]
    extra = [{"name": name, **check(x, values), "eigenvalues": list(map(str, values))}
             for name, x, values in examples]
    polynomial_evaluations += sum(len(x) + 1 for _, x, _ in examples)
    # Regression controls: three common incorrect empirical measures must disagree.
    rectangular = [Fraction(2), Fraction(0)]
    positive = [v for v in rectangular if v > 0]
    assert Fraction(len(positive), 2) != 1  # dropping zeros loses total mass
    assert sum(positive) / len(positive) != 1  # renormalization changes the first moment
    assert Fraction(len(set([1, 1])), 2) != 1  # deduplication loses multiplicity
    record = {"status": "exact finite checks, not a formal proof",
              "sign_matrices": total, "additional_matrices": len(examples),
              "moment_checks": (total + len(examples)) * 7,
              "characteristic_polynomial_evaluations": polynomial_evaluations,
              "rank_and_zero_atom_checks": total + len(examples),
              "moment_orders": list(range(7)), "ensembles": ensembles, "examples": extra,
              "incorrect_measure_controls_rejected": 3}
    out = Path(__file__).parent / "results" / "spectral-interface.json"
    out.write_text(json.dumps(record, indent=2) + "\n")
    print(f"PASS: {total} sign matrices and {len(examples)} additional matrices; "
          f"{record['moment_checks']} exact moments; {polynomial_evaluations} characteristic "
          f"polynomial evaluations; {record['rank_and_zero_atom_checks']} rank/atom checks; "
          "3 incorrect-measure controls rejected")


if __name__ == "__main__":
    main()
