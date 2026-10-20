"""Independent numerical integration and exact polynomial checks for the MP law.

Quadrature evaluates the explicit density using x=a+(b-a)u^2. This is a
numerical cross-check, not certified interval arithmetic or a Lean proof.
"""
from __future__ import annotations

import heapq
import json
import math
from fractions import Fraction
from pathlib import Path
from typing import Callable


def moment(k: int, gamma: Fraction) -> Fraction:
    if k == 0:
        return Fraction(1)
    return sum((Fraction(math.comb(k, j + 1) * math.comb(k, j), k) * gamma**j
                for j in range(k)), Fraction(0))


def integrate(f: Callable[[float], float], tolerance: float) -> tuple[float, int]:
    evaluations = 3
    serial = 0

    def panel(a: float, b: float, fa: float, fm: float, fb: float) -> tuple:
        nonlocal evaluations, serial
        m = (a + b) / 2
        fl, fr = f((a + m) / 2), f((m + b) / 2)
        evaluations += 2
        old = (b - a) * (fa + 4 * fm + fb) / 6
        lo = (m - a) * (fa + 4 * fl + fm) / 6
        hi = (b - m) * (fm + 4 * fr + fb) / 6
        correction = (lo + hi - old) / 15
        serial += 1
        return (-abs(correction), serial, a, b, fa, fl, fm, fr, fb, lo + hi + correction)

    first = panel(0.0, 1.0, f(0.0), f(0.5), f(1.0))
    heap = [first]
    total_error = -first[0]
    # Refine the largest estimated error, using a global error budget. Endpoint
    # square roots need not satisfy an arbitrarily tiny per-panel relative budget.
    while total_error > tolerance:
        neg_error, _, a, b, fa, fl, fm, fr, fb, _ = heapq.heappop(heap)
        m = (a + b) / 2
        if len(heap) > 100000 or m in (a, b):
            raise RuntimeError("Quadrature failed to reach its requested tolerance")
        lo, hi = panel(a, m, fa, fl, fm), panel(m, b, fm, fr, fb)
        total_error += neg_error - lo[0] - hi[0]
        heapq.heappush(heap, lo)
        heapq.heappush(heap, hi)
    return math.fsum(row[-1] for row in heap), evaluations


def density_integral(gamma: Fraction, k: int, tolerance: float) -> tuple[float, int]:
    g = float(gamma)
    root = math.sqrt(g)
    a, width = (1 - root)**2, 4 * root
    target = min(Fraction(1), 1 / gamma) if k == 0 else moment(k, gamma)
    scale = max(1.0, float(target))

    def transformed(u: float) -> float:
        if u == 0:
            return 4 / math.pi if gamma == 1 and k == 0 else 0.0
        if u == 1:
            return 0.0
        x = a + width * u * u
        # Explicit density times dx/du, with endpoint cancellation made stable.
        weighted_density = width**2 * u**2 * math.sqrt(1 - u**2) / (math.pi * g * x)
        return weighted_density * (x**k / scale)

    value, evaluations = integrate(transformed, tolerance)
    return value * scale, evaluations


def main() -> None:
    gammas = [Fraction(1, 100), Fraction(1, 10), Fraction(1, 4), Fraction(1, 2),
              Fraction(9, 10), Fraction(99, 100), Fraction(999, 1000), Fraction(1),
              Fraction(1001, 1000), Fraction(101, 100), Fraction(11, 10),
              Fraction(2), Fraction(4), Fraction(10), Fraction(100)]
    records = []
    exact_checks = 0
    for gamma in gammas:
        atom = max(1 - 1 / gamma, Fraction(0))
        continuous_mass = min(Fraction(1), 1 / gamma)
        assert atom + continuous_mass == 1
        assert moment(1, gamma) == 1 and moment(2, gamma) == 1 + gamma
        for k in range(30):
            assert (k + 4) * moment(k + 3, gamma) == (
                (2*k + 5) * (1 + gamma) * moment(k + 2, gamma)
                - (k + 1) * (gamma - 1)**2 * moment(k + 1, gamma))
            exact_checks += 1
        rows = []
        for k in range(11):
            value, evaluations = density_integral(gamma, k, 1e-11)
            expected = continuous_mass if k == 0 else moment(k, gamma)
            error = abs(value - float(expected)) / max(1.0, abs(float(expected)))
            assert error < 1e-8, (gamma, k, value, expected, error)
            full_moment = value + float(atom) if k == 0 else value
            assert abs(full_moment - float(moment(k, gamma))) / max(1.0, float(moment(k, gamma))) < 1e-8
            rows.append({"order": k, "continuous_integral": value, "expected": str(expected),
                         "scaled_absolute_error": error, "evaluations": evaluations})
        records.append({"gamma": str(gamma), "atom": str(atom),
                        "continuous_mass": str(continuous_mass), "moments": rows})
    refinements = []
    for gamma in (Fraction(999, 1000), Fraction(1), Fraction(1001, 1000), Fraction(4)):
        for k in (0, 2, 10):
            coarse, _ = density_integral(gamma, k, 1e-8)
            fine, _ = density_integral(gamma, k, 1e-11)
            discrepancy = abs(coarse - fine) / max(1.0, abs(fine))
            assert discrepancy < 1e-7
            refinements.append({"gamma": str(gamma), "order": k, "scaled_difference": discrepancy})
    # Normalization errors are exposed numerically, not silently normalized away.
    mass, _ = density_integral(Fraction(4), 0, 1e-11)
    first, _ = density_integral(Fraction(4), 1, 1e-11)
    assert abs(mass - 1) > 0.7
    assert abs(first / mass - 1) > 2.9
    assert max(1 - 1 / Fraction(1), Fraction(0)) == 0
    result = {"status": "numerical quadrature and exact arithmetic checks, not a formal proof",
              "quadrature_tolerance": 1e-11, "acceptance_scaled_error": 1e-8,
              "quadrature_moments": 165, "exact_recurrence_checks": exact_checks,
              "refinement_checks": refinements, "results": records,
              "incorrect_normalization_controls_rejected": 2}
    (Path(__file__).parent / "results" / "mp-density.json").write_text(json.dumps(result, indent=2) + "\n")
    worst = max(row["scaled_absolute_error"] for entry in records for row in entry["moments"])
    print(f"PASS: 165 density moment integrals over 15 positive aspect ratios; "
          f"450 exact recurrence checks; 12 quadrature refinements; "
          f"2 incorrect normalization controls; maximum scaled quadrature error {worst:.3g}")


if __name__ == "__main__":
    main()
