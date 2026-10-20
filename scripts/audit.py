"""Audit proof dependencies and reject false normalization, Narayana, bias and variance claims."""
from __future__ import annotations

import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main() -> None:
    result = subprocess.run(["scripts/lake.sh", "env", "lean", "RandomMatrix/Audit.lean"],
                            cwd=ROOT, capture_output=True, text=True, check=True)
    output = result.stdout + result.stderr
    expected = re.findall(r"^#print axioms (\S+)", (ROOT / "RandomMatrix/Audit.lean").read_text(), re.M)
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
    # Lean reports definitional equalities with a distinct zero-dependency message.
    found += [(name, "") for name in re.findall(
        r"'([^']+)' does not depend on any axioms", output)]
    if len(found) != len(expected) or {name for name, _ in found} != set(expected):
        raise RuntimeError("The audit did not report every requested declaration")
    for name, raw in found:
        extra = {value.strip() for value in raw.split(",") if value.strip()} - ALLOWED
        if extra:
            raise RuntimeError(f"Unexpected proof dependencies in {name}: {extra}")
    print(output, end="")
    dest = ROOT / "docs/validation"
    dest.mkdir(exist_ok=True)
    (dest / "axioms.log").write_text(output)

    moment_source = '''import RandomMatrix
open RandomMatrix
-- Deliberately wrong: the finite 1-by-1 second moment is 1, not 2.
example : average (fun ω : Fin 1 × Fin 1 → Bool =>
    normalizedMoment (signMatrix ω) 2) = 2 := by
  rw [expected_second_moment (by decide) (by decide)]
  norm_num
'''
    narayana_source = '''import RandomMatrix
open RandomMatrix
-- Deliberately wrong: the order-three leading coefficient with two blocks of each color is 3.
example : patternCoefficient 3 2 2 = 4 := by
  rw [patternCoefficient_narayana 3 2 2 (by decide) (by decide) (by decide)]
  norm_num
'''
    bias_source = '''import RandomMatrix
open RandomMatrix
-- Deliberately wrong: the finite bias cannot be discarded at dimensions 1-by-1.
example : |average (fun ω : Fin 1 × Fin 1 → Bool =>
    normalizedMoment (signMatrix ω) 2) - mpMoment 2 1| ≤ 0 := by
  rw [expected_second_moment (by decide) (by decide), mpMoment_two]
  norm_num
'''
    variance_source = '''import RandomMatrix
open RandomMatrix
-- Deliberately wrong: a fair sign has variance one, not zero.
example : finiteVariance sign = 0 := by
  rw [finiteVariance_sign]
  norm_num
'''
    controls = [
        ("NegativeControl", "negative-control.log", moment_source),
        ("NarayanaNegativeControl", "narayana-negative-control.log", narayana_source),
        ("FiniteBiasNegativeControl", "finite-bias-negative-control.log", bias_source),
        ("VarianceNegativeControl", "variance-negative-control.log", variance_source),
    ]
    for name, log_name, source in controls:
        negative = ROOT / ".lake" / f"{name}.lean"
        negative.write_text(source)
        try:
            rejected = subprocess.run(["scripts/lake.sh", "env", "lean", str(negative)],
                                      cwd=ROOT, capture_output=True, text=True)
        finally:
            negative.unlink()
        diagnosis = rejected.stdout + rejected.stderr
        if rejected.returncode == 0 or "unsolved goals" not in diagnosis:
            raise RuntimeError(f"{name} did not fail for the intended proof obligation: " + diagnosis)
        if any(term in diagnosis for term in ("unknownIdentifier", "does not exist", "unknown module")):
            raise RuntimeError(f"{name} failed because of infrastructure, not mathematics")
        (dest / log_name).write_text(source + "\nEXPECTED REJECTION:\n" + diagnosis)
    print(f"PASS: {len(found)} declaration dependency audits; "
          "incorrect finite second moment, Narayana coefficient, zero finite bias and zero sign variance rejected")



if __name__ == "__main__":
    main()
