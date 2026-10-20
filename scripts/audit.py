"""Audit proof dependencies and reject false moment and spectral convergence claims."""
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
    # All mathematical modules use the RandomMatrix namespace, with qualified
    # names for nested declarations. Keep exported helper lemmas in scope too.
    exported = {
        "RandomMatrix." + name
        for path in (ROOT / "RandomMatrix").glob("*.lean") if path.stem != "Audit"
        for name in re.findall(r"^(?:@\[[^\]]+\]\s+)?(?:theorem|lemma) ([\w.']+)",
                               path.read_text(), re.M)
    }
    missing = exported - set(expected)
    if missing:
        raise RuntimeError(f"Exported declarations missing from the audit: {sorted(missing)}")
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
    spectral_mass_source = '''import RandomMatrix
open RandomMatrix MeasureTheory
-- Deliberately wrong: the empirical zeroth moment is one, even with repeated eigenvalues.
example (X : Matrix (Fin 2) (Fin 1) ℝ) :
    ∫ x, x ^ 0 ∂empiricalMeasure X = 0 := by
  rw [empiricalMeasure_moment_zero (by decide)]
  norm_num
'''
    spectral_atom_source = '''import RandomMatrix
open RandomMatrix
-- Deliberately wrong: a two-by-one covariance matrix cannot have zero mass at zero.
example (X : Matrix (Fin 2) (Fin 1) ℝ) :
    (empiricalMeasure X {0}).toReal = 0 := by
  have h := empiricalMeasure_zero_atom_lower (by decide : 0 < 2) X
  norm_num at h
'''
    mp_mass_source = '''import RandomMatrix
open RandomMatrix MeasureTheory
-- Deliberately wrong: at gamma=2 the continuous density has mass 1/2, not 1.
example : (∫ x, mpDensity 2 x) = 1 := by
  rw [mpDensity_integral (by norm_num : (0 : ℝ) < 2)]
  norm_num
'''
    mp_moment_source = '''import RandomMatrix
open RandomMatrix MeasureTheory
-- Deliberately wrong: the MP second moment at gamma=2 is 3, not 2.
example : (∫ x, x ^ 2 ∂marchenkoPastur 2) = 2 := by
  rw [marchenkoPastur_moment 2 (by norm_num), mpMoment_two]
  norm_num
'''
    mp_critical_atom_source = '''import RandomMatrix
open RandomMatrix
-- Deliberately wrong: gamma=1 has no zero atom despite its density singularity.
example : (marchenkoPastur 1 {0}).toReal = 1 / 2 := by
  rw [marchenkoPastur_zero_atom_real]
  norm_num
'''
    first_moment_only_source = '''import RandomMatrix
open RandomMatrix MeasureTheory
open scoped ENNReal
-- Both laws below have mass one and first moment one. The bounded continuous
-- clipped identity distinguishes them, so the first moment alone is insufficient.
example :
    (∫ x : ℝ, min 1 (max 0 x) ∂((2 : ℝ≥0∞)⁻¹ •
      (Measure.dirac (0 : ℝ) + Measure.dirac 2))) =
    ∫ x : ℝ, min 1 (max 0 x) ∂Measure.dirac 1 := by
  have hmass : (((2 : ℝ≥0∞)⁻¹ • (Measure.dirac (0 : ℝ) + Measure.dirac 2)) :
      Measure ℝ) Set.univ = 1 := by
    simp only [Measure.smul_apply, smul_eq_mul, Measure.add_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), one_add_one_eq_two]
    exact ENNReal.inv_mul_cancel (by norm_num) (by simp)
  have hfirst : (∫ x : ℝ, x ∂((2 : ℝ≥0∞)⁻¹ •
      (Measure.dirac (0 : ℝ) + Measure.dirac 2))) = (1 : ℝ) := by
    rw [integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
      (integrable_dirac (by simp))]
    norm_num
  have hcontinuous : Continuous (fun x : ℝ => min 1 (max 0 x)) :=
    continuous_const.min (continuous_const.max continuous_id)
  have hbounded (x : ℝ) : |min 1 (max 0 x)| ≤ 1 := by
    rw [abs_of_nonneg (le_min (by norm_num) (le_max_left _ _))]
    exact min_le_left _ _
  rw [integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
    (integrable_dirac (by simp))]
  norm_num
'''
    weak_mass_source = '''import RandomMatrix
open RandomMatrix MeasureTheory
-- The bounded continuous constant-one test detects the missing atom at gamma=2.
example (X : Matrix (Fin 2) (Fin 1) ℝ) :
    (∫ _x : ℝ, (1 : ℝ) ∂empiricalMeasure X) = ∫ x : ℝ, mpDensity 2 x := by
  have hm : (∫ _x : ℝ, (1 : ℝ) ∂empiricalMeasure X) = 1 := by
    simpa only [pow_zero] using empiricalMeasure_moment_zero (by decide : 0 < 2) X
  rw [hm, mpDensity_integral (by norm_num : (0 : ℝ) < 2)]
  norm_num
'''
    controls = [
        ("NegativeControl", "negative-control.log", moment_source),
        ("NarayanaNegativeControl", "narayana-negative-control.log", narayana_source),
        ("FiniteBiasNegativeControl", "finite-bias-negative-control.log", bias_source),
        ("VarianceNegativeControl", "variance-negative-control.log", variance_source),
        ("SpectralMassNegativeControl", "spectral-mass-negative-control.log", spectral_mass_source),
        ("SpectralAtomNegativeControl", "spectral-atom-negative-control.log", spectral_atom_source),
        ("MPMassNegativeControl", "mp-mass-negative-control.log", mp_mass_source),
        ("MPMomentNegativeControl", "mp-moment-negative-control.log", mp_moment_source),
        ("MPCriticalAtomNegativeControl", "mp-critical-atom-negative-control.log", mp_critical_atom_source),
        ("FirstMomentOnlyNegativeControl", "first-moment-only-negative-control.log", first_moment_only_source),
        ("WeakMassNegativeControl", "weak-mass-negative-control.log", weak_mass_source),
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
        errors = re.findall(r"^.*?:\d+:\d+: error(?:\([^)]*\))?: (.*)$", diagnosis, re.M)
        if len(errors) != 1 or errors[0] != "unsolved goals":
            raise RuntimeError(f"{name} did not fail solely on its intended goal: " + diagnosis)
        (dest / log_name).write_text(source + "\nEXPECTED REJECTION:\n" + diagnosis)
    print(f"PASS: {len(found)} declaration dependency audits; "
          f"{len(controls)} incorrect moment, variance and spectral convergence claims rejected")



if __name__ == "__main__":
    main()
