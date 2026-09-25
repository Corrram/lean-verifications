import Copula.Families.MarshallOlkin
import Verification.MTP2ConditionalIncreasing

/-! # Remaining mapping rows: Cuadras–Augé CDF and endpoints, Marshall–Olkin endpoint,
and the TP2 ⇒ CI implication -/

open ProbabilityTheory Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

/-- Table 1: the Cuadras–Augé CDF `min(u,v)·max(u,v)^(1-δ)` on the closed square. -/
theorem cuadrasAuge_cdf (δ u v : I) :
    (cuadrasAuge δ).cdf ![u, v] = min (u : ℝ) v * max (u : ℝ) v ^ (1 - (δ : ℝ)) := by
  rw [cuadrasAuge, cdf_marshallOlkin]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hu := u.2.1; have hv := v.2.1
  have hδ := δ.2.1; have hδ1 := δ.2.2
  have hsum : (δ : ℝ) + (1 - (δ : ℝ)) ≠ 0 := by norm_num
  rcases le_total (u : ℝ) v with h | h
  · rw [min_eq_left (Real.rpow_le_rpow hu h hδ), min_eq_left h, max_eq_right h, ← mul_assoc,
      ← Real.rpow_add' hu hsum, show (δ : ℝ) + (1 - (δ : ℝ)) = 1 by ring, Real.rpow_one]
  · rw [min_eq_right (Real.rpow_le_rpow hv h hδ), min_eq_right h, max_eq_left h,
      show (v : ℝ) ^ (δ : ℝ) * ((u : ℝ) ^ (1 - (δ : ℝ)) * (v : ℝ) ^ (1 - (δ : ℝ))) =
        ((v : ℝ) ^ (δ : ℝ) * (v : ℝ) ^ (1 - (δ : ℝ))) * (u : ℝ) ^ (1 - (δ : ℝ)) by ring,
      ← Real.rpow_add' hv hsum, show (δ : ℝ) + (1 - (δ : ℝ)) = 1 by ring, Real.rpow_one]

/-- Table 4: Cuadras–Augé at `δ=1` is the comonotonic copula `M`. -/
theorem cuadrasAuge_one : cuadrasAuge 1 = comonotonic 2 := marshallOlkin_one_one

/-- Table 4: Cuadras–Augé at `δ=0` is independence. -/
theorem cuadrasAuge_zero : cuadrasAuge 0 = independence 2 := marshallOlkin_zero_zero

/-- Table 4: Marshall–Olkin with both weights one is `M`. -/
theorem marshallOlkin_one_one_eq : marshallOlkin 1 1 = comonotonic 2 := marshallOlkin_one_one

/-- Table 4: equal Marshall–Olkin weights give the Cuadras–Augé subfamily. -/
theorem marshallOlkin_diag (δ : I) : marshallOlkin δ δ = cuadrasAuge δ := rfl

/-- Section 2: a TP2 (MTP2) Lebesgue density implies conditional increasingness. -/
theorem mtp2_density_isCI {C : Copula 2} (h : C.HasMTP2Density) : C.IsCI :=
  Verification.mtp2_isCI h

end Papers.AnsariRockel2024
