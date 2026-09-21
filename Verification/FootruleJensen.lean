import Verification.FootruleOptimizer
import Verification.TwoBinProjection
import Verification.StochasticRhoEquality
import Copula.CDF.Bounds

/-! # Universal xi-footrule lower bounds from the two-bin relaxation

The relaxed profile is not asserted to be a copula. Its two rank-like
integrals give a lower bound on the weighted objective for every copula.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

noncomputable def conditionalBinLow (C : Copula 2) (v : I) : ℝ := C.cdf ![v, v] / (v : ℝ)
noncomputable def conditionalBinHigh (C : Copula 2) (v : I) : ℝ := ((v : ℝ) - C.cdf ![v, v]) / (1 - v)

theorem conditionalBin_feasible (C : Copula 2) (v : I) (hv : 0 < (v : ℝ) ∧ (v : ℝ) < 1) :
    conditionalBinLow C v ∈ Icc 0 1 ∧ conditionalBinHigh C v ∈ Icc 0 1 ∧
      (v : ℝ) * conditionalBinLow C v + (1 - v) * conditionalBinHigh C v = v := by
  have hd : 0 < 1 - (v : ℝ) := by linarith [hv.2]
  have hlo := C.cdf_nonneg ![v, v]
  have hhi : C.cdf ![v, v] ≤ (v : ℝ) := C.cdf_le_coord ![v, v] 0
  have hf : 2 * (v : ℝ) - 1 ≤ C.cdf ![v, v] := by
    have h := C.sum_sub_dim_add_one_le_cdf ![v, v]
    norm_num [Fin.sum_univ_two] at h
    linarith
  unfold conditionalBinLow conditionalBinHigh
  refine ⟨⟨div_nonneg hlo hv.1.le, (div_le_one hv.1).mpr hhi⟩,
    ⟨div_nonneg (sub_nonneg.mpr hhi) hd.le, (div_le_one hd).mpr (by linarith)⟩, ?_⟩
  field_simp [ne_of_gt hv.1, ne_of_gt hd]
  ring

theorem conditionalBin_left_mass (C : Copula 2) (v : I) (hv : 0 < (v : ℝ)) :
    (∫ u in Iic v, C.conditionalCDF u v) = (v : ℝ) * conditionalBinLow C v := by
  rw [← C.cdf_eq_integral_conditionalCDF]
  unfold conditionalBinLow
  field_simp

theorem conditionalBin_jensen (C : Copula 2) (v : I) (hv : 0 < (v : ℝ) ∧ (v : ℝ) < 1) :
    (v : ℝ) * conditionalBinLow C v ^ 2 + (1 - v) * conditionalBinHigh C v ^ 2 ≤
      ∫ u : I, C.conditionalCDF u v ^ 2 := by
  apply twoBin_jensen (C.integrable_conditionalCDF v) (C.integrable_conditionalCDF_sq v)
  · exact (C.integral_conditionalCDF v).trans (conditionalBin_feasible C v hv).2.2.symm
  · exact conditionalBin_left_mass C v hv.1

theorem conditionalBin_jensen_eq_iff (C : Copula 2) (v : I) (hv : 0 < (v : ℝ) ∧ (v : ℝ) < 1) :
    (∫ u : I, C.conditionalCDF u v ^ 2) =
      (v : ℝ) * conditionalBinLow C v ^ 2 + (1 - v) * conditionalBinHigh C v ^ 2 ↔
      (fun u => C.conditionalCDF u v) =ᵐ[volume]
        twoBin v (conditionalBinLow C v) (conditionalBinHigh C v) := by
  apply twoBin_jensen_eq_iff (C.integrable_conditionalCDF v) (C.integrable_conditionalCDF_sq v)
  · exact (C.integral_conditionalCDF v).trans (conditionalBin_feasible C v hv).2.2.symm
  · exact conditionalBin_left_mass C v hv.1

noncomputable def relaxedFootrule (μ : ℝ) : ℝ :=
  6 * (∫ v : I, (v : ℝ) * jensenLow μ v) - 2

noncomputable def relaxedXi (μ : ℝ) : ℝ :=
  6 * (∫ v : I, (v : ℝ) * jensenLow μ v ^ 2 + (1 - v) * jensenHigh μ v ^ 2) - 2

theorem integrable_jensen_diagonal (μ : ℝ) (hμ : μ ∈ Icc 0 2) :
    Integrable (fun v : I => (v : ℝ) * jensenLow μ v) := by
  apply integrable_unit_bounded (measurable_subtype_coe.mul (measurable_jensenLow μ))
  intro v
  have h := (jensen_feasible μ hμ v).1
  exact ⟨mul_nonneg v.property.1 h.1,
    (mul_le_mul_of_nonneg_left h.2 v.property.1).trans (by simpa using v.property.2)⟩

theorem integrable_jensen_square (μ : ℝ) (hμ : μ ∈ Icc 0 2) :
    Integrable (fun v : I => (v : ℝ) * jensenLow μ v ^ 2 + (1 - v) * jensenHigh μ v ^ 2) := by
  apply integrable_unit_bounded
    ((measurable_subtype_coe.mul ((measurable_jensenLow μ).pow_const 2)).add
      ((measurable_const.sub measurable_subtype_coe).mul ((measurable_jensenHigh μ).pow_const 2)))
  intro v
  obtain ⟨ha, hb, hm⟩ := jensen_feasible μ hμ v
  have hA : jensenLow μ v ^ 2 ≤ jensenLow μ v := by nlinarith [ha.1, ha.2]
  have hB : jensenHigh μ v ^ 2 ≤ jensenHigh μ v := by nlinarith [hb.1, hb.2]
  refine ⟨add_nonneg (mul_nonneg v.property.1 (sq_nonneg _))
    (mul_nonneg (sub_nonneg.mpr v.property.2) (sq_nonneg _)), ?_⟩
  have h := add_le_add (mul_le_mul_of_nonneg_left hA v.property.1)
    (mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr v.property.2))
  exact h.trans (by rw [hm]; exact v.property.2)

theorem conditional_objective_lower_bound (C : Copula 2) (μ : ℝ) (hμ : μ ∈ Icc 0 2)
    (v : I) (hv : 0 < (v : ℝ) ∧ (v : ℝ) < 1) :
    splitObjective μ v (jensenLow μ v) (jensenHigh μ v) ≤
      μ * C.cdf ![v, v] + ∫ u : I, C.conditionalCDF u v ^ 2 := by
  obtain ⟨ha, hb, hm⟩ := conditionalBin_feasible C v hv
  have ho := jensen_optimal μ hμ v (conditionalBinLow C v) (conditionalBinHigh C v) ha hb hm
  have hj := conditionalBin_jensen C v hv
  have hl := conditionalBin_left_mass C v hv.1
  rw [← C.cdf_eq_integral_conditionalCDF] at hl
  unfold splitObjective at ho ⊢
  have he : μ * (v : ℝ) * conditionalBinLow C v = μ * C.cdf ![v, v] := by rw [mul_assoc, ← hl]
  rw [he] at ho
  linarith

/-- Theorem 3.2, with the relaxed values defined by their exact integrals. -/
theorem xi_footrule_relaxed_lower_bound (C : Copula 2) (μ : ℝ) (hμ : μ ∈ Icc 0 2) :
    μ * relaxedFootrule μ + relaxedXi μ ≤ μ * C.spearmanFootrule + C.chatterjeeXi := by
  have hd := integrable_jensen_diagonal μ hμ
  have hq := integrable_jensen_square μ hμ
  have hl : Integrable (fun v : I => μ * ((v : ℝ) * jensenLow μ v) +
      ((v : ℝ) * jensenLow μ v ^ 2 + (1 - v) * jensenHigh μ v ^ 2)) := (hd.const_mul μ).add hq
  have hr : Integrable (fun v : I => μ * C.cdf ![v, v] + ∫ u : I, C.conditionalCDF u v ^ 2) :=
    (C.integrable_diagonal_cdf.const_mul μ).add C.integrable_integral_conditionalCDF_sq
  have h := integral_mono_ae hl hr (by
    filter_upwards [ae_unit_interior] with v hv
    simpa only [splitObjective, mul_assoc, add_assoc] using conditional_objective_lower_bound C μ hμ v hv)
  rw [integral_add (hd.const_mul μ) hq,
    integral_add (C.integrable_diagonal_cdf.const_mul μ) C.integrable_integral_conditionalCDF_sq,
    integral_const_mul, integral_const_mul] at h
  unfold relaxedFootrule relaxedXi Copula.spearmanFootrule Copula.chatterjeeXi
  nlinarith only [h]

/-- At a prescribed relaxed footrule value, the bound reduces to a xi bound. -/
theorem xi_lower_bound_at_relaxed_footrule (C : Copula 2) (μ : ℝ) (hμ : μ ∈ Icc 0 2)
    (hC : C.spearmanFootrule = relaxedFootrule μ) : relaxedXi μ ≤ C.chatterjeeXi := by
  have h := xi_footrule_relaxed_lower_bound C μ hμ
  rw [hC] at h
  linarith

end Verification
