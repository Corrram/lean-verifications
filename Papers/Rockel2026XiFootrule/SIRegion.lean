import Papers.Rockel2026XiFootrule.UpperBoundary
import Verification.StochasticBounds
import Verification.Mixture
import Verification.TauFootrule
import Copula.OrdinalSum.Rank

/-! # The exact xi-footrule region for stochastically increasing copulas

A single independence block below a comonotonic block attains the lower
boundary. Mixtures with the Frechet upper boundary fill every fixed-footrule
interval. All constructions include their endpoints.
-/

open MeasureTheory ProbabilityTheory Set Verification
open Copula.OrdinalSum
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule

noncomputable def diagonalBoundary (a : I) : Copula 2 :=
  (Copula.independence 2).ordinalSum (Copula.comonotonic 2) a

theorem diagonalBoundary_cdf (a u v : I) :
    (diagonalBoundary a).cdf ![u, v] =
      if v ≤ a then ((v : ℝ) / a) * min (u : ℝ) a else min (u : ℝ) v := by
  by_cases ha : a = 0
  · subst a
    by_cases hv : v ≤ 0
    · have he : v = 0 := le_antisymm hv v.property.1
      simp [diagonalBoundary, he]
    · simp only [diagonalBoundary, Copula.ordinalSum_zero, Copula.cdf_comonotonic_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, ite_eq_right hv]
  have ha0 : 0 < a := lt_of_le_of_ne a.property.1 (Ne.symm ha)
  have ha' : (a : ℝ) ≠ 0 := ne_of_gt ha0
  by_cases hv : v ≤ a
  · rw [ite_eq_left hv]
    by_cases hu : u ≤ a
    · rw [diagonalBoundary, Copula.cdf_ordinalSum_lower _ _ _ _ _ hu hv]
      simp only [Copula.cdf_independence, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, coe_lowerCoord_of_le a u ha0 hu,
        coe_lowerCoord_of_le a v ha0 hv, min_eq_left (show (u : ℝ) ≤ a from hu)]
      field_simp
    · rw [diagonalBoundary, Copula.cdf_ordinalSum_upper_lower _ _ _ _ _
        (le_of_not_ge hu) hv, min_eq_right (show (a : ℝ) ≤ u from le_of_not_ge hu)]
      field_simp
  · rw [ite_eq_right hv]
    have hav : a ≤ v := le_of_not_ge hv
    by_cases hu : u ≤ a
    · rw [diagonalBoundary, Copula.cdf_ordinalSum_lower_upper _ _ _ _ _ hu hav,
        min_eq_left (show (u : ℝ) ≤ v from hu.trans hav)]
    · have hau : a ≤ u := le_of_not_ge hu
      rw [diagonalBoundary, Copula.cdf_ordinalSum_upper _ _ _ _ _ hau hav,
        Copula.cdf_comonotonic_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rcases le_total u v with huv | hvu
      · rw [min_eq_left (show (upperCoord a u : ℝ) ≤ upperCoord a v from
          upperCoord_mono a huv), weight_upperCoord,
          max_eq_right (sub_nonneg.mpr (show (a : ℝ) ≤ u from hau)),
          min_eq_left (show (u : ℝ) ≤ v from huv)]
        ring
      · rw [min_eq_right (show (upperCoord a v : ℝ) ≤ upperCoord a u from
          upperCoord_mono a hvu), weight_upperCoord,
          max_eq_right (sub_nonneg.mpr (show (a : ℝ) ≤ v from hav)),
          min_eq_right (show (v : ℝ) ≤ u from hvu)]
        ring

noncomputable def diagonalConditional (a v u : I) : ℝ :=
  if v ≤ a then ((v : ℝ) / a) * lowerStep a u else lowerStep v u

private theorem lowerStep_antitone (a : I) : Antitone (lowerStep a) := by
  intro u v huv
  by_cases hv : v ≤ a
  · simp [lowerStep, hv, huv.trans hv]
  · by_cases hu : u ≤ a <;> simp [lowerStep, hv, hu]

private theorem diagonalConditional_antitone (a v : I) : Antitone (diagonalConditional a v) := by
  unfold diagonalConditional
  by_cases hv : v ≤ a
  · simpa only [ite_eq_left hv] using
      (lowerStep_antitone a).const_mul (div_nonneg v.property.1 a.property.1)
  · simpa only [ite_eq_right hv] using lowerStep_antitone v

private theorem diagonalConditional_integrable (a v : I) : Integrable (diagonalConditional a v) := by
  unfold diagonalConditional
  by_cases hv : v ≤ a
  · simpa only [ite_eq_left hv] using
      (integrable_lowerStep a).const_mul ((v : ℝ) / a)
  · simpa only [ite_eq_right hv] using integrable_lowerStep v

private theorem diagonalConditional_nonneg (a v u : I) : 0 ≤ diagonalConditional a v u := by
  unfold diagonalConditional lowerStep
  split_ifs <;> simp only [mul_one, mul_zero, le_refl, zero_le_one]
  exact div_nonneg v.property.1 a.property.1

theorem diagonalConditional_primitive (a u v : I) :
    (∫ t in Iic u, diagonalConditional a v t) = (diagonalBoundary a).cdf ![u, v] := by
  rw [diagonalBoundary_cdf]
  by_cases hv : v ≤ a
  · simp only [diagonalConditional, ite_eq_left hv, integral_const_mul, integral_lowerStep]
  · simp only [diagonalConditional, ite_eq_right hv, integral_lowerStep]

theorem diagonalBoundary_isSI (a : I) : (diagonalBoundary a).IsSI := by
  intro u v w z huv hvw
  simp_rw [← diagonalConditional_primitive]
  exact Copula.integral_Iic_concave_of_antitone (diagonalConditional_integrable a z)
    (diagonalConditional_antitone a z) u v w huv hvw

theorem diagonalBoundary_conditionalCDF (a v : I) :
    (fun u => (diagonalBoundary a).conditionalCDF u v) =ᵐ[volume] diagonalConditional a v :=
  Copula.conditionalCDF_ae_eq_of_integral _ _ (diagonalConditional_integrable a v)
    (diagonalConditional_nonneg a v) (fun u => diagonalConditional_primitive a u v)

private theorem integral_lowerStep_univ (a : I) : (∫ u : I, lowerStep a u) = (a : ℝ) := by
  have h := integral_lowerStep a 1
  have he : Iic (1 : I) = univ := by ext u; simp [unitInterval.le_one']
  rw [he, setIntegral_univ] at h
  change (∫ u : I, lowerStep a u) = min (1 : ℝ) a at h
  simpa only [min_eq_right a.property.2] using h

theorem diagonalConditional_sq_integral (a v : I) :
    (∫ u : I, diagonalConditional a v u ^ 2) = (diagonalBoundary a).cdf ![v, v] := by
  have hs (b u : I) : lowerStep b u ^ 2 = lowerStep b u := by
    unfold lowerStep; split_ifs <;> norm_num
  rw [diagonalBoundary_cdf]
  by_cases hv : v ≤ a
  · simp only [diagonalConditional, ite_eq_left hv, mul_pow, hs, integral_const_mul,
      integral_lowerStep_univ, min_eq_left (show (v : ℝ) ≤ a from hv)]
    by_cases ha : (a : ℝ) = 0
    · simp [ha]
    · field_simp
  · simp only [diagonalConditional, ite_eq_right hv, hs, integral_lowerStep_univ, min_self]

theorem diagonalBoundary_xi_eq_footrule (a : I) :
    (diagonalBoundary a).chatterjeeXi = (diagonalBoundary a).spearmanFootrule := by
  unfold Copula.chatterjeeXi Copula.spearmanFootrule
  congr 2
  apply integral_congr_ae
  filter_upwards [] with v
  calc
    _ = ∫ u : I, diagonalConditional a v u ^ 2 :=
      integral_congr_ae ((diagonalBoundary_conditionalCDF a v).fun_comp (fun z : ℝ => z ^ 2))
    _ = _ := diagonalConditional_sq_integral a v

theorem diagonalBoundary_coefficients (a : I) :
    (diagonalBoundary a).chatterjeeXi = 1 - (a : ℝ) ^ 2 ∧
      (diagonalBoundary a).spearmanFootrule = 1 - (a : ℝ) ^ 2 := by
  have hf : (diagonalBoundary a).spearmanFootrule = 1 - (a : ℝ) ^ 2 := by
    simp only [diagonalBoundary, Copula.spearmanFootrule_ordinalSum,
      Copula.spearmanFootrule_independence, Copula.spearmanFootrule_comonotonic]
    ring
  exact ⟨(diagonalBoundary_xi_eq_footrule a).trans hf, hf⟩

theorem si_xi_le_footrule (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi ≤ C.spearmanFootrule := xi_le_footrule_of_isSI C hC

theorem upperBoundary_isSI (a : I) : (upperBoundary a).IsSI :=
  Copula.isSI_comonotonic.mix Copula.isSI_independence a

theorem exact_si_xi_footrule_region (x y : ℝ) :
    (∃ C : Copula 2, C.IsSI ∧ C.chatterjeeXi = x ∧ C.spearmanFootrule = y) ↔
      x ∈ Icc 0 1 ∧ y ∈ Icc 0 1 ∧ x ≤ y ∧ y ≤ Real.sqrt x := by
  constructor
  · rintro ⟨C, hC, rfl, rfl⟩
    have h := si_xi_le_footrule C hC
    exact ⟨C.chatterjeeXi_mem_Icc, ⟨C.chatterjeeXi_nonneg.trans h,
      C.spearmanFootrule_mem_Icc.2⟩, h, footrule_le_sqrt_xi C⟩
  · rintro ⟨hx, hy, hxy, hyx⟩
    let a : I := ⟨Real.sqrt (1 - y), Real.sqrt_nonneg _,
      (Real.sqrt_le_one).mpr (by linarith [hy.1])⟩
    let b : I := ⟨y, hy⟩
    have ha : 1 - (a : ℝ) ^ 2 = y := by
      dsimp [a]
      rw [Real.sq_sqrt (by linarith [hy.2])]
      ring
    have hd := diagonalBoundary_coefficients a
    rw [ha] at hd
    have hy2 : y ^ 2 ≤ x := by
      have hs := Real.sq_sqrt hx.1
      nlinarith [Real.sqrt_nonneg x]
    obtain ⟨t, ht⟩ := exists_unitInterval_eq
      (continuous_xi_mix (diagonalBoundary a) (upperBoundary b))
      (by simpa [xi_upperBoundary, b] using hy2)
      (by simpa [hd.1] using hxy)
    refine ⟨(diagonalBoundary a).mix (upperBoundary b) t,
      (diagonalBoundary_isSI a).mix (upperBoundary_isSI b) t, ht, ?_⟩
    rw [Copula.spearmanFootrule_mix, hd.2, footrule_upperBoundary]
    change (t : ℝ) * y + (1 - (t : ℝ)) * y = y
    ring

theorem si_xi_le_three_quarters_tau (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi ≤ 3 / 4 * C.kendallTau + 1 / 4 := by
  have h := si_xi_le_footrule C hC
  have ht := tau_footrule_lower C
  linarith

end Papers.Rockel2026XiFootrule
