import Papers.AnsariRockel2026XiRho.BandDensitySections
import Verification.BandCDFFormula

/-! # The corrected equation (19) and the journal's missing boundary term -/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.AnsariRockel2026XiRho

/-- The source dependence curves s_v and a_v. -/
noncomputable def sourceBandRoot (b : ℝ) (v : I) : ℝ := sourceBandIntercept b v/b
noncomputable def sourceBandLower (b : ℝ) (v : I) : ℝ := (sourceBandIntercept b v-1)/b

/-- A formula valid at every point, without case restrictions. -/
theorem sourceBand_cdf_positive_parts (b : ℝ) (hb : 0 < b) (u v : I) :
    (sourceBand b hb).cdf ![u,v] =
      (sourceBandIntercept b v^2-max 0 (sourceBandIntercept b v-b*(u : ℝ))^2-
        max 0 (sourceBandIntercept b v-1)^2+max 0 (sourceBandIntercept b v-1-b*(u : ℝ))^2)/(2*b) := by
  rw [sourceBand_cdf, integral_prefix_clamp hb, max_eq_right (sourceBandIntercept_mem hb v).1]

/-- Equation (19) in arXiv v3, including the correction at the left boundary. -/
theorem sourceBand_cdf_piecewise (b : ℝ) (hb : 0 < b) (u v : I) :
    (sourceBand b hb).cdf ![u,v] =
      if sourceBandLower b v < (u : ℝ) ∧ (u : ℝ) ≤ sourceBandRoot b v then
        (u : ℝ)-b/2*((u : ℝ)-sourceBandLower b v)^2+b/2*(min (sourceBandLower b v) 0)^2
      else min (u : ℝ) (v : ℝ) := by
  by_cases h : sourceBandLower b v < (u : ℝ) ∧ (u : ℝ) ≤ sourceBandRoot b v
  · rw [ite_eq_left h, sourceBand_cdf_positive_parts]
    have hl : sourceBandIntercept b v-1 < b*(u : ℝ) := by
      have := (div_lt_iff₀ hb).mp h.1; nlinarith only [this]
    have hu : b*(u : ℝ) ≤ sourceBandIntercept b v := by
      have := (le_div_iff₀ hb).mp h.2; nlinarith only [this]
    rw [max_eq_right (by linarith : 0 ≤ sourceBandIntercept b v-b*(u : ℝ)),
      max_eq_left (by linarith : sourceBandIntercept b v-1-b*(u : ℝ) ≤ 0)]
    unfold sourceBandLower
    by_cases ha : sourceBandIntercept b v-1 ≤ 0
    · rw [max_eq_left ha, min_eq_left (div_nonpos_of_nonpos_of_nonneg ha hb.le)]
      field_simp
      ring
    · rw [max_eq_right (by linarith), min_eq_right (div_nonneg (by linarith) hb.le)]
      field_simp
      ring
  · rw [ite_eq_right h]
    by_cases hl : (u : ℝ) ≤ sourceBandLower b v
    · have he : (sourceBand b hb).cdf ![u,v] = (u : ℝ) := by
        rw [sourceBand_cdf]
        have hk : EqOn (fun t : I => unitClamp (sourceBandIntercept b v-b*(t : ℝ))) (fun _ => (1 : ℝ)) (Iic u) := by
          intro t ht
          have ht' : (t : ℝ) ≤ u := ht
          have hh := (le_div_iff₀ hb).mp hl
          change min 1 (max 0 (sourceBandIntercept b v-b*(t : ℝ))) = 1
          rw [max_eq_right (by nlinarith), min_eq_left (by nlinarith)]
        rw [setIntegral_congr_fun measurableSet_Iic hk, Copula.integral_unit_Iic (fun _ => (1 : ℝ))]
        simp
      have hv := (sourceBand b hb).cdf_le_coord ![u,v] 1
      change (sourceBand b hb).cdf ![u,v] ≤ (v : ℝ) at hv
      rw [he] at hv
      rw [he, min_eq_left hv]
    · have hu : sourceBandRoot b v < (u : ℝ) := lt_of_not_ge (fun hh => h ⟨lt_of_not_ge hl, hh⟩)
      have he : (sourceBand b hb).cdf ![u,v] = (v : ℝ) := by
        rw [sourceBand_cdf, setIntegral_eq_integral_of_forall_compl_eq_zero]
        · exact sourceBandIntercept_mean hb v
        · intro t ht
          have ht' : (u : ℝ) ≤ t := le_of_lt (lt_of_not_ge ht)
          have hh := (div_lt_iff₀ hb).mp hu
          unfold unitClamp
          rw [max_eq_left (by nlinarith)]
          norm_num
      have hv := (sourceBand b hb).cdf_le_coord ![u,v] 0
      change (sourceBand b hb).cdf ![u,v] ≤ (u : ℝ) at hv
      rw [he] at hv
      rw [he, min_eq_right hv]

/-- Literal journal equation (19), before arXiv v3 added the boundary term. -/
noncomputable def journalBandExpression (b : ℝ) (u v : I) : ℝ :=
  if sourceBandLower b v < (u : ℝ) ∧ (u : ℝ) ≤ sourceBandRoot b v then
    (u : ℝ)-b/2*((u : ℝ)-sourceBandLower b v)^2 else min (u : ℝ) (v : ℝ)

/-- A negative boundary value certifies the omitted term is mathematically necessary. -/
theorem journalBandExpression_negative :
    journalBandExpression 1 0 ⟨1/8, by norm_num⟩ = -(1/8 : ℝ) := by
  have hs : Real.sqrt (1/4 : ℝ) = 1/2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]; norm_num
  norm_num [journalBandExpression, sourceBandLower, sourceBandRoot, sourceBandIntercept, bandCut, hs]

/-- The literal uncorrected journal expression cannot be any copula CDF. -/
theorem journalBandExpression_not_copula :
    ¬ ∃ C : Copula 2, ∀ u v : I, C.cdf ![u,v] = journalBandExpression 1 u v := by
  rintro ⟨C,h⟩
  have hn := C.cdf_nonneg ![0,⟨1/8,by norm_num⟩]
  rw [h, journalBandExpression_negative] at hn
  norm_num at hn

end Papers.AnsariRockel2026XiRho
