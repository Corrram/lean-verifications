import Verification.ConditionalRatioBound

/-! # A uniform quantitative improvement of eta <= 2 xi -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

private theorem scalar_gap {m g : ℝ} (hm : 0 ≤ m) (hg : g ≤ 1/10) :
    m^2/2-1/100 ≤ (g-m)^2 := by
  by_cases h : g ≤ 0
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg h hm, sq_nonneg g]
  · nlinarith [sq_nonneg (m-2*g)]

/-- The endpoint bounds of a CDF force a positive square-error contribution. -/
theorem cdf_centered_quantitative_gap (C : Copula 2) (t : I) :
    (21/20 : ℝ)*(∫ u : I, C.conditionalCDF t u-(u : ℝ))^2 ≤
      (∫ u : I, (C.conditionalCDF t u-(u : ℝ))^2)+1/1000 := by
  let g (u : I) := C.conditionalCDF t u-(u : ℝ)
  let m := ∫ u : I, g u
  have hi := (centered_section C t).1
  have hsq := (centered_section C t).2
  have hg : Integrable (fun u => (g u-m)^2) := by
    have he : (fun u => (g u-m)^2) = fun u => g u^2-2*m*g u+m^2 := by funext u; ring
    rw [he]
    exact (hsq.sub (hi.const_mul (2*m))).add (integrable_const _)
  have hn : ∀ u, 0 ≤ (g u-m)^2 := fun u => sq_nonneg _
  have hstrip : (1/10 : ℝ)*(m^2/2-1/100) ≤ ∫ u : I, (g u-m)^2 := by
    by_cases hm : 0 ≤ m
    · let q : I := ⟨9/10,by norm_num⟩
      have hpoint : ∀ u ∈ Ici q, m^2/2-1/100 ≤ (g u-m)^2 := by
        intro u hu
        apply scalar_gap hm
        have hu' : (9/10 : ℝ) ≤ u := hu
        dsimp [g]
        linarith [C.conditionalCDF_le_one t u]
      have h := setIntegral_mono_on (integrable_const (m^2/2-1/100)).integrableOn hg.integrableOn measurableSet_Ici hpoint
      have hv : (volume : Measure I).real (Ici q) = 1/10 := by
        rw [Measure.real, unitInterval.volume_Ici]
        norm_num [q]
      simp only [setIntegral_const, smul_eq_mul, hv] at h
      exact h.trans (setIntegral_le_integral hg (Filter.Eventually.of_forall hn))
    · let q : I := ⟨1/10,by norm_num⟩
      have hpoint : ∀ u ∈ Iic q, m^2/2-1/100 ≤ (g u-m)^2 := by
        intro u hu
        have hu' : (u : ℝ) ≤ 1/10 := hu
        have hb : -g u ≤ 1/10 := by dsimp [g]; linarith [C.conditionalCDF_nonneg t u]
        have h := scalar_gap (m := -m) (g := -g u) (by linarith) hb
        nlinarith only [h]
      have h := setIntegral_mono_on (integrable_const (m^2/2-1/100)).integrableOn hg.integrableOn measurableSet_Iic hpoint
      have hv : (volume : Measure I).real (Iic q) = 1/10 := by
        rw [Measure.real, unitInterval.volume_Iic]
        norm_num [q]
      simp only [setIntegral_const, smul_eq_mul, hv] at h
      exact h.trans (setIntegral_le_integral hg (Filter.Eventually.of_forall hn))
  have he := centered_square_identity hi hsq
  change (∫ u : I, (g u-m)^2) = (∫ u : I, g u^2)-m^2 at he
  change (21/20 : ℝ)*m^2 ≤ (∫ u : I, g u^2)+1/1000
  linarith only [hstrip, he]

/-- This estimate separates every xi=1/4 copula uniformly from eta=1/2. -/
theorem correlationRatio_quantitative_bound (C : Copula 2) :
    (21/20 : ℝ)*correlationRatio C ≤ 2*C.chatterjeeXi+3/250 := by
  have hb (t : I) : (21/20 : ℝ)*(conditionalMean C t-1/2)^2 ≤
      (∫ u : I, (C.conditionalCDF t u-(u : ℝ))^2)+1/1000 := by
    have h := cdf_centered_quantitative_gap C t
    rw [centered_mean] at h
    nlinarith only [h]
  have hm : Measurable (fun t : I => conditionalMean C t) := by
    simp_rw [conditionalMean_eq]
    exact measurable_const.sub C.measurable_conditionalCDF.stronglyMeasurable.integral_prod_left.measurable
  have hi : Integrable (fun t : I => (conditionalMean C t-1/2)^2) := by
    refine ((centered_sq_integrable C).integral_prod_right.add (integrable_const (1/1000 : ℝ))).mono'
      ((hm.sub measurable_const).pow_const 2).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      change (conditionalMean C t-1/2)^2 ≤ (∫ u : I, (C.conditionalCDF t u-(u : ℝ))^2)+1/1000
      have h := hb t
      nlinarith [sq_nonneg (conditionalMean C t-1/2)]
  have h := integral_mono (hi.const_mul (21/20 : ℝ))
    ((centered_sq_integrable C).integral_prod_right.add (integrable_const (1/1000 : ℝ))) hb
  dsimp only [Pi.add_apply, Prod.fst, Prod.snd] at h
  rw [integral_const_mul, integral_add (centered_sq_integrable C).integral_prod_right (integrable_const _)] at h
  rw [← integral_integral_swap (centered_sq_integrable C)] at h
  norm_num only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  rw [correlationRatio, C.chatterjeeXi_eq_integral_centered_sq]
  linarith only [h]

end Verification
