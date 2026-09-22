import Verification.PartialRevealMoments

/-! # The coefficient path xi=(1+3t^2)/4, eta=t^3 -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

private theorem integral_prefix_linear (t : I) (a b : ℝ) :
    (∫ u in Iic t, a-b*(u : ℝ)) = a*(t : ℝ)-b*(t : ℝ)^2/2 := by
  rw [Copula.integral_unit_Iic (fun u => a-b*u)]
  have hd (u : ℝ) : HasDerivAt (fun u => a*u-b*u^2/2) (a-b*u) u := by
    convert! (((hasDerivAt_id u).const_mul a).sub (((hasDerivAt_id u).pow 2).const_mul b |>.div_const 2)) using 1
    simp only [id_eq,Nat.cast_ofNat,Nat.add_one_sub_one,pow_one]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((show Continuous (fun u : ℝ => a-b*u) by fun_prop).intervalIntegrable _ _)]
  ring

private theorem integral_revealed_squares (t : I) :
    (∫ u : I, if u ≤ t then (1+(t : ℝ))/2-(u : ℝ) else 1/2-(1/4)*(u : ℝ)) = 3/8+(t : ℝ)^2/8 := by
  have hf : Integrable (fun u : I => (1+(t : ℝ))/2-(u : ℝ)) := Copula.integrable_continuous_unit volume (by fun_prop)
  have hg : Integrable (fun u : I => 1/2-(1/4)*(u : ℝ)) := Copula.integrable_continuous_unit volume (by fun_prop)
  have hgfull : (∫ u : I, 1/2-(1/4)*(u : ℝ)) = 3/8 := by
    rw [integral_sub (integrable_const _) ((Copula.integrable_continuous_unit volume continuous_subtype_val).const_mul _),
      integral_const_mul,Copula.integral_unit_id]
    norm_num
  have hgparts := integral_add_compl (s := Iic t) measurableSet_Iic hg
  rw [integral_prefix_linear,hgfull] at hgparts
  change (∫ u : I, (Iic t).piecewise (fun u => (1+(t : ℝ))/2-(u : ℝ)) (fun u => 1/2-(1/4)*(u : ℝ)) u) = _
  rw [integral_piecewise measurableSet_Iic hf.integrableOn hg.integrableOn]
  have hfp : (∫ u in Iic t, (1+(t : ℝ))/2-(u : ℝ)) = (t : ℝ)/2 := by
    have h := integral_prefix_linear t ((1+(t : ℝ))/2) 1
    simpa only [one_mul] using h.trans (by ring)
  rw [hfp]
  linarith only [hgparts]

theorem partialReveal_xi (t : I) : (partialReveal t).chatterjeeXi = (1+3*(t : ℝ)^2)/4 := by
  have he (v : I) : (∫ u : I, (partialReveal t).conditionalCDF u v^2) =
      ∫ u : I, partialRevealKernel t v u^2 := by
    apply integral_congr_ae
    filter_upwards [partialReveal_conditionalCDF t v] with u hu
    rw [hu]
  have hi : Integrable (fun p : I × I => partialRevealKernel t p.1 p.2^2)
      ((volume : Measure I).prod volume) := by
    refine (integrable_const (1 : ℝ)).mono' ((partialRevealKernel_measurable t).pow_const 2).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have h := partialRevealKernel_mem t p.1 p.2
      nlinarith [h.1,h.2]
  unfold Copula.chatterjeeXi
  simp_rw [he]
  rw [integral_integral_swap hi]
  simp_rw [partialRevealKernel_response_square_integral]
  rw [integral_revealed_squares]
  ring

theorem partialReveal_correlationRatio (t : I) : correlationRatio (partialReveal t) = (t : ℝ)^3 := by
  have he : (fun u => (conditionalMean (partialReveal t) u-1/2)^2) =ᵐ[volume]
      (Iic t).indicator (fun u => ((u : ℝ)-(t : ℝ)/2)^2) := by
    filter_upwards [partialReveal_conditionalMean t] with u hu
    rw [hu]
    by_cases h : u ≤ t
    · rw [ite_eq_left h,indicator_of_mem (show u ∈ Iic t from h)]
      ring
    · rw [ite_eq_right h,indicator_of_notMem (show u ∉ Iic t from h)]
      ring
  rw [correlationRatio,integral_congr_ae he,integral_indicator measurableSet_Iic,
    Copula.integral_unit_Iic (fun u => (u-(t : ℝ)/2)^2)]
  have hd (u : ℝ) : HasDerivAt (fun u => (u-(t : ℝ)/2)^3/3) ((u-(t : ℝ)/2)^2) u := by
    convert! (((hasDerivAt_id u).sub_const ((t : ℝ)/2)).pow 3 |>.div_const 3) using 1
    simp only [id_eq,Nat.cast_ofNat,Nat.add_one_sub_one]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((show Continuous (fun u : ℝ => (u-(t : ℝ)/2)^2) by fun_prop).intervalIntegrable _ _)]
  ring

end Verification
