import Verification.PartialRevealKernel
import Verification.FoldedUniformRank

/-! # Conditional moments along the central-revelation family -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

private theorem response_indicator_integrable (r : ℝ) :
    Integrable (fun v : I => if r ≤ (v : ℝ) then (1 : ℝ) else 0) := by
  refine (integrable_const (1 : ℝ)).mono'
    ((measurable_const.ite (measurableSet_le measurable_const measurable_subtype_coe) measurable_const).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun v => by split_ifs <;> norm_num

private theorem response_indicator_integral {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    (∫ v : I, if r ≤ (v : ℝ) then (1 : ℝ) else 0) = 1-r :=
  Copula.integral_unit_upper_indicator ⟨r,hr⟩

private theorem response_indicator_square_integral {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    (∫ v : I, (if r ≤ (v : ℝ) then (1 : ℝ) else 0)^2) = 1-r := by
  have he (v : I) : (if r ≤ (v : ℝ) then (1 : ℝ) else 0)^2 = (if r ≤ (v : ℝ) then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  simp_rw [he]
  exact response_indicator_integral hr

theorem foldKernel_response_square_integral (u : I) :
    (∫ v : I, foldKernel v u^2) = 1/2-(1/4)*(u : ℝ) := by
  have he (v : I) : foldKernel v u^2 =
      (if foldLower u ≤ v then (1 : ℝ) else 0)/4+3*(if foldUpper u ≤ v then 1 else 0)/4 := by
    have hh : foldLower u ≤ foldUpper u := by
      change (1-(u : ℝ))/2 ≤ (1+(u : ℝ))/2
      linarith [u.property.1]
    unfold foldKernel
    split_ifs
    all_goals norm_num at *
    all_goals order
  simp_rw [he]
  have hi (a : I) : Integrable (fun v : I => if a ≤ v then (1 : ℝ) else 0) := response_indicator_integrable a
  rw [integral_add ((hi (foldLower u)).div_const 4) (((hi (foldUpper u)).const_mul 3).div_const 4),
    integral_div,integral_div,integral_const_mul,Copula.integral_unit_upper_indicator,Copula.integral_unit_upper_indicator]
  dsimp [foldLower,foldUpper]
  ring

private theorem centralResponse_mem (t u : I) (hu : u ≤ t) :
    (1-(t : ℝ))/2+(u : ℝ) ∈ Icc (0 : ℝ) 1 := by
  have h : (u : ℝ) ≤ t := hu
  constructor <;> linarith [u.property.1,t.property.2]

theorem partialRevealKernel_response_integral (t u : I) :
    (∫ v : I, partialRevealKernel t v u) =
      if u ≤ t then 1-((1-(t : ℝ))/2+(u : ℝ)) else 1/2 := by
  by_cases hu : u ≤ t
  · simp only [partialRevealKernel,hu,ite_true]
    exact response_indicator_integral (centralResponse_mem t u hu)
  · simp only [partialRevealKernel,hu,ite_false]
    exact foldKernel_response_integral u

theorem partialRevealKernel_response_square_integral (t u : I) :
    (∫ v : I, partialRevealKernel t v u^2) =
      if u ≤ t then (1+(t : ℝ))/2-(u : ℝ) else 1/2-(1/4)*(u : ℝ) := by
  by_cases hu : u ≤ t
  · simp only [partialRevealKernel,hu,ite_true]
    rw [response_indicator_square_integral (centralResponse_mem t u hu)]
    ring
  · simp only [partialRevealKernel,hu,ite_false]
    exact foldKernel_response_square_integral u

theorem partialReveal_conditionalMean (t : I) :
    conditionalMean (partialReveal t) =ᵐ[volume]
      fun u => if u ≤ t then (1-(t : ℝ))/2+(u : ℝ) else 1/2 := by
  have ha : ∀ᵐ u : I, ∀ᵐ v : I, (partialReveal t).conditionalCDF u v = partialRevealKernel t v u :=
    (Measure.ae_ae_comm (μ := (volume : Measure I)) (ν := (volume : Measure I))
      (p := fun v u : I => (partialReveal t).conditionalCDF u v = partialRevealKernel t v u)
      (measurableSet_eq_fun (partialReveal t).measurable_conditionalCDF (partialRevealKernel_measurable t))).mp
      (Filter.Eventually.of_forall (partialReveal_conditionalCDF t))
  filter_upwards [ha] with u hu
  rw [conditionalMean_eq,integral_congr_ae hu,partialRevealKernel_response_integral]
  split_ifs <;> ring

end Verification
