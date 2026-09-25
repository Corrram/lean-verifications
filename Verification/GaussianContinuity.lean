import Verification.GaussianRepresentation
import Verification.GaussianReflection
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open ProbabilityTheory MeasureTheory Set Copula Filter
open scoped unitInterval Topology

namespace Verification

noncomputable def gaussianSample (r : ℝ) (x : Fin 2 → ℝ) : Fin 2 → I :=
  ![cdfUnit (gaussianReal 0 1) (x 0),
    cdfUnit (gaussianReal 0 1) (r*x 0+Real.sqrt (1-r^2)*x 1)]

theorem measurable_gaussianSample (r : ℝ) : Measurable (gaussianSample r) := by
  unfold gaussianSample
  fun_prop

theorem gaussianBivariate_cdf_sample {r : ℝ} (hr : r∈Icc (-1) 1) (u : Fin 2 → I) :
    (gaussianBivariate r hr).cdf u=
      ∫ x, (Iic u).indicator (fun _ => (1:ℝ)) (gaussianSample r x)
        ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 1) := by
  rw [Copula.cdf,gaussianBivariate_toMeasure_independent hr]
  change ((Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).map (gaussianSample r)).real (Iic u)=_
  rw [← integral_indicator_one measurableSet_Iic]
  change (∫ y, (Iic u).indicator (fun _ => (1:ℝ)) y
    ∂(Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).map (gaussianSample r))=_
  rw [integral_map (measurable_gaussianSample r).aemeasurable
      ((measurable_const.indicator measurableSet_Iic).aestronglyMeasurable)]

theorem gaussianBivariate_sample_integral_continuousAt {r : ℝ} (hr : r∈Icc (-1) 1)
    (u : Fin 2 → I) :
    ContinuousAt (fun s : ℝ => ∫ x, (Iic u).indicator (fun _ => (1:ℝ)) (gaussianSample s x)
      ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) r := by
  let μ := Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)
  let F := fun s x => (Iic u).indicator (fun _ => (1:ℝ)) (gaussianSample s x)
  have hm (s : ℝ) : Measurable (F s) :=
    (measurable_const.indicator measurableSet_Iic).comp (measurable_gaussianSample s)
  have hb (s : ℝ) (x : Fin 2 → ℝ) : ‖F s x‖≤1 := by
    dsimp [F,Set.indicator]
    split_ifs <;> norm_num
  have hn : ∀ᵐ x ∂μ, gaussianSample r x 1≠u 1 := by
    have h := (gaussianBivariate r hr).ae_eval_ne 1 (u 1)
    rw [gaussianBivariate_toMeasure_independent hr] at h
    exact (ae_map_iff (measurable_gaussianSample r).aemeasurable
      ((measurableSet_eq_fun (measurable_pi_apply 1) measurable_const).compl)).mp h
  apply continuousAt_of_dominated (μ := μ) (bound := fun _ => (1:ℝ))
    (Eventually.of_forall fun s => (hm s).aestronglyMeasurable)
    (Eventually.of_forall fun s => Eventually.of_forall (hb s)) (integrable_const _)
  filter_upwards [hn] with x hx
  have hne : ProbabilityTheory.cdf (gaussianReal 0 1) (r*x 0+Real.sqrt (1-r^2)*x 1)≠(u 1:ℝ) :=
    fun h => hx (Subtype.ext h)
  have hc : ContinuousAt (fun s : ℝ => ProbabilityTheory.cdf (gaussianReal 0 1)
      (s*x 0+Real.sqrt (1-s^2)*x 1)) r :=
    continuous_standardNormalCDF.continuousAt.comp (by fun_prop)
  have hf (s : ℝ) : F s x=
      if cdfUnit (gaussianReal 0 1) (x 0)≤u 0 ∧
        ProbabilityTheory.cdf (gaussianReal 0 1) (s*x 0+Real.sqrt (1-s^2)*x 1)≤(u 1:ℝ)
      then 1 else 0 := by
    simp only [F,indicator,mem_Iic,Pi.le_def,Fin.forall_fin_two,
      gaussianSample,Matrix.cons_val_zero,Matrix.cons_val_one]
    rfl
  simp_rw [hf]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have he := (tendsto_order.mp hc).2 _ hlt
    apply (show ContinuousAt (fun _ : ℝ => if cdfUnit (gaussianReal 0 1) (x 0)≤u 0 then (1:ℝ) else 0) r
      from continuousAt_const).congr
    filter_upwards [he] with s hs
    simp only [hs.le,and_true]
  · have he := (tendsto_order.mp hc).1 _ hgt
    apply (show ContinuousAt (fun _ : ℝ => (0:ℝ)) r from continuousAt_const).congr
    filter_upwards [he] with s hs
    simp only [not_le.mpr hs,and_false,ite_false]

theorem gaussianBivariate_cdf_continuous (u : Fin 2 → I) :
    Continuous (fun r : Icc (-1:ℝ) 1 => (gaussianBivariate r r.property).cdf u) := by
  have he : (fun r : Icc (-1:ℝ) 1 => (gaussianBivariate r r.property).cdf u)=
      fun r : Icc (-1:ℝ) 1 => ∫ x, (Iic u).indicator (fun _ => (1:ℝ)) (gaussianSample r x)
        ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 1) := by
    funext r
    exact gaussianBivariate_cdf_sample r.property u
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro r
  exact (gaussianBivariate_sample_integral_continuousAt r.property u).comp
    continuous_subtype_val.continuousAt

theorem gaussianBivariate_cdf_tendsto_zero (u : Fin 2 → I) :
    Tendsto (fun r : Icc (-1:ℝ) 1 => (gaussianBivariate r r.property).cdf u)
      (𝓝 (⟨0,by norm_num⟩ : Icc (-1:ℝ) 1)) (𝓝 ((independence 2).cdf u)) := by
  simpa only [gaussianBivariate_zero] using
    (gaussianBivariate_cdf_continuous u).tendsto (⟨0,by norm_num⟩ : Icc (-1:ℝ) 1)

theorem gaussianBivariate_cdf_tendsto_one (u : Fin 2 → I) :
    Tendsto (fun r : Icc (-1:ℝ) 1 => (gaussianBivariate r r.property).cdf u)
      (𝓝 (⟨1,by norm_num⟩ : Icc (-1:ℝ) 1)) (𝓝 ((comonotonic 2).cdf u)) := by
  simpa only [gaussianBivariate_one] using
    (gaussianBivariate_cdf_continuous u).tendsto (⟨1,by norm_num⟩ : Icc (-1:ℝ) 1)

theorem gaussianBivariate_cdf_tendsto_negative_one (u : Fin 2 → I) :
    Tendsto (fun r : Icc (-1:ℝ) 1 => (gaussianBivariate r r.property).cdf u)
      (𝓝 (⟨-1,by norm_num⟩ : Icc (-1:ℝ) 1)) (𝓝 (countermonotonic.cdf u)) := by
  simpa only [gaussianBivariate_negative_one] using
    (gaussianBivariate_cdf_continuous u).tendsto (⟨-1,by norm_num⟩ : Icc (-1:ℝ) 1)

end Verification
