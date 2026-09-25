import Verification.GammaPrecisionConcentration
import Copula.Families.ScaleMixtures

open MeasureTheory ProbabilityTheory Set Filter Copula
open scoped Topology

namespace Verification

theorem concentration_integral_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ→ℝ) (hf : Measurable f) {B η δ : ℝ} (hB : ∀ x,|f x|≤B)
    (hη : 0≤η) (hloc : ∀ x,|x-1|<δ → |f x-f 1|≤η) :
    |(∫ x, f x ∂μ)-f 1|≤η+2*B*μ.real {x | δ≤|x-1|} := by
  have hi : Integrable f μ := ⟨hf.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)⟩
  let S : Set ℝ := {x | δ≤|x-1|}
  have hS : MeasurableSet S := by dsimp [S]; measurability
  have hiS : Integrable (S.indicator (fun _ : ℝ => 2*B)) μ := (integrable_const _).indicator hS
  have hb : ∀ x, |f x-f 1|≤η+S.indicator (fun _ : ℝ => 2*B) x := by
    intro x
    by_cases hx : x∈S
    · rw [Set.indicator_of_mem hx]
      have h := abs_sub (f x) (f 1)
      linarith [hB x,hB 1]
    · rw [Set.indicator_of_notMem hx,add_zero]
      exact hloc x (lt_of_not_ge hx)
  have hid : Integrable (fun x => f x-f 1) μ := hi.sub (integrable_const _)
  have he : (∫ x, f x-f 1 ∂μ)=(∫ x, f x ∂μ)-f 1 := by
    rw [integral_sub hi (integrable_const _)]
    simp
  calc
    |(∫ x, f x ∂μ)-f 1|=‖∫ x, f x-f 1 ∂μ‖ := by rw [he,Real.norm_eq_abs]
    _≤∫ x, ‖f x-f 1‖ ∂μ := norm_integral_le_integral_norm _
    _≤∫ x, η+S.indicator (fun _ : ℝ => 2*B) x ∂μ :=
      integral_mono hid.norm ((integrable_const η).add hiS) (fun x => by
        simpa only [Real.norm_eq_abs] using hb x)
    _=η+2*B*μ.real {x | δ≤|x-1|} := by
      rw [integral_add (integrable_const η) hiS,integral_indicator_const _ hS]
      simp [S,mul_comm]

theorem tendsto_integral_of_concentration {ι : Type*} {l : Filter ι}
    (μ : ι→ProbabilityMeasure ℝ)
    (hμ : ∀ (δ : ℝ), δ>0 → Tendsto (fun i => (μ i).toMeasure.real {x | δ≤|x-1|}) l (nhds 0))
    (f : ℝ→ℝ) (hf : Measurable f) (hc : ContinuousAt f 1)
    {B : ℝ} (hB : ∀ x,|f x|≤B) :
    Tendsto (fun i => ∫ x, f x ∂(μ i).toMeasure) l (nhds (f 1)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp
    ((Metric.tendsto_nhds.mp hc.tendsto) (ε/2) (by positivity))
  have hlocal : ∀ x,|x-1|<δ → |f x-f 1|≤ε/2 := by
    intro x hx
    have h := hball (show x∈Metric.ball (1:ℝ) δ by simpa only [Metric.mem_ball,Real.dist_eq] using hx)
    exact le_of_lt (by simpa only [Set.mem_ofPred_eq,Real.dist_eq] using h)
  have hz := (hμ δ hδ).const_mul (2*B)
  simp only [mul_zero] at hz
  filter_upwards [hz.eventually (eventually_lt_nhds (show (0:ℝ)<ε/2 by positivity))] with i hi
  have hbound := concentration_integral_bound (μ i).toMeasure f hf hB
    (show 0≤ε/2 by positivity) hlocal
  rw [Real.dist_eq]
  linarith

theorem gammaPrecision_integral_tendsto {ι : Type*} {l : Filter ι}
    (a : ι→ℝ) (ha : ∀ i,0<a i) (ht : Tendsto a l atTop)
    (f : ℝ→ℝ) (hf : Measurable f) (hc : ContinuousAt f 1)
    {B : ℝ} (hB : ∀ x,|f x|≤B) :
    Tendsto (fun i => ∫ x, f x ∂gammaMeasure (a i) (a i)) l (nhds (f 1)) := by
  exact tendsto_integral_of_concentration
    (fun i => gammaProbability (a i) (a i) (ha i) (ha i))
    (fun δ hδ => gammaPrecision_concentrates a ha ht hδ) f hf hc hB

end Verification
