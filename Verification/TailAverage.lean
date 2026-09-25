import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

open MeasureTheory Set Filter
open scoped Topology

namespace Verification

theorem tendsto_lower_tail_average (μ : Measure ℝ) [IsFiniteMeasure μ]
    {f : ℝ → ℝ} {L : ℝ} (hi : Integrable f μ)
    (hp : ∀ a : ℝ,0<μ.real (Iic a)) (ht : Tendsto f atBot (𝓝 L)) :
    Tendsto (fun a => (∫ x in Iic a, f x ∂μ)/μ.real (Iic a)) atBot (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨b,hb⟩ := eventually_atBot.mp ((Metric.tendsto_nhds.mp ht) (ε/2) (by positivity))
  apply eventually_atBot.mpr
  refine ⟨b,fun a ha => ?_⟩
  have hlo : (∫ _ in Iic a, L-ε/2 ∂μ)≤∫ x in Iic a,f x ∂μ := by
    apply setIntegral_mono_on (integrable_const _).integrableOn hi.integrableOn measurableSet_Iic
    intro x hx
    have h := hb x (hx.trans ha)
    rw [Real.dist_eq] at h
    exact le_of_lt (by linarith [(abs_lt.mp h).1])
  have hhi : (∫ x in Iic a,f x ∂μ)≤∫ _ in Iic a,L+ε/2 ∂μ := by
    apply setIntegral_mono_on hi.integrableOn (integrable_const _).integrableOn measurableSet_Iic
    intro x hx
    have h := hb x (hx.trans ha)
    rw [Real.dist_eq] at h
    exact le_of_lt (by linarith [(abs_lt.mp h).2])
  rw [setIntegral_const,smul_eq_mul] at hlo hhi
  have hl : L-ε/2≤(∫ x in Iic a,f x ∂μ)/μ.real (Iic a) :=
    (le_div_iff₀ (hp a)).mpr (by simpa only [mul_comm] using hlo)
  have hu : (∫ x in Iic a,f x ∂μ)/μ.real (Iic a)≤L+ε/2 :=
    (div_le_iff₀ (hp a)).mpr (by simpa only [mul_comm] using hhi)
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

end Verification
