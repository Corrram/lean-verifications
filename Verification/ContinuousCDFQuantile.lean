import Copula.Sklar.Continuous

open ProbabilityTheory MeasureTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def continuousCDFQuantile (μ : Measure ℝ)
    (hc : Continuous (ProbabilityTheory.cdf μ)) (hs : StrictMono (ProbabilityTheory.cdf μ)) (u : I) : ℝ :=
  (hc.measurableEmbedding hs.injective).invFun (u:ℝ)

theorem strictCDF_mem_Ioo (μ : Measure ℝ) (hs : StrictMono (ProbabilityTheory.cdf μ)) (x : ℝ) :
    ProbabilityTheory.cdf μ x∈Ioo (0:ℝ) 1 := by
  constructor
  · have h := hs (show x-1<x by linarith)
    have hn := ProbabilityTheory.cdf_nonneg μ (x-1)
    linarith
  · have h := hs (show x<x+1 by linarith)
    have hn := ProbabilityTheory.cdf_le_one μ (x+1)
    linarith

theorem continuousCDFQuantile_cdfUnit (μ : Measure ℝ)
    (hc : Continuous (ProbabilityTheory.cdf μ)) (hs : StrictMono (ProbabilityTheory.cdf μ)) (x : ℝ) :
    continuousCDFQuantile μ hc hs (cdfUnit μ x)=x :=
  (hc.measurableEmbedding hs.injective).leftInverse_invFun x

theorem cdf_continuousCDFQuantile (μ : Measure ℝ)
    (hc : Continuous (ProbabilityTheory.cdf μ)) (hs : StrictMono (ProbabilityTheory.cdf μ))
    {u : I} (hu : (u:ℝ)∈Ioo (0:ℝ) 1) :
    ProbabilityTheory.cdf μ (continuousCDFQuantile μ hc hs u)=(u:ℝ) := by
  obtain ⟨x,hx⟩ := exists_cdf_eq_of_continuous μ hc hu.1 hu.2
  have he : cdfUnit μ x=u := Subtype.ext hx
  rw [← he,continuousCDFQuantile_cdfUnit]
  rfl

theorem continuousCDFQuantile_tendsto_zero (μ : Measure ℝ)
    (hc : Continuous (ProbabilityTheory.cdf μ)) (hs : StrictMono (ProbabilityTheory.cdf μ)) :
    Tendsto (continuousCDFQuantile μ hc hs) (𝓝[>] (0:I)) atBot := by
  apply tendsto_atBot.mpr
  intro b
  have ht : Tendsto (fun u : I => (u:ℝ)) (𝓝[>] (0:I)) (𝓝 (0:ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ u : I in 𝓝[>] (0:I),(u:ℝ)<ProbabilityTheory.cdf μ b :=
    ht.eventually (eventually_lt_nhds (strictCDF_mem_Ioo μ hs b).1)
  filter_upwards [he,(self_mem_nhdsWithin : ∀ᶠ u : I in 𝓝[>] (0:I),0<u)] with u hu hu0
  apply hs.le_iff_le.mp
  rw [cdf_continuousCDFQuantile μ hc hs ⟨hu0,hu.trans (strictCDF_mem_Ioo μ hs b).2⟩]
  exact hu.le

end Verification
