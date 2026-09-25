import Verification.ScaleMixtureComparison
import Verification.GaussianTau

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

theorem kendallTau_ofContinuousMarginals_probability (μ : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ i,Continuous (ProbabilityTheory.cdf (marginal μ i)))
    (hm : ∀ i,StrictMono (ProbabilityTheory.cdf (marginal μ i))) :
    (ofContinuousMarginals μ hc).kendallTau=
      4*(μ.toMeasure.prod μ.toMeasure).real {p | p.1≤p.2}-1 := by
  let f := marginalTransform μ
  have hf : Measurable f := measurable_marginalTransform μ
  have hC : (ofContinuousMarginals μ hc).toMeasure=μ.toMeasure.map f := rfl
  have hS : MeasurableSet {p : (Fin 2 → I)×(Fin 2 → I) | p.1≤p.2} :=
    measurableSet_le measurable_fst measurable_snd
  have he : (Prod.map f f) ⁻¹' {p : (Fin 2 → I)×(Fin 2 → I) | p.1≤p.2}=
      {p : (Fin 2 → ℝ)×(Fin 2 → ℝ) | p.1≤p.2} := by
    ext p
    change (∀ i,ProbabilityTheory.cdf (marginal μ i) (p.1 i)≤
      ProbabilityTheory.cdf (marginal μ i) (p.2 i)) ↔ ∀ i,p.1 i≤p.2 i
    exact forall_congr' (fun i => (hm i).le_iff_le)
  rw [kendallTau_probability,hC,Measure.map_prod_map _ _ hf hf,
    map_measureReal_apply (hf.prodMap hf) hS,he]

theorem gaussianScaleMixture_kendallTau {r : ℝ} (hr : r∈Icc (-1) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) :
    (gaussianScaleMixture (bivariateCorrelation r) (bivariateCorrelation_posSemidef hr)
      (by intro i; fin_cases i <;> rfl) μ s hs hp).kendallTau=2/Real.pi*Real.arcsin r := by
  have hm (i : Fin 2) : StrictMono (ProbabilityTheory.cdf
      (marginal (gaussianScaleMixtureLaw (bivariateCorrelation r) μ s) i)) := by
    rw [gaussianScaleMixtureLaw_marginal _ (bivariateCorrelation_posSemidef hr)
      (by intro j; fin_cases j <;> rfl) μ s hs i]
    exact normalScaleMixtureMarginal_cdf_strictMono μ s hs hp
  rw [gaussianScaleMixture,kendallTau_ofContinuousMarginals_probability _ _ hm,
    gaussianScaleMixtureLaw_comparison r μ s hs hp]
  exact (gaussianBivariate_tau_quadrant hr).symm.trans (gaussianBivariate_kendallTau hr)

end Verification
