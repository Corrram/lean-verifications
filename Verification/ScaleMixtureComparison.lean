import Verification.GaussianWeightedDifference
import Verification.ScaleMixtureCDF
import Verification.ProductRegroup

open ProbabilityTheory MeasureTheory Set Copula

namespace Verification

theorem gaussianScaleMixtureLaw_comparison (r : ℝ) (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ)
    (hs : Measurable s) (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) :
    let L := (gaussianScaleMixtureLaw (bivariateCorrelation r) μ s).toMeasure
    (L.prod L).real {p | p.1≤p.2}=
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)).real
        {x | x 0≤0 ∧ x 1≤0} := by
  dsimp only
  let G := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)
  let P := G.prod μ.toMeasure
  let F := fun p : EuclideanSpace ℝ (Fin 2)×ℝ => fun i => s p.2*p.1 i
  let H := fun p : (EuclideanSpace ℝ (Fin 2)×ℝ)×(EuclideanSpace ℝ (Fin 2)×ℝ) =>
    ((p.1.1,p.2.1),(p.1.2,p.2.2))
  let S := {p : (EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2))×(ℝ×ℝ) |
    s p.2.1*p.1.1 0≤s p.2.2*p.1.2 0 ∧ s p.2.1*p.1.1 1≤s p.2.2*p.1.2 1}
  have hF : Measurable F := by fun_prop
  have hS : MeasurableSet S := by
    have hl (i : Fin 2) : Measurable (fun p : (EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2))×(ℝ×ℝ) => s p.2.1*p.1.1 i) := by fun_prop
    have hr (i : Fin 2) : Measurable (fun p : (EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2))×(ℝ×ℝ) => s p.2.2*p.1.2 i) := by fun_prop
    exact (measurableSet_le (hl 0) (hr 0)).inter (measurableSet_le (hl 1) (hr 1))
  change ((P.map F).prod (P.map F)).real {p | p.1≤p.2}=G.real _
  rw [Measure.map_prod_map _ _ hF hF,map_measureReal_apply (hF.prodMap hF)
    (measurableSet_le measurable_fst measurable_snd)]
  have he : (Prod.map F F) ⁻¹' {p : (Fin 2 → ℝ)×(Fin 2 → ℝ) | p.1≤p.2}=H ⁻¹' S := by
    ext p
    simp [F,H,S,Pi.le_def,Fin.forall_fin_two]
  rw [he]
  have hmeasure := congrArg ENNReal.toReal
    ((measurePreserving_product_regroup G μ.toMeasure).measure_preimage hS.nullMeasurableSet)
  change (P.prod P).real (H ⁻¹' S)=((G.prod G).prod (μ.toMeasure.prod μ.toMeasure)).real S at hmeasure
  rw [hmeasure,← integral_indicator_one hS]
  have hi : Integrable (S.indicator (fun _ => (1:ℝ))) ((G.prod G).prod (μ.toMeasure.prod μ.toMeasure)) :=
    (integrable_const _).indicator hS
  change (∫ p, S.indicator (fun _ => (1:ℝ)) p ∂(G.prod G).prod (μ.toMeasure.prod μ.toMeasure))=_
  rw [integral_prod_symm _ hi]
  have hpos : ∀ᵐ t ∂μ.toMeasure.prod μ.toMeasure,0<s t.1 ∧ 0<s t.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_lt measurable_const (hs.comp measurable_fst)).inter
        (measurableSet_lt measurable_const (hs.comp measurable_snd)))).mpr
    filter_upwards [hp] with a ha
    filter_upwards [hp] with b hb
    exact ⟨ha,hb⟩
  have heq : (fun t : ℝ×ℝ => ∫ p, S.indicator (fun _ => (1:ℝ)) (p,t) ∂G.prod G)=ᵐ[μ.toMeasure.prod μ.toMeasure]
      fun _ => G.real {x | x 0≤0 ∧ x 1≤0} := by
    filter_upwards [hpos] with t ht
    have hT : MeasurableSet {p : EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2) |
        s t.1*p.1 0≤s t.2*p.2 0 ∧ s t.1*p.1 1≤s t.2*p.2 1} := by
      have hl (i : Fin 2) : Measurable (fun p : EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2) => s t.1*p.1 i) := by fun_prop
      have hr (i : Fin 2) : Measurable (fun p : EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2) => s t.2*p.2 i) := by fun_prop
      exact (measurableSet_le (hl 0) (hr 0)).inter (measurableSet_le (hl 1) (hr 1))
    have hint := integral_indicator_one (μ := G.prod G) hT
    change (∫ p, S.indicator (fun _ => (1:ℝ)) (p,t) ∂G.prod G)=_
    have hval := gaussian_scaled_comparison_probability r (s t.1) (s t.2)
      (by nlinarith [sq_pos_of_pos ht.1,sq_nonneg (s t.2)])
    rw [← hval]
    simpa only [S,indicator,mem_ofPred_eq,Pi.one_apply] using hint
  rw [integral_congr_ae heq]
  simp

end Verification
