import Verification.SklarTP2Transfer

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval ENNReal

namespace Verification

theorem gaussianScaleMixture_joint_tp2_density {r : ℝ} (hr : r∈Ioo (-1) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ→ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t)
    (htp : (gaussianScaleMixture (bivariateCorrelation r)
      (bivariateCorrelation_posSemidef ⟨hr.1.le,hr.2.le⟩)
      (by intro i; fin_cases i <;> rfl) μ s hs hp).HasMTP2Density) :
    ∃ g : ℝ×ℝ→ℝ, Measurable g ∧ (∀ p,0≤g p) ∧
      (∀ a b c d : ℝ, a≤b → c≤d → g (a,d)*g (b,c)≤g (a,c)*g (b,d)) ∧
      (gaussianScaleMixtureLaw (bivariateCorrelation r) μ s).toMeasure.map
        MeasurableEquiv.finTwoArrow=volume.withDensity (fun p => ENNReal.ofReal (g p)) := by
  let M := normalScaleMixtureMarginal μ s
  let L := gaussianScaleMixtureLaw (bivariateCorrelation r) μ s
  let F := fun p : ℝ×ℝ => ![cdfUnit M p.1,cdfUnit M p.2]
  have hm (i : Fin 2) : marginal L i=M :=
    gaussianScaleMixtureLaw_marginal _ (bivariateCorrelation_posSemidef ⟨hr.1.le,hr.2.le⟩)
      (by intro j; fin_cases j <;> rfl) μ s hs i
  let : IsProbabilityMeasure M := by
    rw [← hm 0]
    infer_instance
  have hc : Continuous (ProbabilityTheory.cdf M) := by
    rw [← hm 0]
    exact continuous_gaussianScaleMixtureLaw_marginal _ (bivariateCorrelation_posSemidef ⟨hr.1.le,hr.2.le⟩)
      (by intro i; fin_cases i <;> rfl) μ s hs hp 0
  have hf : Measurable F := by fun_prop
  have hmap : (M.prod M).map F=(independence 2).toMeasure := by
    have he := Measure.map_map hf MeasurableEquiv.finTwoArrow.measurable
      (μ := Measure.pi (fun _ : Fin 2 => M))
    rw [(measurePreserving_finTwoArrow M).map_eq] at he
    have hfun : F ∘ MeasurableEquiv.finTwoArrow=(fun x : Fin 2 → ℝ => fun i => cdfUnit M (x i)) := by
      funext x i
      fin_cases i <;> rfl
    rw [hfun,Measure.pi_map_pi (fun _ => (measurable_cdfUnit M).aemeasurable)] at he
    simpa only [map_cdfUnit M hc,toMeasure_independence] using he
  have hC : (gaussianScaleMixture (bivariateCorrelation r) (bivariateCorrelation_posSemidef ⟨hr.1.le,hr.2.le⟩)
      (by intro i; fin_cases i <;> rfl) μ s hs hp).toMeasure=
      (L.toMeasure.map MeasurableEquiv.finTwoArrow).map F := by
    change L.toMeasure.map (marginalTransform L)=_
    rw [Measure.map_map hf MeasurableEquiv.finTwoArrow.measurable]
    congr 1
    funext x i
    dsimp only [marginalTransform]
    rw [hm i]
    fin_cases i <;> rfl
  let D := normalScaleMixtureDensity μ s
  have hD : Measurable D := measurable_normalScaleMixtureDensity μ s hs
  have hMd : M=volume.withDensity D := normalScaleMixtureMarginal_withDensity μ s hs hp
  have hfinite : (∫⁻ x, D x)≠∞ := by
    have he := withDensity_apply (μ := (volume : Measure ℝ)) D MeasurableSet.univ
    rw [← hMd,Measure.restrict_univ] at he
    rw [← he]
    exact measure_ne_top _ _
  have htop : ∀ᵐ x ∂(volume : Measure ℝ), D x≠∞ :=
    (ae_lt_top' hD.aemeasurable hfinite).mono (fun _ h => h.ne)
  have hMr : M=volume.withDensity (fun x => ENNReal.ofReal ((D x).toReal)) := by
    rw [hMd]
    apply withDensity_congr_ae
    filter_upwards [htop] with x hx
    exact (ENNReal.ofReal_toReal hx).symm
  apply joint_tp2_density_of_copula _ M (fun x => (D x).toReal) hD.ennreal_toReal
    (fun _ => ENNReal.toReal_nonneg) hMr (cdfUnit M) (measurable_cdfUnit M) _ _ _ _ hC htp
  · intro x y hxy
    exact (normalScaleMixtureMarginal_cdf_strictMono μ s hs hp).monotone hxy
  · intro x y he
    exact (normalScaleMixtureMarginal_cdf_strictMono μ s hs hp).injective (congrArg Subtype.val he)
  · exact hmap

end Verification
