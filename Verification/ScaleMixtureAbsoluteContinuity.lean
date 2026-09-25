import Verification.ScaleMixtureJointDensity
import Verification.StudentNegativeEndpoint

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

theorem gaussianScaleMixture_absolutelyContinuous {r : ℝ} (hr : r∈Ioo (-1) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) :
    (gaussianScaleMixture (bivariateCorrelation r) (bivariateCorrelation_posSemidef ⟨hr.1.le,hr.2.le⟩)
      (by intro i; fin_cases i <;> rfl) μ s hs hp).toMeasure ≪ volume := by
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
  have hinj : Function.Injective F := by
    intro p q he
    apply Prod.ext
    · apply (normalScaleMixtureMarginal_cdf_strictMono μ s hs hp).injective
      exact congrArg Subtype.val (congrFun he 0)
    · apply (normalScaleMixtureMarginal_cdf_strictMono μ s hs hp).injective
      exact congrArg Subtype.val (congrFun he 1)
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
  have hab : (volume : Measure (ℝ×ℝ)) ≪ M.prod M := by
    rw [Measure.volume_eq_prod]
    exact (normalScaleMixtureMarginal_equivalent_volume μ s hs hp).2.prod
      (normalScaleMixtureMarginal_equivalent_volume μ s hs hp).2
  have hac := (gaussianScaleMixtureLaw_joint_equivalent_volume hr μ s hs hp).1.trans hab
  have hh := (hf.measurableEmbedding hinj).absolutelyContinuous_map hac
  rw [hmap] at hh
  rw [hC]
  exact hh

theorem gaussianScaleMixture_absolutelyContinuous_iff {r : ℝ} (hr : r∈Icc (-1) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) :
    (gaussianScaleMixture (bivariateCorrelation r) (bivariateCorrelation_posSemidef hr)
      (by intro i; fin_cases i <;> rfl) μ s hs hp).toMeasure ≪ volume ↔ r∈Ioo (-1) 1 := by
  constructor
  · intro h
    have hn : r≠ -1 := by
      intro he
      subst r
      rw [gaussianScaleMixture_negative_one μ s hs hp,← mardia_neg_one] at h
      have hh := (mardia_absolutelyContinuous_iff (-1) (by norm_num)).mp h
      norm_num at hh
    have hpos : r≠1 := by
      intro he
      subst r
      rw [gaussianScaleMixture_one μ s hs hp,← mardia_one] at h
      have hh := (mardia_absolutelyContinuous_iff 1 (by norm_num)).mp h
      norm_num at hh
    exact ⟨lt_of_le_of_ne hr.1 (Ne.symm hn),lt_of_le_of_ne hr.2 hpos⟩
  · exact fun h => gaussianScaleMixture_absolutelyContinuous h μ s hs hp

end Verification
