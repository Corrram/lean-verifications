import Verification.GaussianDifference

open MeasureTheory ProbabilityTheory Set

namespace Verification

noncomputable def gaussianWeightedDifference (a b : ℝ) :
    (EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2)) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (a/Real.sqrt (a^2+b^2)) • ContinuousLinearMap.fst ℝ _ _ -
    (b/Real.sqrt (a^2+b^2)) • ContinuousLinearMap.snd ℝ _ _

theorem map_gaussianWeightedDifference (r a b : ℝ) (hp : 0<a^2+b^2) :
    let μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)
    (μ.prod μ).map (gaussianWeightedDifference a b)=μ := by
  dsimp only
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)
  change (μ.prod μ).map (gaussianWeightedDifference a b)=μ
  apply Measure.ext_of_charFunDual
  funext L
  have h1 : (L.comp (gaussianWeightedDifference a b)).comp (.inl ℝ _ _)=
      (a/Real.sqrt (a^2+b^2)) • L := by ext x; simp [gaussianWeightedDifference]
  have h2 : (L.comp (gaussianWeightedDifference a b)).comp (.inr ℝ _ _)=
      (-(b/Real.sqrt (a^2+b^2))) • L := by ext x; simp [gaussianWeightedDifference]
  have hmean : ∫ x, id x ∂μ=0 := integral_id_multivariateGaussian
  have hc : (a/Real.sqrt (a^2+b^2))^2+(b/Real.sqrt (a^2+b^2))^2=1 := by
    rw [div_pow,div_pow,Real.sq_sqrt hp.le,← add_div,div_self hp.ne']
  rw [charFunDual_map,charFunDual_prod,h1,h2]
  simp only [IsGaussian.charFunDual_eq',hmean,map_zero,Complex.ofReal_zero,zero_mul,
    zero_sub,map_smul,smul_apply,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_neg]
  rw [← Complex.exp_add]
  congr 1
  have hc' : ((a/Real.sqrt (a^2+b^2):ℝ):ℂ)^2+((b/Real.sqrt (a^2+b^2):ℝ):ℂ)^2=1 := by
    exact_mod_cast hc
  calc
    _ = -((((a/Real.sqrt (a^2+b^2):ℝ):ℂ)^2+((b/Real.sqrt (a^2+b^2):ℝ):ℂ)^2)*
      (covarianceBilinDual μ L L : ℂ))/2 := by ring
    _ = _ := by rw [hc']; ring

theorem gaussian_scaled_comparison_probability (r a b : ℝ) (hp : 0<a^2+b^2) :
    let μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)
    (μ.prod μ).real {p | a*p.1 0≤b*p.2 0 ∧ a*p.1 1≤b*p.2 1}=
      μ.real {x | x 0≤0 ∧ x 1≤0} := by
  dsimp only
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)
  have hQ : MeasurableSet {x : EuclideanSpace ℝ (Fin 2) | x 0≤0 ∧ x 1≤0} := by
    apply MeasurableSet.inter
    · exact measurableSet_le (show Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x 0) by fun_prop) measurable_const
    · exact measurableSet_le (show Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x 1) by fun_prop) measurable_const
  have hs : (gaussianWeightedDifference a b) ⁻¹' {x | x 0≤0 ∧ x 1≤0}=
      {p : EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2) |
        a*p.1 0≤b*p.2 0 ∧ a*p.1 1≤b*p.2 1} := by
    ext p
    have hroot := Real.sqrt_pos.mpr hp
    have he (x y : ℝ) : a/Real.sqrt (a^2+b^2)*x-b/Real.sqrt (a^2+b^2)*y=
        (a*x-b*y)/Real.sqrt (a^2+b^2) := by ring
    change (a/Real.sqrt (a^2+b^2)*p.1 0-b/Real.sqrt (a^2+b^2)*p.2 0≤0 ∧
      a/Real.sqrt (a^2+b^2)*p.1 1-b/Real.sqrt (a^2+b^2)*p.2 1≤0) ↔ _
    simp only [he,div_le_iff₀ hroot,zero_mul,sub_nonpos,Set.mem_ofPred_eq]
  rw [← hs,← map_measureReal_apply (by fun_prop) hQ,map_gaussianWeightedDifference r a b hp]

end Verification
