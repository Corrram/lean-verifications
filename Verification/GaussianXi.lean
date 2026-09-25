import Verification.GaussianXiProbability

/-! # Corrected Gaussian Chatterjee xi formula -/

open ProbabilityTheory MeasureTheory Set Copula

namespace Verification

theorem gaussian_xi_integral_quadrant {r : ℝ} (hr : r∈Ioo (-1) 1) :
    (∫ b, ∫ x, (ProbabilityTheory.cdf (gaussianReal 0 1)
      ((b-r*x)/Real.sqrt (1-r^2)))^2 ∂gaussianReal 0 1 ∂gaussianReal 0 1)=
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2))
        (bivariateCorrelation ((1+r^2)/2))).real {x | x 0≤0 ∧ x 1≤0} := by
  let μ := gaussianReal 0 1
  let s := Real.sqrt (1-r^2)
  let Q := {x : EuclideanSpace ℝ (Fin 2) | x 0≤0 ∧ x 1≤0}
  let S := (gaussianXiMap r) ⁻¹' Q
  have hs : 0<s := Real.sqrt_pos.2 (by nlinarith [hr.1,hr.2])
  have hQ : MeasurableSet Q := by
    apply MeasurableSet.inter
    · exact measurableSet_le
        (show Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x 0) by fun_prop) measurable_const
    · exact measurableSet_le
        (show Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x 1) by fun_prop) measurable_const
  have hS : MeasurableSet S := hQ.preimage (by fun_prop)
  have hi : Integrable (S.indicator (fun _ => (1:ℝ))) ((μ.prod μ).prod (μ.prod μ)) :=
    (integrable_const _).indicator hS
  have hc : 0<(Real.sqrt 2)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (by norm_num))
  have he (p : ℝ×ℝ) :
      (∫ q, S.indicator (fun _ => (1:ℝ)) (p,q) ∂μ.prod μ)=
        (ProbabilityTheory.cdf μ ((p.1-r*p.2)/s))^2 := by
    have hh (y : ℝ) : (Real.sqrt 2)⁻¹*(r*p.2-p.1+s*y)≤0 ↔
        y≤(p.1-r*p.2)/s := by
      rw [le_div_iff₀ hs]
      constructor
      · intro h
        nlinarith
      · intro h
        exact mul_nonpos_of_nonneg_of_nonpos hc.le (by nlinarith)
    have hfun : (fun q : ℝ×ℝ => S.indicator (fun _ => (1:ℝ)) (p,q))=
        (Iic ((p.1-r*p.2)/s) ×ˢ Iic ((p.1-r*p.2)/s)).indicator 1 := by
      funext q
      simp only [S,Q,indicator,mem_preimage,mem_ofPred_eq,mem_prod,mem_Iic,Pi.one_apply]
      congr 1
      change ((Real.sqrt 2)⁻¹*(r*p.2-p.1+s*q.1)≤0 ∧
        (Real.sqrt 2)⁻¹*(r*p.2-p.1+s*q.2)≤0)=_
      simp only [hh]
    rw [hfun,integral_indicator_one (measurableSet_Iic.prod measurableSet_Iic),
      measureReal_prod_prod,← ProbabilityTheory.cdf_eq_real,pow_two]
  have hg : Integrable
      (fun p : ℝ×ℝ => (ProbabilityTheory.cdf μ ((p.1-r*p.2)/s))^2) (μ.prod μ) := by
    apply (integrable_const (1:ℝ)).mono'
      ((((monotone_cdf μ).measurable.comp
        (show Measurable (fun p : ℝ×ℝ => (p.1-r*p.2)/s) by fun_prop)).pow_const 2).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun p => by
      dsimp only [Function.comp_def]
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      nlinarith [cdf_nonneg μ ((p.1-r*p.2)/s),cdf_le_one μ ((p.1-r*p.2)/s)]
  symm
  rw [← map_gaussianXiMap ⟨hr.1.le,hr.2.le⟩,
    map_measureReal_apply (by fun_prop) hQ,← integral_indicator_one hS]
  change (∫ p, S.indicator (fun _ => (1:ℝ)) p ∂(μ.prod μ).prod (μ.prod μ))=_
  rw [integral_prod _ hi]
  simp_rw [he]
  exact integral_prod _ hg

theorem gaussianBivariate_chatterjeeXi {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate r hr).chatterjeeXi=3/Real.pi*Real.arcsin ((1+r^2)/2)-1/2 := by
  by_cases hneg : r= -1
  · subst r
    rw [gaussianBivariate_negative_one,chatterjeeXi_countermonotonic]
    norm_num [Real.arcsin_one]
    field_simp
    norm_num
  by_cases hpos : r=1
  · subst r
    rw [gaussianBivariate_one,chatterjeeXi_comonotonic]
    norm_num [Real.arcsin_one]
    field_simp
    norm_num
  have hi : r∈Ioo (-1) 1 := ⟨lt_of_le_of_ne hr.1 (Ne.symm hneg),lt_of_le_of_ne hr.2 hpos⟩
  have hq : (1+r^2)/2∈Ioo (-1) 1 := by constructor <;> nlinarith [hi.1,hi.2,sq_nonneg r]
  rw [gaussianBivariate_xi_normal_integral hi,gaussian_xi_integral_quadrant hi,
    multivariateGaussian_lower_quadrant hq]
  ring

end Verification
