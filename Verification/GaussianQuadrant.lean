import Verification.GaussianWedge
import Verification.GaussianRepresentation

/-! # Centered bivariate Gaussian quadrant probabilities

The checked half-line normal-CDF integral evaluates the mixed-sign quadrant.
The standard normal marginal then gives the lower quadrant. We also establish
strict CDF monotonicity to transfer comparisons through the copula transform.
-/

open MeasureTheory ProbabilityTheory Set

namespace Verification

theorem standardNormalCDF_strictMono :
    StrictMono (ProbabilityTheory.cdf (gaussianReal 0 1)) := by
  intro a b hab
  apply lt_of_le_of_ne ((monotone_cdf (gaussianReal 0 1)) hab.le)
  intro he
  have hz : (gaussianReal 0 1) (Ioc a b)=0 := by
    rw [← measure_cdf (gaussianReal 0 1),StieltjesFunction.measure_Ioc,← he,
      sub_self,ENNReal.ofReal_zero]
  have hv := gaussianReal_absolutelyContinuous' 0 (by norm_num : (1:NNReal)≠0) hz
  rw [Real.volume_Ioc,ENNReal.ofReal_eq_zero] at hv
  linarith

theorem standardGaussian_linear_halfline {s : ℝ} (hs : 0<s) (b : ℝ) :
    (∫ y, (if s*y≤b then (1:ℝ) else 0) ∂gaussianReal 0 1)=
      ProbabilityTheory.cdf (gaussianReal 0 1) (b/s) := by
  have he (y : ℝ) : s*y≤b ↔ y≤b/s := by
    rw [le_div_iff₀ hs,mul_comm]
  simp_rw [he]
  rw [ProbabilityTheory.cdf_eq_real]
  simpa only [indicator,mem_Iic,Pi.one_apply] using
    integral_indicator_one (μ := gaussianReal 0 1) (s := Iic (b/s)) measurableSet_Iic

theorem standardGaussian_discordant_quadrant {r : ℝ} (hr : r∈Ioo (-1) 1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
      {p : ℝ×ℝ | 0<p.1 ∧ r*p.1+Real.sqrt (1-r^2)*p.2≤0}=
      1/4-Real.arcsin r/(2*Real.pi) := by
  let μ := gaussianReal 0 1
  let S := {p : ℝ×ℝ | 0<p.1 ∧ r*p.1+Real.sqrt (1-r^2)*p.2≤0}
  have hS : MeasurableSet S := by
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le
        ((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd))
        measurable_const)
  have hi : Integrable (S.indicator (fun _ => (1:ℝ))) (μ.prod μ) :=
    (integrable_const _).indicator hS
  have hs : 0<Real.sqrt (1-r^2) := Real.sqrt_pos.2 (by nlinarith [hr.1,hr.2])
  change (μ.prod μ).real S=_
  rw [← integral_indicator_one hS]
  change (∫ x, S.indicator (fun _ => (1:ℝ)) x ∂μ.prod μ)=_
  rw [integral_prod _ hi]
  have he (x : ℝ) :
      (∫ y, S.indicator (fun _ => (1:ℝ)) (x,y) ∂μ)=
      (Ioi (0:ℝ)).indicator
        (fun x => ProbabilityTheory.cdf μ ((-r/Real.sqrt (1-r^2))*x)) x := by
    by_cases hx : 0<x
    · rw [indicator_of_mem (show x∈Ioi (0:ℝ) from hx)]
      have hf (y : ℝ) : S.indicator (fun _ => (1:ℝ)) (x,y)=
          if Real.sqrt (1-r^2)*y≤ -r*x then (1:ℝ) else 0 := by
        simp only [S,indicator,mem_ofPred_eq,hx,true_and]
        congr 1
        apply propext
        constructor <;> intro h <;> linarith
      simp_rw [hf]
      rw [standardGaussian_linear_halfline hs]
      congr 1
      ring
    · simp [S,indicator,hx]
  simp_rw [he]
  rw [integral_indicator measurableSet_Ioi,integral_standardGaussian_cdf]
  rw [neg_div,Real.arctan_neg,← Real.arcsin_eq_arctan hr]
  ring

theorem multivariateGaussian_discordant_quadrant {r : ℝ} (hr : r∈Ioo (-1) 1) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)).real
      {x | 0<x 0 ∧ x 1≤0}=1/4-Real.arcsin r/(2*Real.pi) := by
  have hm : MeasurableSet {x : EuclideanSpace ℝ (Fin 2) | 0<x 0 ∧ x 1≤0} := by
    apply MeasurableSet.inter
    · exact measurableSet_lt measurable_const
        (show Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x 0) by fun_prop)
    · exact measurableSet_le
        (show Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x 1) by fun_prop) measurable_const
  rw [← map_gaussianMix (show r∈Icc (-1) 1 from ⟨hr.1.le,hr.2.le⟩),
    ← map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (by fun_prop),
    map_measureReal_apply (by fun_prop) hm]
  change (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).real
    {x | 0<x 0 ∧ r*x 0+Real.sqrt (1-r^2)*x 1≤0}=_
  have hs : MeasurableSet {p : ℝ×ℝ | 0<p.1 ∧ r*p.1+Real.sqrt (1-r^2)*p.2≤0} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le
        ((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd))
        measurable_const)
  have he := (measurePreserving_finTwoArrow (gaussianReal 0 1)).measure_preimage
    hs.nullMeasurableSet
  have hh := congrArg ENNReal.toReal he
  change (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).real
    {x | 0<x 0 ∧ r*x 0+Real.sqrt (1-r^2)*x 1≤0}=
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
      {p : ℝ×ℝ | 0<p.1 ∧ r*p.1+Real.sqrt (1-r^2)*p.2≤0} at hh
  rw [hh,standardGaussian_discordant_quadrant hr]

theorem multivariateGaussian_lower_quadrant {r : ℝ} (hr : r∈Ioo (-1) 1) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)).real
      {x | x 0≤0 ∧ x 1≤0}=1/4+Real.arcsin r/(2*Real.pi) := by
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)
  have h0 : MeasurableSet {x : EuclideanSpace ℝ (Fin 2) | x 0≤0} :=
    measurableSet_le (show Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x 0) by fun_prop)
      measurable_const
  have hp := (measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ (Fin 2)))
    (bivariateCorrelation_posSemidef ⟨hr.1.le,hr.2.le⟩) (i := 1)).measure_preimage
    measurableSet_Iic.nullMeasurableSet (s := Iic (0:ℝ))
  have hm : μ.real {x | x 1≤0}=1/2 := by
    have hh := congrArg ENNReal.toReal hp
    norm_num [bivariateCorrelation] at hh
    change μ.real {x | x 1≤0}=(gaussianReal 0 1).real (Iic 0) at hh
    rw [← ProbabilityTheory.cdf_eq_real,standardGaussian_cdf_zero] at hh
    exact hh
  have he := measureReal_inter_add_sdiff (μ := μ)
    (s := {x : EuclideanSpace ℝ (Fin 2) | x 1≤0}) h0
  have hs : {x : EuclideanSpace ℝ (Fin 2) | x 1≤0} ∩ {x | x 0≤0}=
      {x | x 0≤0 ∧ x 1≤0} := by ext x; simp [and_comm]
  have ht : {x : EuclideanSpace ℝ (Fin 2) | x 1≤0} \ {x | x 0≤0}=
      {x | 0<x 0 ∧ x 1≤0} := by ext x; simp [and_comm]
  rw [hs,ht,hm,multivariateGaussian_discordant_quadrant hr] at he
  change μ.real {x | x 0≤0 ∧ x 1≤0}=_
  linarith

end Verification
