import Verification.TEVCorrelationOrder
import Copula.Diagonal.Power

/-! # Singular correlation endpoints of the t-EV construction

At `r=1` the Gaussian coordinates coincide and the construction is the comonotonic copula.
At `r=-1` the positive parts have disjoint supports and it is the independence copula.
-/

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped unitInterval

namespace Verification

theorem tEV_one_pickands_half (ν : ℝ) (hν : 0<ν) :
    copulaPickands (tEV ν 1 hν ⟨by norm_num,le_rfl⟩) unitHalf=1/2 := by
  rw [tEV,stableTailCopula_pickands]
  have hWm : Measurable (gaussianPositiveWeight ν) :=
    (positivePower_continuous ν hν).measurable.div_const _
  change (∫ z, max ((1-(1/2:ℝ))*gaussianPositiveWeight ν (z 0)) ((1/2:ℝ)*gaussianPositiveWeight ν (z 1))
    ∂multivariateGaussian 0 (bivariateCorrelation 1))=1/2
  rw [integral_bivariateGaussian_mix ⟨by norm_num,le_rfl⟩
    (fun a b => max ((1-(1/2:ℝ))*gaussianPositiveWeight ν a) ((1/2:ℝ)*gaussianPositiveWeight ν b))
    (by fun_prop)]
  simp only [one_pow,sub_self,Real.sqrt_zero,zero_mul,add_zero,one_mul]
  norm_num
  rw [integral_prod _ ((((gaussianPositiveWeight_integrable ν hν).const_mul (1/2)).comp_fst
    (gaussianReal 0 1)).congr (Filter.Eventually.of_forall fun p => by norm_num))]
  simp only [integral_const,measureReal_univ_eq_one,smul_eq_mul,one_mul]
  rw [integral_const_mul,gaussianPositiveWeight_mean ν hν]
  norm_num

theorem tEV_one (ν : ℝ) (hν : 0<ν) :
    tEV ν 1 hν ⟨by norm_num,le_rfl⟩=comonotonic 2 := by
  have hp := (tEV_isExtremeValue ν 1 hν ⟨by norm_num,le_rfl⟩).hasPowerDiagonal
  rw [extremalCoefficient_eq_twice_pickands _ (tEV_isExtremeValue ν 1 hν _),
    tEV_one_pickands_half ν hν,show (2:ℝ)*(1/2)=1 by norm_num] at hp
  exact (hasPowerDiagonal_one_iff _).mp hp

theorem gaussianPositiveWeight_neg_mean (ν : ℝ) (hν : 0<ν) :
    ∫ z, gaussianPositiveWeight ν (-z) ∂gaussianReal 0 1=1 := by
  have hWm : Measurable (gaussianPositiveWeight ν) :=
    (positivePower_continuous ν hν).measurable.div_const _
  have h := integral_map (μ := gaussianReal 0 1) (f := gaussianPositiveWeight ν)
    (measurable_neg.aemeasurable) hWm.aestronglyMeasurable
  rw [gaussianReal_map_neg,neg_zero] at h
  rw [← h,gaussianPositiveWeight_mean ν hν]

theorem tEVStableTail_negative_one (ν : ℝ) (hν : 0<ν) {x y : ℝ} (hx : 0≤x) (hy : 0≤y) :
    (tEVStableTail ν (-1) hν ⟨le_rfl,by norm_num⟩).value x y=x+y := by
  have hWi := gaussianPositiveWeight_integrable ν hν
  change (∫ z, max (x*gaussianPositiveWeight ν (z 0)) (y*gaussianPositiveWeight ν (z 1))
    ∂multivariateGaussian 0 (bivariateCorrelation (-1)))=x+y
  rw [integral_bivariateGaussian_mix ⟨le_rfl,by norm_num⟩
    (fun a b => max (x*gaussianPositiveWeight ν a) (y*gaussianPositiveWeight ν b)) (by fun_prop)]
  have hsimp : ∀ p : ℝ×ℝ, max (x*gaussianPositiveWeight ν p.1)
      (y*gaussianPositiveWeight ν (-1*p.1+Real.sqrt (1-(-1)^2)*p.2))=
      x*gaussianPositiveWeight ν p.1+y*gaussianPositiveWeight ν (-p.1) := by
    intro p
    norm_num
    rcases le_or_gt p.1 0 with h|h
    · rw [gaussianPositiveWeight_of_nonpos ν hν h,mul_zero,zero_add]
      exact max_eq_right (mul_nonneg hy (gaussianPositiveWeight_nonneg ν hν _))
    · rw [gaussianPositiveWeight_of_nonpos ν hν (by linarith : -p.1≤0),mul_zero,add_zero]
      exact max_eq_left (mul_nonneg hx (gaussianPositiveWeight_nonneg ν hν _))
  simp_rw [hsimp]
  have hWm : Measurable (gaussianPositiveWeight ν) :=
    (positivePower_continuous ν hν).measurable.div_const _
  have hm : (gaussianReal 0 1).map (fun z : ℝ => -z)=gaussianReal 0 1 := by
    rw [gaussianReal_map_neg,neg_zero]
  have hneg : Integrable (fun z => gaussianPositiveWeight ν (-z)) (gaussianReal 0 1) := by
    have h : Integrable (gaussianPositiveWeight ν) ((gaussianReal 0 1).map (fun z : ℝ => -z)) := by
      rw [hm]; exact hWi
    exact (integrable_map_measure hWm.aestronglyMeasurable measurable_neg.aemeasurable).mp h
  rw [integral_prod _ ((((hWi.const_mul x).comp_fst (gaussianReal 0 1)).add
    ((hneg.const_mul y).comp_fst (gaussianReal 0 1))))]
  simp only [integral_const,measureReal_univ_eq_one,smul_eq_mul,one_mul]
  rw [integral_add (hWi.const_mul x) (hneg.const_mul y),integral_const_mul,integral_const_mul,
    gaussianPositiveWeight_mean ν hν,gaussianPositiveWeight_neg_mean ν hν]
  ring

theorem tEV_negative_one (ν : ℝ) (hν : 0<ν) :
    tEV ν (-1) hν ⟨le_rfl,by norm_num⟩=independence 2 := by
  apply ext_cdf_two
  intro u v
  rw [tEV,stableTailCopula_cdf,cdf_independence,Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
  unfold stableTailCDF
  split_ifs with h
  · rcases h with h|h <;> simp [h]
  · push_neg at h
    have hu : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (fun e => h.1 (Subtype.ext e.symm))
    have hv : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (fun e => h.2 (Subtype.ext e.symm))
    rw [tEVStableTail_negative_one ν hν (neg_nonneg.mpr (Real.log_nonpos u.property.1 u.property.2))
      (neg_nonneg.mpr (Real.log_nonpos v.property.1 v.property.2))]
    rw [neg_add,neg_neg,neg_neg,Real.exp_add,Real.exp_log hu,Real.exp_log hv]

end Verification
