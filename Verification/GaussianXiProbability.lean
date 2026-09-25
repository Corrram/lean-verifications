import Verification.GaussianConditional

/-! # A Gaussian representation for the squared conditional-CDF integral -/

open ProbabilityTheory MeasureTheory Set

namespace Verification

theorem charFunDual_standardNormal (L : StrongDual ℝ ℝ) :
    charFunDual (gaussianReal 0 1) L=Complex.exp (-((L 1)^2 : ℝ)/2) := by
  have he : charFunDual (gaussianReal 0 1) L=charFun (gaussianReal 0 1) (L 1) := by
    rw [charFunDual_apply,charFun_apply]
    congr 1
    funext x
    have hx : L x=x*L 1 := by simpa using L.map_smul x (1:ℝ)
    simp [hx,mul_comm]
  rw [he,charFun_gaussianReal]
  simp only [Complex.ofReal_zero,mul_zero,zero_mul,NNReal.coe_one,Complex.ofReal_one,
    one_mul,zero_sub,Complex.ofReal_pow,neg_div]

noncomputable def gaussianXiMap (r : ℝ) :
    ((ℝ×ℝ)×(ℝ×ℝ)) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  let b := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) (ℝ×ℝ))
  let x := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) (ℝ×ℝ))
  let y := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ×ℝ) (ℝ×ℝ))
  let z := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ×ℝ) (ℝ×ℝ))
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi
      ![(Real.sqrt 2)⁻¹ • (r • x-b+Real.sqrt (1-r^2) • y),
        (Real.sqrt 2)⁻¹ • (r • x-b+Real.sqrt (1-r^2) • z)])

theorem map_gaussianXiMap {r : ℝ} (hr : r∈Icc (-1) 1) :
    (((gaussianReal 0 1).prod (gaussianReal 0 1)).prod
      ((gaussianReal 0 1).prod (gaussianReal 0 1))).map (gaussianXiMap r)=
      multivariateGaussian 0 (bivariateCorrelation ((1+r^2)/2)) := by
  have hs : 0≤1-r^2 := by nlinarith [hr.1,hr.2]
  have hq : (1+r^2)/2∈Icc (-1) 1 := by constructor <;> nlinarith [sq_nonneg r]
  have hc : ((Real.sqrt 2)⁻¹)^2=(1:ℝ)/2 := by
    rw [inv_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  have hc' : ((Real.sqrt 2 : ℝ):ℂ)⁻¹^2=(1:ℂ)/2 := by
    rw [← Complex.ofReal_inv,← Complex.ofReal_pow,hc]
    norm_num
  have hs' : ((Real.sqrt (1-r^2) : ℝ):ℂ)^2=1-(r:ℂ)^2 := by
    have h := congrArg Complex.ofReal (Real.sq_sqrt hs)
    simpa using h
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_eq_charFunDual_toDualMap,charFunDual_map,charFunDual_prod,
    charFunDual_prod,charFunDual_prod,
    charFunDual_standardNormal,charFunDual_standardNormal,
    charFunDual_standardNormal,charFunDual_standardNormal,
    charFun_bivariateGaussian hq]
  simp [gaussianXiMap,PiLp.inner_apply,Fin.sum_univ_two]
  simp only [← Complex.exp_add]
  congr 1
  ring_nf
  rw [hc',hs']
  ring

end Verification
