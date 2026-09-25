import Verification.TEVConstruction
import Verification.TEVStudentCDF
import Verification.GaussianRepresentation

/-! # The t-EV Pickands function in Student-t form

For `-1<r<1` and `ν>0`, the spectral t-EV construction of `TEVConstruction.lean` has
stable tail function
`L(x,y)=x T_{ν+1}(k((x/y)^(1/ν)-r))+y T_{ν+1}(k((y/x)^(1/ν)-r))`,
`k=sqrt((1+ν)/(1-r²))`, for positive `x,y`. Consequently its Pickands function is the
expression printed in Tables 1 and 4 of Ansari–Rockel.
-/

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped unitInterval

namespace Verification

/-! ## Two Gaussian representations -/

noncomputable def gaussianMixSwap (r : ℝ) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (![r • EuclideanSpace.proj 0+Real.sqrt (1-r^2) • EuclideanSpace.proj 1,
      EuclideanSpace.proj 0]))

noncomputable def gaussianMixSwapRow (r : ℝ) (i : Fin 2) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (!![r,Real.sqrt (1-r^2);1,0] i)

theorem gaussianMixSwap_inner (r : ℝ) (i : Fin 2) :
    (fun u => inner (𝕜 := ℝ) ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis i) u) ∘
      gaussianMixSwap r = fun u => inner (𝕜 := ℝ) (gaussianMixSwapRow r i) u := by
  funext u
  fin_cases i <;> simp [gaussianMixSwap,gaussianMixSwapRow,PiLp.inner_apply,Fin.sum_univ_two]
  ring

theorem map_gaussianMixSwap {r : ℝ} (hr : r∈Icc (-1) 1) :
    (stdGaussian (EuclideanSpace ℝ (Fin 2))).map (gaussianMixSwap r)=
      multivariateGaussian 0 (bivariateCorrelation r) := by
  have hs : 0≤1-r^2 := by nlinarith [hr.1,hr.2]
  have hsq := Real.sq_sqrt hs
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map,integral_id_stdGaussian,map_zero,integral_id_multivariateGaussian]
    exact IsGaussian.integrable_id
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis fun i j => ?_
  rw [ContinuousLinearMap.toBilinForm_apply,ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov,covariance_map]
  · rw [gaussianMixSwap_inner,gaussianMixSwap_inner,
      ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian,innerSL_apply_apply,
      covarianceBilin_multivariateGaussian (bivariateCorrelation_posSemidef hr)]
    simp only [PiLp.inner_apply]
    fin_cases i <;> fin_cases j <;>
      simp [gaussianMixSwapRow,bivariateCorrelation,Fin.sum_univ_two]
    nlinarith
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id

theorem integral_bivariateGaussian_mix {r : ℝ} (hr : r∈Icc (-1) 1) (F : ℝ → ℝ → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    (∫ z, F (z 0) (z 1) ∂multivariateGaussian 0 (bivariateCorrelation r))=
      ∫ p : ℝ×ℝ, F p.1 (r*p.1+Real.sqrt (1-r^2)*p.2) ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := by
  have hFz : Measurable (fun z : EuclideanSpace ℝ (Fin 2) => F (z 0) (z 1)) :=
    hF.comp (by fun_prop)
  rw [← map_gaussianMix hr,← map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) hFz.aestronglyMeasurable,
    ← (measurePreserving_finTwoArrow (gaussianReal 0 1)).integral_comp' ]
  congr 1
  funext x
  simp [gaussianMix,MeasurableEquiv.finTwoArrow]

theorem integral_bivariateGaussian_mixSwap {r : ℝ} (hr : r∈Icc (-1) 1) (F : ℝ → ℝ → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    (∫ z, F (z 0) (z 1) ∂multivariateGaussian 0 (bivariateCorrelation r))=
      ∫ p : ℝ×ℝ, F (r*p.1+Real.sqrt (1-r^2)*p.2) p.1 ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := by
  have hFz : Measurable (fun z : EuclideanSpace ℝ (Fin 2) => F (z 0) (z 1)) :=
    hF.comp (by fun_prop)
  rw [← map_gaussianMixSwap hr,← map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) hFz.aestronglyMeasurable,
    ← (measurePreserving_finTwoArrow (gaussianReal 0 1)).integral_comp' ]
  congr 1
  funext x
  simp [gaussianMixSwap,MeasurableEquiv.finTwoArrow]

/-! ## Pointwise threshold identities -/

theorem gaussianPositiveWeight_le_iff (ν : ℝ) (hν : 0<ν) {κ a : ℝ} (hκ : 0<κ) (ha : 0<a) (z : ℝ) :
    gaussianPositiveWeight ν z≤κ*gaussianPositiveWeight ν a ↔ z≤κ^(1/ν)*a := by
  have hm := gaussianPositiveMoment_pos ν hν
  have hc : 0<κ^(1/ν)*a := mul_pos (Real.rpow_pos_of_pos hκ _) ha
  have hpow : κ*a^ν=(κ^(1/ν)*a)^ν := by
    rw [Real.mul_rpow (Real.rpow_nonneg hκ.le _) ha.le,← Real.rpow_mul hκ.le,
      one_div_mul_cancel hν.ne',Real.rpow_one]
  unfold gaussianPositiveWeight positivePower
  rw [max_eq_left ha.le,mul_div_assoc',div_le_div_iff_of_pos_right hm,hpow,
    Real.rpow_le_rpow_iff (le_max_right _ _) hc.le hν,max_le_iff]
  exact ⟨fun h => h.1,fun h => ⟨h,hc.le⟩⟩

theorem gaussianPositiveWeight_lt_iff (ν : ℝ) (hν : 0<ν) {κ a : ℝ} (hκ : 0<κ) (ha : 0<a) (z : ℝ) :
    gaussianPositiveWeight ν z<κ*gaussianPositiveWeight ν a ↔ z<κ^(1/ν)*a := by
  have hm := gaussianPositiveMoment_pos ν hν
  have hc : 0<κ^(1/ν)*a := mul_pos (Real.rpow_pos_of_pos hκ _) ha
  have hpow : κ*a^ν=(κ^(1/ν)*a)^ν := by
    rw [Real.mul_rpow (Real.rpow_nonneg hκ.le _) ha.le,← Real.rpow_mul hκ.le,
      one_div_mul_cancel hν.ne',Real.rpow_one]
  unfold gaussianPositiveWeight positivePower
  rw [max_eq_left ha.le,mul_div_assoc',div_lt_div_iff_of_pos_right hm,hpow,
    Real.rpow_lt_rpow_iff (le_max_right _ _) hc.le hν,max_lt_iff]
  exact ⟨fun h => h.1,fun h => ⟨h,hc⟩⟩

theorem gaussianPositiveWeight_of_nonpos (ν : ℝ) (hν : 0<ν) {a : ℝ} (ha : a≤0) :
    gaussianPositiveWeight ν a=0 := by
  simp [gaussianPositiveWeight,positivePower,max_eq_right ha,Real.zero_rpow hν.ne']

theorem standardGaussian_linear_halfline_strict {s : ℝ} (hs : 0<s) (b : ℝ) :
    (∫ y, (if s*y<b then (1:ℝ) else 0) ∂gaussianReal 0 1)=
      ProbabilityTheory.cdf (gaussianReal 0 1) (b/s) := by
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  rw [← standardGaussian_linear_halfline hs b]
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne (gaussianReal 0 1) (b/s)] with y hy
  have hne : s*y≠b := by
    intro h
    apply hy
    rw [← h]
    field_simp
  by_cases h : s*y<b
  · simp [h,h.le]
  · have h' : ¬ s*y≤b := fun k => h (lt_of_le_of_ne k hne)
    simp [h,h']

/-! ## Conditional evaluation -/

theorem tEV_weighted_normalCDF (ν : ℝ) (hν : 0<ν) (q : ℝ) :
    (∫ a, gaussianPositiveWeight ν a*ProbabilityTheory.cdf (gaussianReal 0 1) (q*a) ∂gaussianReal 0 1)=
      studentTCDF (ν+1) (q*Real.sqrt (ν+1)) := by
  have hm := gaussianPositiveMoment_pos ν hν
  unfold gaussianPositiveWeight
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div,positivePower_normalCDF_integral ν hν q]
  field_simp

theorem integrable_weight_indicator (ν : ℝ) (hν : 0<ν) (P : ℝ×ℝ → Prop) [DecidablePred P]
    (hP : MeasurableSet {p | P p}) :
    Integrable (fun p : ℝ×ℝ => gaussianPositiveWeight ν p.1*(if P p then (1:ℝ) else 0))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hW : Integrable (fun p : ℝ×ℝ => gaussianPositiveWeight ν p.1)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (gaussianPositiveWeight_integrable ν hν).comp_fst _
  apply hW.mono'
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · exact ((positivePower_continuous ν hν).measurable.div_const _).comp measurable_fst
    · exact Measurable.ite hP measurable_const measurable_const
  · filter_upwards [] with p
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (gaussianPositiveWeight_nonneg ν hν _)]
    by_cases h : P p <;> simp [h,gaussianPositiveWeight_nonneg ν hν]

/-- The conditional threshold integral with a non-strict comparison. -/
theorem tEV_threshold_le (ν r : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) {κ : ℝ} (hκ : 0<κ) :
    (∫ p : ℝ×ℝ, gaussianPositiveWeight ν p.1*
      (if gaussianPositiveWeight ν (r*p.1+Real.sqrt (1-r^2)*p.2)≤κ*gaussianPositiveWeight ν p.1
        then (1:ℝ) else 0) ∂(gaussianReal 0 1).prod (gaussianReal 0 1))=
      studentTCDF (ν+1) ((κ^(1/ν)-r)/Real.sqrt (1-r^2)*Real.sqrt (ν+1)) := by
  have hs : 0<Real.sqrt (1-r^2) := Real.sqrt_pos.mpr (by nlinarith [hr.1,hr.2])
  have hWm : Measurable (gaussianPositiveWeight ν) :=
    (positivePower_continuous ν hν).measurable.div_const _
  rw [integral_prod _ (integrable_weight_indicator ν hν _ (measurableSet_le
    (hWm.comp (by fun_prop)) ((hWm.comp measurable_fst).const_mul κ)))]
  rw [← tEV_weighted_normalCDF ν hν]
  congr 1
  funext a
  by_cases ha : a≤0
  · simp [gaussianPositiveWeight_of_nonpos ν hν ha]
  have ha' : 0<a := lt_of_not_ge ha
  rw [integral_const_mul]
  congr 1
  have he : (fun b => if gaussianPositiveWeight ν (r*a+Real.sqrt (1-r^2)*b)≤
      κ*gaussianPositiveWeight ν a then (1:ℝ) else 0)=
      fun b => if Real.sqrt (1-r^2)*b≤κ^(1/ν)*a-r*a then (1:ℝ) else 0 := by
    funext b
    congr 1
    apply propext
    rw [gaussianPositiveWeight_le_iff ν hν hκ ha']
    constructor <;> intro h <;> linarith
  rw [he,standardGaussian_linear_halfline hs]
  congr 1
  field_simp
  ring

/-- The conditional threshold integral with a strict comparison. -/
theorem tEV_threshold_lt (ν r : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) {κ : ℝ} (hκ : 0<κ) :
    (∫ p : ℝ×ℝ, gaussianPositiveWeight ν p.1*
      (if gaussianPositiveWeight ν (r*p.1+Real.sqrt (1-r^2)*p.2)<κ*gaussianPositiveWeight ν p.1
        then (1:ℝ) else 0) ∂(gaussianReal 0 1).prod (gaussianReal 0 1))=
      studentTCDF (ν+1) ((κ^(1/ν)-r)/Real.sqrt (1-r^2)*Real.sqrt (ν+1)) := by
  have hs : 0<Real.sqrt (1-r^2) := Real.sqrt_pos.mpr (by nlinarith [hr.1,hr.2])
  have hWm : Measurable (gaussianPositiveWeight ν) :=
    (positivePower_continuous ν hν).measurable.div_const _
  rw [integral_prod _ (integrable_weight_indicator ν hν _ (measurableSet_lt
    (hWm.comp (by fun_prop)) ((hWm.comp measurable_fst).const_mul κ)))]
  rw [← tEV_weighted_normalCDF ν hν]
  congr 1
  funext a
  by_cases ha : a≤0
  · simp [gaussianPositiveWeight_of_nonpos ν hν ha]
  have ha' : 0<a := lt_of_not_ge ha
  rw [integral_const_mul]
  congr 1
  have he : (fun b => if gaussianPositiveWeight ν (r*a+Real.sqrt (1-r^2)*b)<
      κ*gaussianPositiveWeight ν a then (1:ℝ) else 0)=
      fun b => if Real.sqrt (1-r^2)*b<κ^(1/ν)*a-r*a then (1:ℝ) else 0 := by
    funext b
    congr 1
    apply propext
    rw [gaussianPositiveWeight_lt_iff ν hν hκ ha']
    constructor <;> intro h <;> linarith
  rw [he,standardGaussian_linear_halfline_strict hs]
  congr 1
  field_simp
  ring

/-! ## The stable tail function -/

/-- The argument `z` of the t-EV Pickands function, written for a ratio `σ`. -/
noncomputable def tEVArg (ν r σ : ℝ) : ℝ := Real.sqrt ((1+ν)/(1-r^2))*(σ-r)

theorem tEVArg_eq (ν r σ : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) :
    (σ-r)/Real.sqrt (1-r^2)*Real.sqrt (ν+1)=tEVArg ν r σ := by
  have hs : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  unfold tEVArg
  rw [Real.sqrt_div (by linarith),add_comm 1 ν]
  have := Real.sqrt_pos.mpr hs
  field_simp

private theorem max_split (p q : ℝ) :
    max p q=p*(if q≤p then (1:ℝ) else 0)+q*(if p<q then (1:ℝ) else 0) := by
  by_cases h : q≤p
  · simp [h,not_lt.mpr h,max_eq_left h]
  · have h' : p<q := lt_of_not_ge h
    simp [h,h',max_eq_right h'.le]

theorem tEVStableTail_formula (ν r : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) {x y : ℝ}
    (hx : 0<x) (hy : 0<y) :
    (tEVStableTail ν r hν ⟨hr.1.le,hr.2.le⟩).value x y=
      x*studentTCDF (ν+1) (tEVArg ν r ((x/y)^(1/ν)))+
      y*studentTCDF (ν+1) (tEVArg ν r ((y/x)^(1/ν))) := by
  have hr' : r∈Icc (-1) 1 := ⟨hr.1.le,hr.2.le⟩
  have hWm : Measurable (gaussianPositiveWeight ν) :=
    (positivePower_continuous ν hν).measurable.div_const _
  set W := gaussianPositiveWeight ν
  let N := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)
  have hI (i : Fin 2) := gaussianPositiveWeight_coordinate_integrable ν r hν hr' i
  -- split the maximum
  have hsplit : (tEVStableTail ν r hν hr').value x y=
      x*(∫ z, W (z 0)*(if y*W (z 1)≤x*W (z 0) then (1:ℝ) else 0) ∂N)+
      y*(∫ z, W (z 1)*(if x*W (z 0)<y*W (z 1) then (1:ℝ) else 0) ∂N) := by
    change (∫ z, max (x*W (z 0)) (y*W (z 1)) ∂N)=_
    have hm0 : Measurable (fun z : EuclideanSpace ℝ (Fin 2) => W (z 0)) := hWm.comp (by fun_prop)
    have hm1 : Measurable (fun z : EuclideanSpace ℝ (Fin 2) => W (z 1)) := hWm.comp (by fun_prop)
    have hi1 : Integrable (fun z : EuclideanSpace ℝ (Fin 2) =>
        x*W (z 0)*(if y*W (z 1)≤x*W (z 0) then (1:ℝ) else 0)) N := by
      apply ((hI 0).const_mul x).mono'
      · exact ((hm0.const_mul x).mul (Measurable.ite (measurableSet_le (hm1.const_mul y)
          (hm0.const_mul x)) measurable_const measurable_const)).aestronglyMeasurable
      · filter_upwards [] with z
        have h0 := gaussianPositiveWeight_nonneg ν hν (z 0)
        split_ifs <;> simp [abs_of_nonneg (mul_nonneg hx.le h0),abs_of_nonneg h0]
    have hi2 : Integrable (fun z : EuclideanSpace ℝ (Fin 2) =>
        y*W (z 1)*(if x*W (z 0)<y*W (z 1) then (1:ℝ) else 0)) N := by
      apply ((hI 1).const_mul y).mono'
      · exact ((hm1.const_mul y).mul (Measurable.ite (measurableSet_lt (hm0.const_mul x)
          (hm1.const_mul y)) measurable_const measurable_const)).aestronglyMeasurable
      · filter_upwards [] with z
        have h1 := gaussianPositiveWeight_nonneg ν hν (z 1)
        split_ifs <;> simp [abs_of_nonneg (mul_nonneg hy.le h1),abs_of_nonneg h1]
    simp_rw [max_split]
    rw [integral_add hi1 hi2,← integral_const_mul,← integral_const_mul]
    congr 1 <;> apply integral_congr_ae <;> filter_upwards [] with z <;> ring
  -- first term, conditioning on the first coordinate
  have h1 : (∫ z, W (z 0)*(if y*W (z 1)≤x*W (z 0) then (1:ℝ) else 0) ∂N)=
      studentTCDF (ν+1) (tEVArg ν r ((x/y)^(1/ν))) := by
    have hF : Measurable (Function.uncurry fun a b : ℝ =>
        W a*(if y*W b≤x*W a then (1:ℝ) else 0)) := by
      apply Measurable.mul (hWm.comp measurable_fst)
      exact Measurable.ite (measurableSet_le ((hWm.comp measurable_snd).const_mul y)
        ((hWm.comp measurable_fst).const_mul x)) measurable_const measurable_const
    rw [integral_bivariateGaussian_mix hr' (fun a b => W a*(if y*W b≤x*W a then (1:ℝ) else 0)) hF,
      ← tEVArg_eq ν r _ hν hr,← tEV_threshold_le ν r hν hr (div_pos hx hy)]
    congr 1
    funext p
    congr 2
    apply propext
    rw [div_mul_eq_mul_div,le_div_iff₀ hy,mul_comm]
  -- second term, conditioning on the second coordinate
  have h2 : (∫ z, W (z 1)*(if x*W (z 0)<y*W (z 1) then (1:ℝ) else 0) ∂N)=
      studentTCDF (ν+1) (tEVArg ν r ((y/x)^(1/ν))) := by
    have hF : Measurable (Function.uncurry fun a b : ℝ =>
        W b*(if x*W a<y*W b then (1:ℝ) else 0)) := by
      apply Measurable.mul (hWm.comp measurable_snd)
      exact Measurable.ite (measurableSet_lt ((hWm.comp measurable_fst).const_mul x)
        ((hWm.comp measurable_snd).const_mul y)) measurable_const measurable_const
    rw [integral_bivariateGaussian_mixSwap hr' (fun a b => W b*(if x*W a<y*W b then (1:ℝ) else 0)) hF,
      ← tEVArg_eq ν r _ hν hr,← tEV_threshold_lt ν r hν hr (div_pos hy hx)]
    congr 1
    funext p
    congr 2
    apply propext
    rw [div_mul_eq_mul_div,lt_div_iff₀ hx,mul_comm]
  rw [hsplit,h1,h2]

/-- The t-EV Pickands function on the open unit interval, as printed in Tables 1 and 4. -/
theorem tEV_pickands_formula (ν r : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) (t : I)
    (ht : (t:ℝ)∈Ioo (0:ℝ) 1) :
    copulaPickands (tEV ν r hν ⟨hr.1.le,hr.2.le⟩) t=
      (1-(t:ℝ))*studentTCDF (ν+1) (tEVArg ν r (((1-(t:ℝ))/(t:ℝ))^(1/ν)))+
      (t:ℝ)*studentTCDF (ν+1) (tEVArg ν r (((t:ℝ)/(1-(t:ℝ)))^(1/ν))) := by
  rw [tEV,stableTailCopula_pickands]
  exact tEVStableTail_formula ν r hν hr (by linarith [ht.2]) ht.1

/-- The t-EV CDF at interior points, as an extreme-value copula with the Student-t
stable tail function. -/
theorem tEV_cdf_interior (ν r : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) (u v : I)
    (hu : (u:ℝ)∈Ioo (0:ℝ) 1) (hv : (v:ℝ)∈Ioo (0:ℝ) 1) :
    (tEV ν r hν ⟨hr.1.le,hr.2.le⟩).cdf ![u,v]=Real.exp (-(
      (-Real.log (u:ℝ))*studentTCDF (ν+1)
        (tEVArg ν r (((-Real.log (u:ℝ))/(-Real.log (v:ℝ)))^(1/ν)))+
      (-Real.log (v:ℝ))*studentTCDF (ν+1)
        (tEVArg ν r (((-Real.log (v:ℝ))/(-Real.log (u:ℝ)))^(1/ν))))) := by
  rw [tEV,stableTailCopula_cdf,stableTailCDF_positive_coords _ _ _ hu.1 hv.1,
    tEVStableTail_formula ν r hν hr
      (neg_pos.mpr (Real.log_neg hu.1 hu.2)) (neg_pos.mpr (Real.log_neg hv.1 hv.2))]

end Verification
