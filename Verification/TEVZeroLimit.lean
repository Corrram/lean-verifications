import Verification.TEVLimits
import Verification.TEVStudentDensity
import Copula.Families.MarshallOlkin
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # The `ν → 0` limit of the t-EV family

The Student-t CDF with one degree of freedom is the Cauchy CDF `1/2+arctan(x)/π`, and
`T_k → T_1` locally uniformly in the argument as `k → 1`. Consequently the t-EV copulas
converge, as `ν → 0+`, to the Marshall–Olkin copula with equal weights
`α=β=1/2+arcsin(ρ)/π`.
-/

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem studentMarginalPDF_one (x : ℝ) : studentMarginalPDF 1 x=1/(Real.pi*(1+x^2)) := by
  rw [studentMarginalPDF_standard_form one_pos x]
  norm_num [Real.Gamma_one,Real.Gamma_one_half_eq]
  have hp : 0<1+x^2 := by positivity
  rw [Real.rpow_neg_one]
  have hs : Real.sqrt Real.pi*Real.sqrt Real.pi=Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  field_simp
  nlinarith [hs]

/-- The Cauchy CDF. -/
theorem studentTCDF_one (x : ℝ) : studentTCDF 1 x=1/2+Real.arctan x/Real.pi := by
  let F : ℝ → ℝ := fun y => studentTCDF 1 y-(1/2+Real.arctan y/Real.pi)
  have hd : ∀ y, HasDerivAt F 0 y := by
    intro y
    have h1 := studentTCDF_hasDerivAt 1 one_pos y
    have h2 := ((Real.hasDerivAt_arctan y).div_const Real.pi).const_add (1/2)
    convert h1.sub h2 using 1
    rw [studentMarginalPDF_one]
    field_simp
    ring
  have hc := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt) (fun y => (hd y).deriv) x 0
  have h0 : F 0=0 := by
    simp only [F,studentTCDF_zero 1 one_pos,Real.arctan_zero,zero_div,add_zero,sub_self]
  simp only [F] at hc h0
  linarith

/-- Normalizing constant of the Student density. -/
noncomputable def studentConst (k : ℝ) : ℝ :=
  Real.Gamma ((k+1)/2)/(Real.sqrt (k*Real.pi)*Real.Gamma (k/2))

theorem studentConst_continuousOn : ContinuousOn studentConst (Icc 1 2) := by
  intro k hk
  have hk0 : 0<k := by linarith [hk.1]
  apply ContinuousAt.continuousWithinAt
  unfold studentConst
  have hG (s : ℝ) (hs : 0<s) : ContinuousAt Real.Gamma s :=
    (Real.differentiableAt_Gamma (fun m => by
      have : (0:ℝ)≤m := Nat.cast_nonneg m; linarith)).continuousAt
  apply ContinuousAt.div
  · exact (hG _ (by positivity)).comp ((continuousAt_id.add continuousAt_const).div_const 2)
  · exact ((Real.continuous_sqrt.comp (continuous_id.mul continuous_const)).continuousAt).mul
      ((hG _ (by positivity)).comp (continuousAt_id.div_const 2))
  · have := Real.Gamma_pos_of_pos (show 0<k/2 by positivity)
    have := Real.sqrt_pos.mpr (show 0<k*Real.pi by positivity)
    positivity

theorem studentConst_bound : ∃ M, 0<M ∧ ∀ k ∈ Icc (1:ℝ) 2, studentConst k≤M := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn studentConst_continuousOn
  refine ⟨max M 1,by positivity,fun k hk => ?_⟩
  exact (le_abs_self _).trans ((hM k hk).trans (le_max_left _ _))

theorem studentMarginalPDF_le {k : ℝ} (hk : k∈Icc (1:ℝ) 2) {M : ℝ} (hM : studentConst k≤M) (t : ℝ) :
    studentMarginalPDF k t≤2*M/(1+t^2) := by
  have hk0 : 0<k := by linarith [hk.1]
  rw [studentMarginalPDF_standard_form hk0 t]
  have hb1 : 1≤1+t^2/k := by
    have : 0≤t^2/k := by positivity
    linarith
  have hpow : (1+t^2/k)^(-((k+1)/2))≤(1+t^2/k)⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hb1 (by linarith [hk.1])
  have hcmp : (1+t^2/k)⁻¹≤2/(1+t^2) := by
    rw [inv_eq_one_div,div_le_div_iff₀ (by positivity) (by positivity)]
    have : t^2/k≥t^2/2 := div_le_div_of_nonneg_left (sq_nonneg t) hk0 hk.2
    nlinarith
  have hc0 : 0≤studentConst k := by
    unfold studentConst
    have := Real.Gamma_pos_of_pos (show 0<(k+1)/2 by positivity)
    have := Real.Gamma_pos_of_pos (show 0<k/2 by positivity)
    positivity
  change studentConst k*(1+t^2/k)^(-((k+1)/2))≤2*M/(1+t^2)
  calc studentConst k*(1+t^2/k)^(-((k+1)/2))≤M*(2/(1+t^2)) :=
        mul_le_mul hM (hpow.trans hcmp) (by positivity) (by linarith)
    _ = 2*M/(1+t^2) := by ring

theorem studentMarginalPDF_continuousAt_df (t : ℝ) {k : ℝ} (hk : 0<k) :
    ContinuousAt (fun k => studentMarginalPDF k t) k := by
  have he : ∀ᶠ k' in 𝓝 k, studentMarginalPDF k' t=studentConst k'*(1+t^2/k')^(-((k'+1)/2)) := by
    filter_upwards [lt_mem_nhds hk] with k' hk'
    exact studentMarginalPDF_standard_form hk' t
  apply ContinuousAt.congr _ (EventuallyEq.symm he)
  have hG (s : ℝ) (hs : 0<s) : ContinuousAt Real.Gamma s :=
    (Real.differentiableAt_Gamma (fun m => by
      have : (0:ℝ)≤m := Nat.cast_nonneg m; linarith)).continuousAt
  apply ContinuousAt.mul
  · unfold studentConst
    apply ContinuousAt.div
    · exact (hG _ (by positivity)).comp ((continuousAt_id.add continuousAt_const).div_const 2)
    · exact ((Real.continuous_sqrt.comp (continuous_id.mul continuous_const)).continuousAt).mul
        ((hG _ (by positivity)).comp (continuousAt_id.div_const 2))
    · have := Real.Gamma_pos_of_pos (show 0<k/2 by positivity)
      have := Real.sqrt_pos.mpr (show 0<k*Real.pi by positivity)
      positivity
  · apply ContinuousAt.rpow
    · exact continuousAt_const.add (continuousAt_const.div continuousAt_id hk.ne')
    · exact ((continuousAt_id.add continuousAt_const).div_const 2).neg
    · left; positivity


theorem studentTCDF_eq_integral_indicator (k : ℝ) (hk : 0<k) (x : ℝ) :
    studentTCDF k x=∫ t, (Iic x).indicator (studentMarginalPDF k) t := by
  rw [studentTCDF_eq_integral_Iic k hk x,integral_indicator measurableSet_Iic]

/-- Continuity of `T_k(x)` in `(k,x)` at `k=1`. -/
theorem studentTCDF_tendsto_df {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (k x : ι → ℝ) (hk : ∀ i, k i∈Icc (1:ℝ) 2) (hkl : Tendsto k l (𝓝 1)) {x0 : ℝ}
    (hx : Tendsto x l (𝓝 x0)) :
    Tendsto (fun i => studentTCDF (k i) (x i)) l (𝓝 (studentTCDF 1 x0)) := by
  obtain ⟨M,hM0,hM⟩ := studentConst_bound
  have hk0 (i : ι) : 0<k i := by linarith [(hk i).1]
  simp_rw [studentTCDF_eq_integral_indicator _ (hk0 _),studentTCDF_eq_integral_indicator 1 one_pos]
  apply tendsto_integral_filter_of_dominated_convergence (fun t => 2*M*(1+t^2)⁻¹)
  · exact Eventually.of_forall fun i =>
      ((studentMarginalPDF_continuous _ (hk0 i)).measurable.indicator measurableSet_Iic).aestronglyMeasurable
  · refine Eventually.of_forall fun i => Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs]
    by_cases ht : t∈Iic (x i)
    · rw [indicator_of_mem ht,abs_of_nonneg (studentMarginalPDF_pos (hk0 i) t).le]
      have := studentMarginalPDF_le (hk i) (hM (k i) (hk i)) t
      rwa [div_eq_mul_inv] at this
    · rw [indicator_of_notMem ht,abs_zero]; positivity
  · exact (integrable_inv_one_add_sq).const_mul _
  · filter_upwards [Measure.ae_ne volume x0] with t ht
    have hpdf : Tendsto (fun i => studentMarginalPDF (k i) t) l (𝓝 (studentMarginalPDF 1 t)) :=
      (studentMarginalPDF_continuousAt_df t one_pos).tendsto.comp hkl
    rcases lt_or_gt_of_ne ht with h|h
    · rw [indicator_of_mem (show t∈Iic x0 from h.le)]
      apply hpdf.congr'
      filter_upwards [hx.eventually (lt_mem_nhds h)] with i hi
      rw [indicator_of_mem (show t∈Iic (x i) from hi.le)]
    · rw [indicator_of_notMem (show t∉Iic x0 from not_le.mpr h)]
      apply tendsto_const_nhds.congr'
      filter_upwards [hx.eventually (gt_mem_nhds h)] with i hi
      rw [indicator_of_notMem (show t∉Iic (x i) from not_le.mpr hi)]

/-- `T_k(x)→1` as `k→1` and `x→∞`. -/
theorem studentTCDF_tendsto_df_atTop {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (k x : ι → ℝ) (hk : ∀ i, k i∈Icc (1:ℝ) 2) (hkl : Tendsto k l (𝓝 1))
    (hx : Tendsto x l atTop) :
    Tendsto (fun i => studentTCDF (k i) (x i)) l (𝓝 1) := by
  obtain ⟨M,hM0,hM⟩ := studentConst_bound
  have hk0 (i : ι) : 0<k i := by linarith [(hk i).1]
  simp_rw [studentTCDF_eq_integral_indicator _ (hk0 _)]
  rw [← studentMarginalPDF_integral 1 one_pos]
  apply tendsto_integral_filter_of_dominated_convergence (fun t => 2*M*(1+t^2)⁻¹)
  · exact Eventually.of_forall fun i =>
      ((studentMarginalPDF_continuous _ (hk0 i)).measurable.indicator measurableSet_Iic).aestronglyMeasurable
  · refine Eventually.of_forall fun i => Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs]
    by_cases ht : t∈Iic (x i)
    · rw [indicator_of_mem ht,abs_of_nonneg (studentMarginalPDF_pos (hk0 i) t).le]
      have := studentMarginalPDF_le (hk i) (hM (k i) (hk i)) t
      rwa [div_eq_mul_inv] at this
    · rw [indicator_of_notMem ht,abs_zero]; positivity
  · exact (integrable_inv_one_add_sq).const_mul _
  · refine Eventually.of_forall fun t => ?_
    have hpdf : Tendsto (fun i => studentMarginalPDF (k i) t) l (𝓝 (studentMarginalPDF 1 t)) :=
      (studentMarginalPDF_continuousAt_df t one_pos).tendsto.comp hkl
    apply hpdf.congr'
    filter_upwards [hx.eventually_ge_atTop t] with i hi
    rw [indicator_of_mem (show t∈Iic (x i) from hi)]

theorem arctan_tEV_half {r : ℝ} (hr : r∈Ioo (-1) 1) :
    Real.arctan (Real.sqrt (1-r^2)/(1+r))=Real.pi/4-Real.arcsin r/2 := by
  set θ := Real.pi/4-Real.arcsin r/2
  have ha := Real.neg_pi_div_two_le_arcsin r
  have hb := Real.arcsin_le_pi_div_two r
  have hθ1 : -(Real.pi/2)<θ := by simp only [θ]; linarith [Real.pi_pos]
  have hθ2 : θ<Real.pi/2 := by
    have : -(Real.pi/2)<Real.arcsin r := by
      exact Real.neg_pi_div_two_lt_arcsin.mpr hr.1
    simp only [θ]; linarith [Real.pi_pos]
  have hc2 : Real.cos (2*θ)=r := by
    rw [show 2*θ=Real.pi/2-Real.arcsin r by simp only [θ]; ring,Real.cos_pi_div_two_sub,
      Real.sin_arcsin hr.1.le hr.2.le]
  have hs2 : Real.sin (2*θ)=Real.sqrt (1-r^2) := by
    rw [show 2*θ=Real.pi/2-Real.arcsin r by simp only [θ]; ring,Real.sin_pi_div_two_sub,
      Real.cos_arcsin]
  have hcos : 0<Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨hθ1,hθ2⟩
  have htan : Real.tan θ=Real.sqrt (1-r^2)/(1+r) := by
    rw [← hs2,← hc2,Real.sin_two_mul,Real.cos_two_mul,Real.tan_eq_sin_div_cos]
    field_simp
    ring
  rw [← htan,Real.arctan_tan hθ1 hθ2]

theorem tEVArg_one_zero_limit {r : ℝ} (hr : r∈Ioo (-1) 1) :
    Real.sqrt ((1+0)/(1-r^2))*(1-r)=Real.sqrt (1-r^2)/(1+r) := by
  have hs : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  have h1 : 0<1+r := by linarith [hr.1]
  have hq := Real.sqrt_pos.mpr hs
  rw [add_zero,Real.sqrt_div zero_le_one,Real.sqrt_one]
  field_simp
  rw [Real.sq_sqrt hs.le]
  ring


/-- The common Marshall–Olkin weight of the `ν → 0` limit. -/
noncomputable def tEVZeroWeight (r : ℝ) : ℝ := 1/2+Real.arcsin r/Real.pi

theorem tEVZeroWeight_mem (r : ℝ) : tEVZeroWeight r∈Icc (0:ℝ) 1 := by
  have ha := Real.neg_pi_div_two_le_arcsin r
  have hb := Real.arcsin_le_pi_div_two r
  have hp := Real.pi_pos
  unfold tEVZeroWeight
  constructor
  · have : -(1/2:ℝ)≤Real.arcsin r/Real.pi := by
      rw [le_div_iff₀ hp]; linarith
    linarith
  · have : Real.arcsin r/Real.pi≤1/2 := by
      rw [div_le_iff₀ hp]; linarith
    linarith

noncomputable def tEVZeroWeightI (r : ℝ) : I := ⟨tEVZeroWeight r,tEVZeroWeight_mem r⟩

/-- Marshall–Olkin with equal weights in exponential coordinates. -/
theorem marshallOlkin_equal_exp (a : I) {x y : ℝ} (hx : 0<x) (hy : 0<y) :
    (marshallOlkin a a).cdf ![⟨Real.exp (-x),(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (by linarith)⟩,
      ⟨Real.exp (-y),(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (by linarith)⟩]=
      Real.exp (-(max x y+(1-(a:ℝ))*min x y)) := by
  have ha : 0≤(a:ℝ) := a.property.1
  rw [cdf_marshallOlkin]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [← Real.exp_mul]
  rcases le_total x y with hxy|hxy
  · rw [min_eq_right (Real.exp_le_exp.mpr (by nlinarith : -y*(a:ℝ)≤-x*a)),← Real.exp_add,
      ← Real.exp_add,max_eq_right hxy,min_eq_left hxy]
    congr 1
    ring
  · rw [min_eq_left (Real.exp_le_exp.mpr (by nlinarith : -x*(a:ℝ)≤-y*a)),← Real.exp_add,
      ← Real.exp_add,max_eq_left hxy,min_eq_right hxy]
    congr 1
    ring

theorem studentTCDF_one_neg_arcsin {r : ℝ} (hr : r∈Ioo (-1) 1) :
    studentTCDF 1 (Real.sqrt ((1+0)/(1-r^2))*(0-r))=1-tEVZeroWeight r := by
  have hs : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  have hq := Real.sqrt_pos.mpr hs
  have he : Real.sqrt ((1+0)/(1-r^2))*(0-r)=-(r/Real.sqrt (1-r^2)) := by
    rw [add_zero,Real.sqrt_div zero_le_one,Real.sqrt_one]; field_simp; ring
  rw [he,studentTCDF_one,Real.arctan_neg,← Real.arcsin_eq_arctan hr]
  unfold tEVZeroWeight
  ring

theorem studentTCDF_one_half_limit {r : ℝ} (hr : r∈Ioo (-1) 1) :
    studentTCDF 1 (Real.sqrt ((1+0)/(1-r^2))*(1-r))=1-tEVZeroWeight r/2 := by
  rw [tEVArg_one_zero_limit hr,studentTCDF_one,arctan_tEV_half hr]
  unfold tEVZeroWeight
  have := Real.pi_pos
  field_simp
  ring

theorem tEVArg_zero_limit_finite {ι : Type*} {l : Filter ι} (ν : ι → ℝ) (hνl : Tendsto ν l (𝓝 0))
    (r : ℝ) {w : ι → ℝ} {w0 : ℝ} (hw : Tendsto w l (𝓝 w0)) :
    Tendsto (fun i => tEVArg (ν i) r (w i)) l (𝓝 (Real.sqrt ((1+0)/(1-r^2))*(w0-r))) := by
  unfold tEVArg
  apply Tendsto.mul _ (hw.sub_const r)
  exact (Real.continuous_sqrt.tendsto _).comp ((hνl.const_add 1).div_const _)

theorem tEVArg_zero_limit_atTop {ι : Type*} {l : Filter ι} (ν : ι → ℝ) (hνl : Tendsto ν l (𝓝 0))
    {r : ℝ} (hr : r∈Ioo (-1) 1) {w : ι → ℝ} (hw : Tendsto w l atTop) :
    Tendsto (fun i => tEVArg (ν i) r (w i)) l atTop := by
  have hs : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  unfold tEVArg
  apply Tendsto.pos_mul_atTop (Real.sqrt_pos.mpr (show (0:ℝ)<(1+0)/(1-r^2) by positivity))
  · exact (Real.continuous_sqrt.tendsto _).comp ((hνl.const_add 1).div_const _)
  · exact tendsto_atTop_add_const_right _ (-r) hw |>.congr fun i => by ring

/-- Table 4 audit: as `ν → 0+`, the t-EV copula tends pointwise to the Marshall–Olkin copula
with equal weights `1/2+arcsin(ρ)/π`. -/
theorem tEV_tendsto_marshallOlkin {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (ν : ι → ℝ) (hν : ∀ i, 0<ν i) (hν1 : ∀ i, ν i≤1) (hνl : Tendsto ν l (𝓝 0))
    {r : ℝ} (hr : r∈Ioo (-1) 1) (u v : I) :
    Tendsto (fun i => (tEV (ν i) r (hν i) ⟨hr.1.le,hr.2.le⟩).cdf ![u,v]) l
      (𝓝 ((marshallOlkin (tEVZeroWeightI r) (tEVZeroWeightI r)).cdf ![u,v])) := by
  set a := tEVZeroWeightI r
  have hk : ∀ i, ν i+1∈Icc (1:ℝ) 2 := fun i => ⟨by linarith [hν i],by linarith [hν1 i]⟩
  have hkl : Tendsto (fun i => ν i+1) l (𝓝 1) := by simpa using hνl.add_const 1
  have hinv : Tendsto (fun i => 1/ν i) l atTop := by
    have : Tendsto ν l (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hνl,Eventually.of_forall hν⟩
    simpa only [one_div,Function.comp_def] using tendsto_inv_nhdsGT_zero.comp this
  -- boundary cases
  by_cases hu0 : u=0
  · subst hu0
    rw [(marshallOlkin a a).cdf_eq_zero_of_coord_eq_zero _ 0 rfl]
    exact tendsto_const_nhds.congr fun i => ((tEV (ν i) r (hν i) _).cdf_eq_zero_of_coord_eq_zero _ 0 rfl).symm
  by_cases hv0 : v=0
  · subst hv0
    rw [(marshallOlkin a a).cdf_eq_zero_of_coord_eq_zero _ 1 rfl]
    exact tendsto_const_nhds.congr fun i => ((tEV (ν i) r (hν i) _).cdf_eq_zero_of_coord_eq_zero _ 1 rfl).symm
  by_cases hu1 : u=1
  · subst hu1
    simp only [cdf_two_one_left]
    exact tendsto_const_nhds
  by_cases hv1 : v=1
  · subst hv1
    simp only [cdf_two_one_right]
    exact tendsto_const_nhds
  have hu : (u:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨lt_of_le_of_ne u.property.1 (fun e => hu0 (Subtype.ext e.symm)),
      lt_of_le_of_ne u.property.2 (fun e => hu1 (Subtype.ext e))⟩
  have hv : (v:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨lt_of_le_of_ne v.property.1 (fun e => hv0 (Subtype.ext e.symm)),
      lt_of_le_of_ne v.property.2 (fun e => hv1 (Subtype.ext e))⟩
  simp_rw [tEV_cdf_interior _ r _ hr u v hu hv]
  set x := -Real.log (u:ℝ)
  set y := -Real.log (v:ℝ)
  have hx : 0<x := neg_pos.mpr (Real.log_neg hu.1 hu.2)
  have hy : 0<y := neg_pos.mpr (Real.log_neg hv.1 hv.2)
  have hue : u=⟨Real.exp (-x),(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (by linarith)⟩ :=
    Subtype.ext (by simp [x,Real.exp_log hu.1])
  have hve : v=⟨Real.exp (-y),(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (by linarith)⟩ :=
    Subtype.ext (by simp [y,Real.exp_log hv.1])
  have htarget := marshallOlkin_equal_exp a hx hy
  rw [← hue,← hve] at htarget
  rw [htarget]
  apply Real.continuous_exp.continuousAt.tendsto.comp
  apply Tendsto.neg
  -- the two Student-t terms
  have hlarge {c : ℝ} (hc : 1<c) :
      Tendsto (fun i => studentTCDF (ν i+1) (tEVArg (ν i) r (c^(1/ν i)))) l (𝓝 1) :=
    studentTCDF_tendsto_df_atTop _ _ hk hkl
      (tEVArg_zero_limit_atTop ν hνl hr ((tendsto_rpow_atTop_of_base_gt_one c hc).comp hinv))
  have hsmall {c : ℝ} (hc0 : 0<c) (hc : c<1) :
      Tendsto (fun i => studentTCDF (ν i+1) (tEVArg (ν i) r (c^(1/ν i)))) l (𝓝 (1-(a:ℝ))) := by
    have h := studentTCDF_tendsto_df _ _ hk hkl
      (tEVArg_zero_limit_finite ν hνl r ((tendsto_rpow_atTop_of_base_lt_one c (by linarith) hc).comp hinv))
    rwa [studentTCDF_one_neg_arcsin hr] at h
  rcases lt_trichotomy y x with hxy|hxy|hxy
  · rw [max_eq_left hxy.le,min_eq_right hxy.le]
    have h1 := hlarge ((one_lt_div hy).mpr hxy)
    have h2 := hsmall (div_pos hy hx) ((div_lt_one hx).mpr hxy)
    convert (h1.const_mul x).add (h2.const_mul y) using 2
    ring
  · rw [hxy,max_self,min_self]
    have he (i : ι) : (x/x)^(1/ν i)=1 := by rw [div_self hx.ne',Real.one_rpow]
    simp_rw [he]
    have h := studentTCDF_tendsto_df _ _ hk hkl (tEVArg_zero_limit_finite ν hνl r
      (tendsto_const_nhds (x := (1:ℝ))))
    rw [studentTCDF_one_half_limit hr] at h
    convert (h.const_mul x).add (h.const_mul x) using 2
    ring_nf
    rfl
  · rw [max_eq_right hxy.le,min_eq_left hxy.le]
    have h1 := hsmall (div_pos hx hy) ((div_lt_one hy).mpr hxy)
    have h2 := hlarge ((one_lt_div hx).mpr hxy)
    convert (h1.const_mul x).add (h2.const_mul y) using 2
    ring

end Verification
