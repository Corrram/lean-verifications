import Verification.TEVPickandsFormula
import Verification.GammaPrecisionConcentration
import Verification.GaussianQuadrant

/-! # Degrees-of-freedom limit of the t-EV family

For a fixed correlation `-1<r<1`, the t-EV copulas converge pointwise to the independence
copula as `ν → ∞`. In particular the Hüsler–Reiss family is not the fixed-correlation limit.
-/

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem studentTCDF_lower_bound (k : ℝ) (hk : 0<k) {z : ℝ} (hz : 0≤z) :
    ProbabilityTheory.cdf (gaussianReal 0 1) (z/2)*(1-(k/2)⁻¹/(3/4)^2)≤studentTCDF k z := by
  have hP : IsProbabilityMeasure (gammaMeasure (k/2) (k/2)) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by positivity)
  set Φ := ProbabilityTheory.cdf (gaussianReal 0 1)
  set S := {t : ℝ | (3/4:ℝ)≤|t-1|}
  have hS : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  have hbound := gammaPrecision_concentration_bound (a := k/2) (by positivity) (by norm_num : (0:ℝ)<3/4)
  have hpt : ∀ t, Φ (z/2)*Sᶜ.indicator (fun _ => (1:ℝ)) t≤Φ (z*Real.sqrt t) := by
    intro t
    by_cases ht : t∈S
    · rw [indicator_of_notMem (by simpa using ht),mul_zero]; exact ProbabilityTheory.cdf_nonneg _ _
    · rw [indicator_of_mem (by simpa using ht),mul_one]
      apply ProbabilityTheory.monotone_cdf
      have ht' : ¬ (3/4:ℝ)≤|t-1| := ht
      push Not at ht'
      have h1 : 1/4<t := by linarith [(abs_lt.mp ht').1]
      have h2 : 1/2≤Real.sqrt t := by
        rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
      nlinarith
  have hint : Integrable (fun t => Φ (z*Real.sqrt t)) (gammaMeasure (k/2) (k/2)) := by
    apply Integrable.of_bound (f := fun t => Φ (z*Real.sqrt t)) (by exact ((ProbabilityTheory.monotone_cdf (gaussianReal 0 1)).measurable.comp
      (measurable_const.mul Real.continuous_sqrt.measurable)).aestronglyMeasurable) 1
    exact Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (ProbabilityTheory.cdf_nonneg _ _)]
      exact ProbabilityTheory.cdf_le_one _ _
  calc Φ (z/2)*(1-(k/2)⁻¹/(3/4)^2)≤Φ (z/2)*(gammaMeasure (k/2) (k/2)).real Sᶜ := by
        apply mul_le_mul_of_nonneg_left _ (ProbabilityTheory.cdf_nonneg _ _)
        rw [measureReal_compl hS,probReal_univ]
        linarith
    _ = ∫ t, Φ (z/2)*Sᶜ.indicator (fun _ => (1:ℝ)) t ∂gammaMeasure (k/2) (k/2) := by
        rw [integral_const_mul,integral_indicator hS.compl,setIntegral_const,smul_eq_mul,mul_one]
    _ ≤ studentTCDF k z := by
        unfold studentTCDF
        exact integral_mono ((integrable_const _).indicator hS.compl |>.const_mul _) hint hpt

theorem studentTCDF_tendsto_one {ι : Type*} {l : Filter ι} (k z : ι → ℝ) (hk : ∀ i, 0<k i)
    (hkt : Tendsto k l atTop) (hzt : Tendsto z l atTop) :
    Tendsto (fun i => studentTCDF (k i) (z i)) l (𝓝 1) := by
  have hΦ : Tendsto (fun i => ProbabilityTheory.cdf (gaussianReal 0 1) (z i/2)) l (𝓝 1) :=
    (tendsto_cdf_atTop (gaussianReal 0 1)).comp (hzt.atTop_div_const (by norm_num))
  have hc : Tendsto (fun i => 1-(k i/2)⁻¹/(3/4:ℝ)^2) l (𝓝 1) := by
    have := ((tendsto_inv_atTop_zero.comp (hkt.atTop_div_const (by norm_num : (0:ℝ)<2))).div_const
      ((3/4:ℝ)^2))
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub this
  have hlow := hΦ.mul hc
  rw [mul_one] at hlow
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [hzt.eventually_ge_atTop 0] with i hi
    exact studentTCDF_lower_bound (k i) (hk i) hi
  · exact Eventually.of_forall fun i => studentTCDF_le_one (k i) (hk i) (z i)

theorem tEVArg_tendsto_atTop {ι : Type*} {l : Filter ι} (ν : ι → ℝ) (_hν : ∀ i, 0<ν i)
    (hνt : Tendsto ν l atTop) {r : ℝ} (hr : r∈Ioo (-1) 1) {c : ℝ} (hc : 0<c) :
    Tendsto (fun i => tEVArg (ν i) r (c^(1/ν i))) l atTop := by
  have hs : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  have hpow : Tendsto (fun i => c^(1/ν i)) l (𝓝 1) := by
    have h0 : Tendsto (fun i => 1/ν i) l (𝓝 0) := by
      simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hνt
    have := ((Real.continuousAt_const_rpow hc.ne').tendsto).comp h0
    simpa [Real.rpow_zero,Function.comp_def] using this
  have hsq : Tendsto (fun i => Real.sqrt ((1+ν i)/(1-r^2))) l atTop := by
    apply Real.tendsto_sqrt_atTop.comp
    apply Tendsto.atTop_div_const hs
    exact tendsto_atTop_add_const_left _ 1 hνt
  unfold tEVArg
  apply hsq.atTop_mul_pos (show (0:ℝ)<1-r by linarith [hr.2])
  exact hpow.sub_const r

/-- Table 4 audit: for fixed `ρ∈(-1,1)`, the t-EV copula tends to independence as `ν → ∞`
(pointwise on the closed square). -/
theorem tEV_tendsto_independence {ι : Type*} {l : Filter ι} (ν : ι → ℝ) (hν : ∀ i, 0<ν i)
    (hνt : Tendsto ν l atTop) {r : ℝ} (hr : r∈Ioo (-1) 1) (u v : I) :
    Tendsto (fun i => (tEV (ν i) r (hν i) ⟨hr.1.le,hr.2.le⟩).cdf ![u,v]) l
      (𝓝 ((independence 2).cdf ![u,v])) := by
  rw [cdf_independence,Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  -- boundary cases
  by_cases hu0 : u=0
  · subst hu0
    simp only [Set.Icc.coe_zero,zero_mul]
    exact tendsto_const_nhds.congr fun i => ((tEV (ν i) r (hν i) _).cdf_eq_zero_of_coord_eq_zero _ 0 rfl).symm
  by_cases hv0 : v=0
  · subst hv0
    simp only [Set.Icc.coe_zero,mul_zero]
    exact tendsto_const_nhds.congr fun i => ((tEV (ν i) r (hν i) _).cdf_eq_zero_of_coord_eq_zero _ 1 rfl).symm
  by_cases hu1 : u=1
  · subst hu1
    simp only [Set.Icc.coe_one,one_mul,cdf_two_one_left]
    exact tendsto_const_nhds
  by_cases hv1 : v=1
  · subst hv1
    simp only [Set.Icc.coe_one,mul_one,cdf_two_one_right]
    exact tendsto_const_nhds
  have hu : (u:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨lt_of_le_of_ne u.property.1 (fun e => hu0 (Subtype.ext e.symm)),
      lt_of_le_of_ne u.property.2 (fun e => hu1 (Subtype.ext e))⟩
  have hv : (v:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨lt_of_le_of_ne v.property.1 (fun e => hv0 (Subtype.ext e.symm)),
      lt_of_le_of_ne v.property.2 (fun e => hv1 (Subtype.ext e))⟩
  set x := -Real.log (u:ℝ)
  set y := -Real.log (v:ℝ)
  have hx : 0<x := neg_pos.mpr (Real.log_neg hu.1 hu.2)
  have hy : 0<y := neg_pos.mpr (Real.log_neg hv.1 hv.2)
  simp_rw [tEV_cdf_interior _ r _ hr u v hu hv]
  have hk : Tendsto (fun i => ν i+1) l atTop := tendsto_atTop_add_const_right _ 1 hνt
  have h1 := studentTCDF_tendsto_one (fun i => ν i+1) _ (fun i => by linarith [hν i]) hk
    (tEVArg_tendsto_atTop ν hν hνt hr (div_pos hx hy))
  have h2 := studentTCDF_tendsto_one (fun i => ν i+1) _ (fun i => by linarith [hν i]) hk
    (tEVArg_tendsto_atTop ν hν hνt hr (div_pos hy hx))
  have hlim := Real.continuous_exp.continuousAt.tendsto.comp
    (((h1.const_mul x).add (h2.const_mul y)).neg)
  have he : Real.exp (-(x*1+y*1))=(u:ℝ)*v := by
    rw [mul_one,mul_one,neg_add,Real.exp_add]
    simp only [x,y,neg_neg,Real.exp_log hu.1,Real.exp_log hv.1]
  rw [he] at hlim
  exact hlim

end Verification
