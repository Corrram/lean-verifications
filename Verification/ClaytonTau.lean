import Copula.Dependence.ClaytonDensityMeasure
import Copula.Rank.ConditionalDerivative
import Verification.KendallConditionalProduct

open ProbabilityTheory MeasureTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def claytonPartial (θ u v : ℝ) : ℝ :=
  u^(-θ-1)*(u^(-θ)+v^(-θ)-1)^(-1/θ-1)

theorem clayton_base_pos {θ u v : ℝ} (hθ : 0<θ) (hu : u∈Ioc 0 1) (hv : v∈Ioc 0 1) :
    0<u^(-θ)+v^(-θ)-1 := by
  have hu' := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu.1 hu.2 (by linarith : -θ≤0)
  have hv' := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv.1 hv.2 (by linarith : -θ≤0)
  linarith

theorem clayton_cdfSection_deriv {θ : ℝ} (hθ : 0<θ) (v : I) (hv : 0<(v:ℝ))
    (u : ℝ) (hu : u∈Ioo 0 1) :
    HasDerivAt (cdfSection (clayton 2 θ hθ) v) (claytonPartial θ u v) u := by
  have hd : HasDerivAt (fun x : ℝ => (x^(-θ)+(v:ℝ)^(-θ)-1)^(-1/θ))
      (claytonPartial θ u v) u :=
    Copula.clayton_cdf_formula_hasDerivAt_first θ u v hθ hu.1 hv hu.2.le v.property.2
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
  have hh := Copula.clayton_cdf_positive_eq_analytic θ hθ (⟨x,hx.1.le,hx.2.le⟩:I) v hx.1 hv
  change (clayton 2 θ hθ).cdf ![(⟨x,hx.1.le,hx.2.le⟩:I),v]=
    (x^(-θ)+(v:ℝ)^(-θ)-1)^(-1/θ) at hh
  simpa only [cdfSection,projIcc_of_mem zero_le_one ⟨hx.1.le,hx.2.le⟩] using hh

theorem clayton_conditionalCDF {θ : ℝ} (hθ : 0<θ) (v : I) (hv : 0<(v:ℝ)) :
    (fun u => (clayton 2 θ hθ).conditionalCDF u v) =ᵐ[volume]
      fun u => claytonPartial θ u v := by
  filter_upwards [(clayton 2 θ hθ).conditionalCDF_eq_deriv v,
    Measure.ae_ne volume (0:I),Measure.ae_ne volume (1:I)] with u hu hu0 hu1
  rw [hu]
  have h0 : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu0 (Subtype.ext h)))
  have h1 : (u:ℝ)<1 := lt_of_le_of_ne u.property.2 (fun h => hu1 (Subtype.ext h))
  exact (clayton_cdfSection_deriv hθ v hv u ⟨h0,h1⟩).deriv

theorem clayton_product_primitive {θ : ℝ} (hθ : 0<θ) (v : I) (hv : 0<(v:ℝ))
    (u : ℝ) (hu : u∈Ioo 0 1) :
    HasDerivAt (fun x : ℝ => (v:ℝ)^(-θ-1)/(θ+2)*(cdfSection (clayton 2 θ hθ) v x)^(θ+2))
      (claytonPartial θ u v*claytonPartial θ v u) u := by
  let A := u^(-θ)+(v:ℝ)^(-θ)-1
  have hA : 0<A := clayton_base_pos hθ ⟨hu.1,hu.2.le⟩ ⟨hv,v.property.2⟩
  have he : cdfSection (clayton 2 θ hθ) v u=A^(-1/θ) := by
    have hh := Copula.clayton_cdf_positive_eq_analytic θ hθ (⟨u,hu.1.le,hu.2.le⟩:I) v hu.1 hv
    change (clayton 2 θ hθ).cdf ![(⟨u,hu.1.le,hu.2.le⟩:I),v]=A^(-1/θ) at hh
    simpa only [cdfSection,projIcc_of_mem zero_le_one ⟨hu.1.le,hu.2.le⟩] using hh
  have hc : 0<cdfSection (clayton 2 θ hθ) v u := by rw [he]; exact Real.rpow_pos_of_pos hA _
  have hh := ((clayton_cdfSection_deriv hθ v hv u hu).rpow_const (Or.inl hc.ne')
    (p:=θ+2)).const_mul ((v:ℝ)^(-θ-1)/(θ+2))
  convert hh using 1
  rw [he,← Real.rpow_mul hA.le]
  have ha : (v:ℝ)^(-θ)+u^(-θ)-1=A := by dsimp [A]; ring
  unfold claytonPartial
  rw [ha]
  change u^(-θ-1)*A^(-1/θ-1)*((v:ℝ)^(-θ-1)*A^(-1/θ-1))=
    (v:ℝ)^(-θ-1)/(θ+2)*(u^(-θ-1)*A^(-1/θ-1)*(θ+2)*A^((-1/θ)*(θ+2-1)))
  have hp : (-1/θ)*(θ+2-1)= -1/θ-1 := by field_simp; ring
  rw [hp]
  have h2 : θ+2≠0 := by linarith
  field_simp [h2]

theorem integral_claytonPartial_product {θ : ℝ} (hθ : 0<θ) (v : I) (hv : 0<(v:ℝ)) :
    (∫ u : I, claytonPartial θ u v*claytonPartial θ v u)=(v:ℝ)/(θ+2) := by
  let C := clayton 2 θ hθ
  let F : ℝ → ℝ := fun x => (v:ℝ)^(-θ-1)/(θ+2)*(cdfSection C v x)^(θ+2)
  let f : ℝ → ℝ := fun x => claytonPartial θ x v*claytonPartial θ v x
  have hc : Continuous (cdfSection C v) := by
    unfold cdfSection
    exact C.continuous_cdf.comp (by fun_prop)
  have hFcont : Continuous F := continuous_const.mul (hc.rpow_const (fun _ => Or.inr (by linarith)))
  have hF (u : ℝ) (hu : u∈Ioo 0 1) : HasDerivAt F (f u) u := clayton_product_primitive hθ v hv u hu
  have hf0 (u : ℝ) (hu : u∈Ioo 0 1) : 0≤f u := by
    have ha := clayton_base_pos hθ ⟨hu.1,hu.2.le⟩ ⟨hv,v.property.2⟩
    have hb := clayton_base_pos hθ ⟨hv,v.property.2⟩ ⟨hu.1,hu.2.le⟩
    dsimp [f,claytonPartial]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg ha.le _))
      (mul_nonneg (Real.rpow_nonneg hv.le _) (Real.rpow_nonneg hb.le _))
  have hi : IntervalIntegrable f volume 0 1 :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg hFcont.continuousOn
      (fun u hu => hF u (by simpa using hu)) (fun u hu => hf0 u (by simpa using hu))
  change (∫ u : I, f (u:ℝ))=_
  rw [Copula.integral_unitInterval f,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hFcont.continuousOn hF hi]
  have hzero : cdfSection C v 0=0 := by
    simp only [cdfSection,projIcc_of_mem zero_le_one (show (0:ℝ)∈Icc 0 1 by norm_num)]
    exact C.cdf_eq_zero_of_coord_eq_zero _ 0 rfl
  have hone : cdfSection C v 1=(v:ℝ) := by
    simp [cdfSection]
  dsimp only [F]
  rw [hzero,hone,Real.zero_rpow (by linarith : θ+2≠0),mul_zero,sub_zero]
  rw [div_mul_eq_mul_div,← Real.rpow_add hv]
  norm_num [show -θ-1+(θ+2)=(1:ℝ) by ring]

theorem clayton_kendallTau {θ : ℝ} (hθ : 0<θ) :
    (clayton 2 θ hθ).kendallTau=θ/(θ+2) := by
  let C := clayton 2 θ hθ
  have hs (u v : I) : C.cdf ![u,v]=C.cdf ![v,u] := by
    by_cases hu : u=0
    · subst u
      rw [C.cdf_eq_zero_of_coord_eq_zero _ 0 rfl,C.cdf_eq_zero_of_coord_eq_zero _ 1 rfl]
    by_cases hv : v=0
    · subst v
      rw [C.cdf_eq_zero_of_coord_eq_zero _ 1 rfl,C.cdf_eq_zero_of_coord_eq_zero _ 0 rfl]
    have hup : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))
    have hvp : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
    rw [cdf_clayton_two_pos θ hθ u v hup hvp,cdf_clayton_two_pos θ hθ v u hvp hup]
    congr 1
    ring
  have hCt : C.transpose=C := by
    apply Copula.ext_cdf
    intro z
    have hz : z=![z 0,z 1] := by funext i; fin_cases i <;> rfl
    rw [hz,Copula.cdf_transpose,hs]
  have ha : ∀ᵐ v : I, ∀ᵐ u : I, C.conditionalCDF u v=claytonPartial θ u v := by
    filter_upwards [Measure.ae_ne (volume : Measure I) 0] with v hv
    have hvp : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
    exact clayton_conditionalCDF hθ v hvp
  have hb : ∀ᵐ v : I, ∀ᵐ u : I, C.conditionalCDF v u=claytonPartial θ v u := by
    apply (Measure.ae_ae_comm (μ := (volume : Measure I)) (ν := (volume : Measure I))
      (p := fun u v => C.conditionalCDF v u=claytonPartial θ v u)
      (measurableSet_eq_fun C.measurable_conditionalCDF (by unfold claytonPartial; fun_prop))).mp
    exact ha
  change C.kendallTau=_
  rw [kendallTau_conditional_product,hCt]
  have he : (∫ v : I, ∫ u : I, C.conditionalCDF v u*C.conditionalCDF u v)=
      ∫ v : I, (v:ℝ)/(θ+2) := by
    apply integral_congr_ae
    filter_upwards [ha,hb,Measure.ae_ne (volume : Measure I) 0] with v hv hv' hv0
    have hvp : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv0 (Subtype.ext h)))
    have he' : (fun u : I => C.conditionalCDF v u*C.conditionalCDF u v) =ᵐ[volume]
        fun u => claytonPartial θ u v*claytonPartial θ v u := by
      filter_upwards [hv,hv'] with u hu hu'
      rw [hu,hu',mul_comm]
    rw [integral_congr_ae he',integral_claytonPartial_product hθ v hvp]
  rw [he,integral_div,Copula.integral_unit_id]
  have h2 : θ+2≠0 := by linarith
  field_simp [h2]
  ring

end Verification
