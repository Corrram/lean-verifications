import Verification.ClaytonTau
import Verification.PositivePartPower
import Copula.Families.Clayton.Negative

open ProbabilityTheory MeasureTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def claytonNegativePartial (θ u v : ℝ) : ℝ :=
  u^(-θ-1)*(max 0 (u^(-θ)+v^(-θ)-1))^(-1/θ-1)

theorem claytonNegative_cdf_pos {θ : ℝ} (hmin : -1≤θ) (hmax : θ<0)
    (u v : I) (hu : 0<(u:ℝ)) (hv : 0<(v:ℝ)) :
    (claytonNegative θ hmin hmax).cdf ![u,v]=
      (max 0 ((u:ℝ)^(-θ)+(v:ℝ)^(-θ)-1))^(-1/θ) := by
  rw [cdf_claytonNegative]
  · simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    congr 1
    field_simp
  · intro i
    fin_cases i
    · exact fun h => hu.ne' (congrArg Subtype.val h)
    · exact fun h => hv.ne' (congrArg Subtype.val h)

theorem claytonNegative_cdfSection_deriv {θ : ℝ} (hmin : -1<θ) (hmax : θ<0)
    (v : I) (hv : 0<(v:ℝ)) (u : ℝ) (hu : u∈Ioo 0 1) :
    HasDerivAt (cdfSection (claytonNegative θ hmin.le hmax) v)
      (claytonNegativePartial θ u v) u := by
  have hp : 1< -1/θ := by apply (lt_div_iff_of_neg hmax).mpr; linarith
  have hb := ((Real.hasDerivAt_rpow_const (p:=-θ) (Or.inl hu.1.ne')).add_const
    ((v:ℝ)^(-θ))).sub_const 1
  have hh := (hasDerivAt_positivePart_rpow hp (u^(-θ)+(v:ℝ)^(-θ)-1)).comp u hb
  have hd : HasDerivAt (fun x : ℝ => (max 0 (x^(-θ)+(v:ℝ)^(-θ)-1))^(-1/θ))
      (claytonNegativePartial θ u v) u := by
    convert hh using 1
    · funext x; rfl
    · unfold claytonNegativePartial
      field_simp [hmax.ne]
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
  have he := claytonNegative_cdf_pos hmin.le hmax (⟨x,hx.1.le,hx.2.le⟩:I) v hx.1 hv
  simpa only [cdfSection,projIcc_of_mem zero_le_one ⟨hx.1.le,hx.2.le⟩] using he

theorem claytonNegative_conditionalCDF {θ : ℝ} (hmin : -1<θ) (hmax : θ<0)
    (v : I) (hv : 0<(v:ℝ)) :
    (fun u => (claytonNegative θ hmin.le hmax).conditionalCDF u v) =ᵐ[volume]
      fun u => claytonNegativePartial θ u v := by
  filter_upwards [(claytonNegative θ hmin.le hmax).conditionalCDF_eq_deriv v,
    Measure.ae_ne volume (0:I),Measure.ae_ne volume (1:I)] with u hu hu0 hu1
  rw [hu]
  have h0 : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu0 (Subtype.ext h)))
  have h1 : (u:ℝ)<1 := lt_of_le_of_ne u.property.2 (fun h => hu1 (Subtype.ext h))
  exact (claytonNegative_cdfSection_deriv hmin hmax v hv u ⟨h0,h1⟩).deriv

theorem claytonNegative_product_primitive {θ : ℝ} (hmin : -1<θ) (hmax : θ<0)
    (v : I) (hv : 0<(v:ℝ)) (u : ℝ) (hu : u∈Ioo 0 1) :
    HasDerivAt (fun x : ℝ => (v:ℝ)^(-θ-1)/(θ+2)*
      (cdfSection (claytonNegative θ hmin.le hmax) v x)^(θ+2))
      (claytonNegativePartial θ u v*claytonNegativePartial θ v u) u := by
  let A := max 0 (u^(-θ)+(v:ℝ)^(-θ)-1)
  have hA : 0≤A := le_max_left _ _
  have he : cdfSection (claytonNegative θ hmin.le hmax) v u=A^(-1/θ) := by
    have hh := claytonNegative_cdf_pos hmin.le hmax (⟨u,hu.1.le,hu.2.le⟩:I) v hu.1 hv
    simpa only [cdfSection,projIcc_of_mem zero_le_one ⟨hu.1.le,hu.2.le⟩] using hh
  have hh := ((claytonNegative_cdfSection_deriv hmin hmax v hv u hu).rpow_const
    (Or.inr (by linarith : 1≤θ+2)) (p:=θ+2)).const_mul ((v:ℝ)^(-θ-1)/(θ+2))
  convert hh using 1
  rw [he,← Real.rpow_mul hA]
  have ha : max 0 ((v:ℝ)^(-θ)+u^(-θ)-1)=A := by dsimp [A]; congr 1; ring
  unfold claytonNegativePartial
  rw [ha]
  change u^(-θ-1)*A^(-1/θ-1)*((v:ℝ)^(-θ-1)*A^(-1/θ-1))=
    (v:ℝ)^(-θ-1)/(θ+2)*(u^(-θ-1)*A^(-1/θ-1)*(θ+2)*A^((-1/θ)*(θ+2-1)))
  have hp : (-1/θ)*(θ+2-1)= -1/θ-1 := by field_simp [hmax.ne]; ring
  rw [hp]
  have h2 : θ+2≠0 := by linarith
  field_simp [h2]

theorem integral_claytonNegativePartial_product {θ : ℝ} (hmin : -1<θ) (hmax : θ<0)
    (v : I) (hv : 0<(v:ℝ)) :
    (∫ u : I, claytonNegativePartial θ u v*claytonNegativePartial θ v u)=(v:ℝ)/(θ+2) := by
  let C := claytonNegative θ hmin.le hmax
  let F : ℝ → ℝ := fun x => (v:ℝ)^(-θ-1)/(θ+2)*(cdfSection C v x)^(θ+2)
  let f : ℝ → ℝ := fun x => claytonNegativePartial θ x v*claytonNegativePartial θ v x
  have hc : Continuous (cdfSection C v) := by
    unfold cdfSection
    exact C.continuous_cdf.comp (by fun_prop)
  have hFcont : Continuous F := continuous_const.mul (hc.rpow_const (fun _ => Or.inr (by linarith)))
  have hF (u : ℝ) (hu : u∈Ioo 0 1) : HasDerivAt F (f u) u :=
    claytonNegative_product_primitive hmin hmax v hv u hu
  have hf0 (u : ℝ) (hu : u∈Ioo 0 1) : 0≤f u := by
    dsimp [f,claytonNegativePartial]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg (le_max_left _ _) _))
      (mul_nonneg (Real.rpow_nonneg hv.le _) (Real.rpow_nonneg (le_max_left _ _) _))
  have hi : IntervalIntegrable f volume 0 1 :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg hFcont.continuousOn
      (fun u hu => hF u (by simpa using hu)) (fun u hu => hf0 u (by simpa using hu))
  change (∫ u : I, f (u:ℝ))=_
  rw [Copula.integral_unitInterval f,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hFcont.continuousOn hF hi]
  have hzero : cdfSection C v 0=0 := by
    simp only [cdfSection,projIcc_of_mem zero_le_one (show (0:ℝ)∈Icc 0 1 by norm_num)]
    exact C.cdf_eq_zero_of_coord_eq_zero _ 0 rfl
  have hone : cdfSection C v 1=(v:ℝ) := by simp [cdfSection]
  dsimp only [F]
  rw [hzero,hone,Real.zero_rpow (by linarith : θ+2≠0),mul_zero,sub_zero]
  rw [div_mul_eq_mul_div,← Real.rpow_add hv]
  norm_num [show -θ-1+(θ+2)=(1:ℝ) by ring]

theorem claytonNegative_kendallTau {θ : ℝ} (hmin : -1<θ) (hmax : θ<0) :
    (claytonNegative θ hmin.le hmax).kendallTau=θ/(θ+2) := by
  let C := claytonNegative θ hmin.le hmax
  have hs (u v : I) : C.cdf ![u,v]=C.cdf ![v,u] := by
    by_cases hu : u=0
    · subst u
      rw [C.cdf_eq_zero_of_coord_eq_zero _ 0 rfl,C.cdf_eq_zero_of_coord_eq_zero _ 1 rfl]
    by_cases hv : v=0
    · subst v
      rw [C.cdf_eq_zero_of_coord_eq_zero _ 1 rfl,C.cdf_eq_zero_of_coord_eq_zero _ 0 rfl]
    have hup : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))
    have hvp : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
    rw [claytonNegative_cdf_pos hmin.le hmax u v hup hvp,claytonNegative_cdf_pos hmin.le hmax v u hvp hup]
    congr 2
    ring
  have hCt : C.transpose=C := by
    apply Copula.ext_cdf
    intro z
    have hz : z=![z 0,z 1] := by funext i; fin_cases i <;> rfl
    rw [hz,Copula.cdf_transpose,hs]
  have ha : ∀ᵐ v : I, ∀ᵐ u : I, C.conditionalCDF u v=claytonNegativePartial θ u v := by
    filter_upwards [Measure.ae_ne (volume : Measure I) 0] with v hv
    have hvp : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
    exact claytonNegative_conditionalCDF hmin hmax v hvp
  have hb : ∀ᵐ v : I, ∀ᵐ u : I, C.conditionalCDF v u=claytonNegativePartial θ v u := by
    apply (Measure.ae_ae_comm (μ := (volume : Measure I)) (ν := (volume : Measure I))
      (p := fun u v => C.conditionalCDF v u=claytonNegativePartial θ v u)
      (measurableSet_eq_fun C.measurable_conditionalCDF (by unfold claytonNegativePartial; fun_prop))).mp
    exact ha
  change C.kendallTau=_
  rw [kendallTau_conditional_product,hCt]
  have he : (∫ v : I, ∫ u : I, C.conditionalCDF v u*C.conditionalCDF u v)=
      ∫ v : I, (v:ℝ)/(θ+2) := by
    apply integral_congr_ae
    filter_upwards [ha,hb,Measure.ae_ne (volume : Measure I) 0] with v hv hv' hv0
    have hvp : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv0 (Subtype.ext h)))
    have he' : (fun u : I => C.conditionalCDF v u*C.conditionalCDF u v) =ᵐ[volume]
        fun u => claytonNegativePartial θ u v*claytonNegativePartial θ v u := by
      filter_upwards [hv,hv'] with u hu hu'
      rw [hu,hu',mul_comm]
    rw [integral_congr_ae he',integral_claytonNegativePartial_product hmin hmax v hvp]
  rw [he,integral_div,Copula.integral_unit_id]
  have h2 : θ+2≠0 := by linarith
  field_simp [h2]
  ring

end Verification
