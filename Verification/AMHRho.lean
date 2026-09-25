import Verification.AMHXi
import Verification.CubeFubini
import Copula.Rank.SpearmanCDF

/-! # Spearman rho integrals for Ali–Mikhail–Haq copulas -/

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval Topology

namespace Verification

theorem amhDen_pos_of_pos_right {θ u v : ℝ} (hθ : θ≤1) (hu : u∈Icc 0 1)
    (hv : v∈Icc 0 1) (hvp : 0<v) : 0<amhDen θ u v := by
  have hp := mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hv.2)
  have hh := mul_le_mul_of_nonneg_right hθ hp
  have hk := mul_nonneg hu.1 (sub_nonneg.mpr hv.2)
  unfold amhDen
  nlinarith

private theorem amh_cdf_primitive (A B v x : ℝ) (hB : B≠0) (hd : A+B*x≠0) :
    HasDerivAt (fun u : ℝ => v*u/B-v*A/B^2*Real.log (A+B*u))
      (x*v/(A+B*x)) x := by
  have hl := (((hasDerivAt_id x).const_mul B).const_add A).log hd
  have hh := (((hasDerivAt_id x).const_mul v).div_const B).sub (hl.const_mul (v*A/B^2))
  convert hh using 1
  · funext u; rfl
  · dsimp only [Pi.mul_apply,Pi.sub_apply,id_eq]
    field_simp [hB,hd]
    have hd' : A+x*B≠0 := by simpa [mul_comm] using hd
    field_simp [hd']
    ring

theorem integral_amh_cdf_section_of_den_pos {θ : ℝ} (hmin : -1≤θ) (hmax : θ≤1) (h0 : θ≠0)
    (v : I) (hv : (v:ℝ)≠1) (hden : ∀ u : ℝ, u∈Icc 0 1 → 0<amhDen θ u v) :
    (∫ u : I, (amh θ hmin hmax).cdf ![u,v])=
      (v:ℝ)/(θ*(1-(v:ℝ)))+
        (v:ℝ)*(1-θ*(1-(v:ℝ)))/(θ*(1-(v:ℝ)))^2*Real.log (1-θ*(1-(v:ℝ))) := by
  let A := 1-θ*(1-(v:ℝ))
  let B := θ*(1-(v:ℝ))
  have hB : B≠0 := mul_ne_zero h0 (sub_ne_zero.mpr hv.symm)
  have hd (u : ℝ) (hu : u∈Icc 0 1) : 0<A+B*u := by
    have hh := hden u hu
    convert hh using 1
    dsimp [A,B,amhDen]
    ring
  let F : ℝ → ℝ := fun u => (v:ℝ)*u/B-(v:ℝ)*A/B^2*Real.log (A+B*u)
  let f : ℝ → ℝ := fun u => u*(v:ℝ)/(A+B*u)
  have hF (u : ℝ) (hu : u∈uIcc 0 1) : HasDerivAt F (f u) u :=
    amh_cdf_primitive A B v u hB (hd u (by simpa using hu)).ne'
  have hi : IntervalIntegrable f volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    exact (hd u (by simpa using hu)).ne'
  have he : (fun u : I => (amh θ hmin hmax).cdf ![u,v])=fun u : I => f (u:ℝ) := by
    funext u
    rw [cdf_amh]
    dsimp [f,A,B]
    congr 1
    ring
  rw [he,Copula.integral_unitInterval f,intervalIntegral.integral_eq_sub_of_hasDerivAt hF hi]
  have hAB : A+B=1 := by dsimp [A,B]; ring
  simp only [F,mul_one,mul_zero,zero_div,add_zero,hAB,Real.log_one,sub_zero]
  change (v:ℝ)/B-(0-(v:ℝ)*A/B^2*Real.log A)=(v:ℝ)/B+(v:ℝ)*A/B^2*Real.log A
  ring

theorem integral_amh_cdf_section {θ : ℝ} (hmin : -1≤θ) (hmax : θ<1) (h0 : θ≠0)
    (v : I) (hv : (v:ℝ)≠1) :
    (∫ u : I, (amh θ hmin hmax.le).cdf ![u,v])=
      (v:ℝ)/(θ*(1-(v:ℝ)))+
        (v:ℝ)*(1-θ*(1-(v:ℝ)))/(θ*(1-(v:ℝ)))^2*Real.log (1-θ*(1-(v:ℝ))) :=
  integral_amh_cdf_section_of_den_pos hmin hmax.le h0 v hv
    (fun _ hu => amhDen_pos_lt_one hmax hu v.property)

theorem amh_spearmanRho_integral_of_le_one {θ : ℝ} (hmin : -1≤θ) (hmax : θ≤1) (h0 : θ≠0) :
    (amh θ hmin hmax).spearmanRho=
      12*(∫ v : I, (v:ℝ)/(θ*(1-(v:ℝ)))+
        (v:ℝ)*(1-θ*(1-(v:ℝ)))/(θ*(1-(v:ℝ)))^2*Real.log (1-θ*(1-(v:ℝ))))-3 := by
  let C := amh θ hmin hmax
  have he := integral_cube_Iic_iterated (C.integrable_cdf volume) 1 1
  have htop : Iic (![(1:I),1]) = Set.univ := by
    ext x
    simp only [mem_Iic,mem_univ,iff_true,Pi.le_def,Fin.forall_fin_two,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    exact ⟨(x 0).property.2,(x 1).property.2⟩
  simp only [htop,Measure.restrict_univ,show Iic (1:I)=Set.univ from Set.Iic_top] at he
  change C.spearmanRho=_
  rw [Copula.spearmanRho_eq_integral_cdf,Copula.toMeasure_independence]
  change 12*(∫ x : Fin 2 → I, C.cdf x)-3=_
  rw [he]
  congr 2
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne (volume : Measure I) 1,Measure.ae_ne (volume : Measure I) 0] with v hv hv0
  have hv' : (v:ℝ)≠1 := fun h => hv (Subtype.ext h)
  have hs (u : I) : C.cdf ![v,u]=C.cdf ![u,v] := by
    simp only [C,cdf_amh]
    ring
  simp_rw [hs]
  have hvp : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv0 (Subtype.ext h)))
  exact integral_amh_cdf_section_of_den_pos hmin hmax h0 v hv'
    (fun _ hu => amhDen_pos_of_pos_right hmax hu v.property hvp)

theorem amh_spearmanRho_integral {θ : ℝ} (hmin : -1≤θ) (hmax : θ<1) (h0 : θ≠0) :
    (amh θ hmin hmax.le).spearmanRho=
      12*(∫ v : I, (v:ℝ)/(θ*(1-(v:ℝ)))+
        (v:ℝ)*(1-θ*(1-(v:ℝ)))/(θ*(1-(v:ℝ)))^2*Real.log (1-θ*(1-(v:ℝ))))-3 :=
  amh_spearmanRho_integral_of_le_one hmin hmax.le h0

theorem amh_spearmanRho_zero : (amh 0 (by norm_num) (by norm_num)).spearmanRho=0 := by
  rw [amh_zero,Copula.spearmanRho_independence]

end Verification
