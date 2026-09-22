import Verification.CuadrasAugeConditional

/-! # Exact Chatterjee xi of the Cuadras–Augé family -/

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval

namespace Verification

theorem integral_cuadrasConditional_sq_response (δ u : I) (hu : 0<u) :
    (∫ v : I,cuadrasConditional δ u v^2) =
      (1-(δ:ℝ))^2*(u:ℝ)^(3-2*(δ:ℝ))/3+
        (1-(u:ℝ)^(3-2*(δ:ℝ)))/(3-2*(δ:ℝ)) := by
  classical
  let p := 1-(δ:ℝ)
  have hp : 0≤p := by dsimp [p]; linarith [δ.property.2]
  have hp2 : 0≤2*p := by positivity
  have hpow : Integrable (fun v : I => (v:ℝ)^(2*p)) :=
    Copula.integrable_continuous_unit volume ((Real.continuous_rpow_const hp2).comp continuous_subtype_val)
  have he (v : I) : cuadrasConditional δ u v^2 =
      if u<v then (v:ℝ)^(2*p) else (p*(u:ℝ)^(-(δ:ℝ)))^2*(v:ℝ)^2 := by
    unfold cuadrasConditional
    split_ifs
    · rw [← Real.rpow_mul_natCast v.property.1]
      congr 1
      dsimp [p]
      ring
    · exact mul_pow _ _ 2
  have hi : Integrable (fun v : I => cuadrasConditional δ u v^2) := by
    simp_rw [he]
    have hg : Integrable (fun v : I => (p*(u:ℝ)^(-(δ:ℝ)))^2*(v:ℝ)^2) :=
      Copula.integrable_continuous_unit volume (by fun_prop)
    exact Integrable.piecewise (s := Ioi u) measurableSet_Ioi hpow.integrableOn hg.integrableOn
  have hs := integral_add_compl (s := Iic u) measurableSet_Iic hi
  rw [compl_Iic] at hs
  have hl : (∫ v in Iic u,cuadrasConditional δ u v^2)=
      (1-(δ:ℝ))^2*(u:ℝ)^(3-2*(δ:ℝ))/3 := by
    rw [setIntegral_congr_fun measurableSet_Iic (fun v hv => by rw [he,ite_eq_right (not_lt.mpr hv)]),
      integral_const_mul,Copula.integral_unit_Iic (fun v : ℝ => v^2),integral_pow]
    norm_num only [Nat.cast_ofNat,Nat.reduceAdd,zero_pow (by decide : 3≠0),sub_zero]
    have hh : ((u:ℝ)^(-(δ:ℝ)))^2*(u:ℝ)^3=(u:ℝ)^(3-2*(δ:ℝ)) := by
      rw [← Real.rpow_mul_natCast u.property.1,← Real.rpow_natCast,← Real.rpow_add (show (0:ℝ)<u from hu)]
      congr 1
      norm_num
      ring
    calc
      _ = p^2*(((u:ℝ)^(-(δ:ℝ)))^2*(u:ℝ)^3)/3 := by ring
      _ = _ := by rw [hh]
  have hr : (∫ v in Ioi u,cuadrasConditional δ u v^2)=
      (1-(u:ℝ)^(3-2*(δ:ℝ)))/(3-2*(δ:ℝ)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun v hv => by rw [he,ite_eq_left (show u<v from hv)])]
    have hh := integral_add_compl (s := Iic u) measurableSet_Iic hpow
    rw [compl_Iic,integral_unit_Iic_rpow_nonneg _ hp2,integral_unit_rpow_nonneg _ hp2] at hh
    have hd : 2*p+1=3-2*(δ:ℝ) := by dsimp [p]; ring
    rw [hd] at hh
    rw [sub_div]
    linarith only [hh]
  rw [hl,hr] at hs
  exact hs.symm

theorem cuadrasAuge_chatterjeeXi (δ : I) :
    (cuadrasAuge δ).chatterjeeXi=(δ:ℝ)^2/(2-(δ:ℝ)) := by
  have he (v : I) : (∫ u : I,(cuadrasAuge δ).conditionalCDF u v^2)=
      (∫ u : I,cuadrasConditional δ u v^2) :=
    integral_congr_ae ((conditionalCDF_cuadrasAuge δ v).fun_comp (fun z => z^2))
  unfold Copula.chatterjeeXi
  simp_rw [he]
  rw [integral_integral_swap (cuadrasConditional_sq_joint_integrable δ)]
  have he' : (∫ u : I,∫ v : I,cuadrasConditional δ u v^2)=
      ∫ u : I, (1-(δ:ℝ))^2*(u:ℝ)^(3-2*(δ:ℝ))/3+
        (1-(u:ℝ)^(3-2*(δ:ℝ)))/(3-2*(δ:ℝ)) := by
    apply integral_congr_ae
    filter_upwards [Measure.ae_ne volume (0:I)] with u hu
    exact integral_cuadrasConditional_sq_response δ u (lt_of_le_of_ne u.property.1 (Ne.symm hu))
  rw [he']
  have hp : 0≤3-2*(δ:ℝ) := by linarith [δ.property.2]
  have hpow : Integrable (fun u : I => (u:ℝ)^(3-2*(δ:ℝ))) :=
    Copula.integrable_continuous_unit volume ((Real.continuous_rpow_const hp).comp continuous_subtype_val)
  rw [integral_add (f := fun u : I => (1-(δ:ℝ))^2*(u:ℝ)^(3-2*(δ:ℝ))/3)
    (g := fun u : I => (1-(u:ℝ)^(3-2*(δ:ℝ)))/(3-2*(δ:ℝ)))
    ((hpow.const_mul _).div_const _) (((integrable_const _).sub hpow).div_const _),
    integral_div,integral_div,integral_const_mul,integral_sub (integrable_const (1:ℝ)) hpow,
    integral_unit_rpow_nonneg _ hp]
  simp only [integral_const,probReal_univ,one_smul]
  have h2 : 2-(δ:ℝ)≠0 := by linarith [δ.property.2]
  have h3 : 3-2*(δ:ℝ)≠0 := by linarith [δ.property.2]
  have h4 : 3-2*(δ:ℝ)+1≠0 := by linarith [δ.property.2]
  have h4' : 4-2*(δ:ℝ)≠0 := by linarith [δ.property.2]
  ring_nf
  field_simp
  ring

end Verification
