import Verification.Raftery
import Verification.CuadrasAugeRho

open MeasureTheory ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

theorem rafteryKernel_joint_measurable (a : ℝ) :
    Measurable (fun p : I × I => rafteryKernel a p.1 p.2) := by
  unfold rafteryKernel
  exact Measurable.ite (measurableSet_le measurable_snd measurable_fst) measurable_const (by fun_prop)

theorem rafteryKernel_coordinate_integrable {a : ℝ} (ha : 0≤a) (t : I) :
    Integrable (fun u : I => rafteryKernel a u t) := by
  refine (integrable_const (1:ℝ)).mono'
    ((rafteryKernel_joint_measurable a).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs,abs_of_nonneg (rafteryKernel_nonneg a u t)]
    exact rafteryKernel_le_one ha u t

theorem integral_rafteryKernel_coordinate {a : ℝ} (ha : 0≤a) (t : I) :
    (∫ u : I, rafteryKernel a u t) = 1-a*(t:ℝ)/(a+1) := by
  by_cases ht : (t:ℝ)=0
  · have ht' : t=0 := Subtype.ext ht
    subst t
    have he (u : I) : rafteryKernel a u 0=1 := by simp [rafteryKernel]
    simp only [he]
    simp
  have htp : 0<(t:ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
  have hl : (∫ u in Iic t, rafteryKernel a u t) = (t:ℝ)/(a+1) := by
    have he (u : I) (hu : u∈Iic t) : rafteryKernel a u t = (u:ℝ)^a/(t:ℝ)^a := by
      by_cases htu : t≤u
      · have heq : u=t := le_antisymm hu htu
        subst u
        simp [rafteryKernel,div_self (Real.rpow_pos_of_pos htp a).ne']
      · simp only [rafteryKernel,htu,ite_false]
        exact Real.div_rpow u.property.1 t.property.1 a
    rw [setIntegral_congr_fun measurableSet_Iic he,integral_div,
      integral_unit_Iic_rpow_nonneg a ha t,Real.rpow_add htp,Real.rpow_one]
    field_simp
  have hr : (∫ u in Ioi t, rafteryKernel a u t) = 1-(t:ℝ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu =>
      show rafteryKernel a u t=1 by simp [rafteryKernel,show t≤u from le_of_lt (show t<u from hu)])]
    have hs := integral_add_compl (s:=Iic t) measurableSet_Iic (integrable_const (1:ℝ) : Integrable (fun _ : I => (1:ℝ)))
    rw [compl_Iic,Copula.integral_unit_Iic (fun _ => (1:ℝ))] at hs
    simp at hs ⊢
    linarith
  have hs := integral_add_compl (s:=Iic t) measurableSet_Iic (rafteryKernel_coordinate_integrable ha t)
  rw [compl_Iic,hl,hr] at hs
  rw [← hs]
  field_simp
  ring

private theorem integral_cube_product (f g : I → ℝ)
    (hi : Integrable (fun x : Fin 2 → I => f (x 0)*g (x 1))) :
    (∫ x : Fin 2 → I, f (x 0)*g (x 1)) = (∫ u : I, f u)*(∫ v : I, g v) := by
  have he := integral_cube_Iic_iterated hi 1 1
  have htop : Iic (![(1:I),1]) = Set.univ := by
    ext x
    simp only [mem_Iic,mem_univ,iff_true,Pi.le_def,Fin.forall_fin_two,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    exact ⟨(x 0).property.2,(x 1).property.2⟩
  simp only [htop,Measure.restrict_univ,show Iic (1:I)=Set.univ from Set.Iic_top,
    Matrix.cons_val_zero,Matrix.cons_val_one] at he
  rw [he]
  simp only [integral_const_mul,integral_mul_const]

private theorem bounded_cube_product_integrable (f g : I → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀u, f u∈Icc (0:ℝ) 1) (hgb : ∀u, g u∈Icc (0:ℝ) 1) :
    Integrable (fun x : Fin 2 → I => f (x 0)*g (x 1)) := by
  refine (integrable_const (1:ℝ)).mono'
    ((hf.comp (measurable_pi_apply 0)).mul (hg.comp (measurable_pi_apply 1))).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hfb _).1 (hgb _).1)]
    calc
      _ ≤ 1*g (x 1) := mul_le_mul_of_nonneg_right (hfb _).2 (hgb _).1
      _ ≤ 1 := by simpa only [one_mul] using (hgb (x 1)).2

private theorem raftery_joint_integrable {a : ℝ} (ha : 0≤a) :
    Integrable (fun p : (Fin 2 → I) × I =>
      rafteryKernel a (p.1 0) p.2*rafteryKernel a (p.1 1) p.2) (volume.prod volume) := by
  have hm (i : Fin 2) : Measurable (fun p : (Fin 2 → I) × I => rafteryKernel a (p.1 i) p.2) := by
    have hi : Measurable (fun p : (Fin 2 → I) × I => p.1 i) :=
      (measurable_pi_apply i).comp measurable_fst
    exact (rafteryKernel_joint_measurable a).comp (hi.prodMk measurable_snd)
  refine (integrable_const (1:ℝ)).mono' ((hm 0).mul (hm 1)).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (rafteryKernel_nonneg a _ _) (rafteryKernel_nonneg a _ _))]
    calc
      _ ≤ 1*rafteryKernel a (p.1 1) p.2 := mul_le_mul_of_nonneg_right
        (rafteryKernel_le_one ha _ _) (rafteryKernel_nonneg a _ _)
      _ ≤ 1 := by simpa only [one_mul] using rafteryKernel_le_one ha (p.1 1) p.2

theorem integral_rafteryPower_cdf {a : ℝ} (ha : 1<a) :
    (∫ x : Fin 2 → I, (rafteryPower a ha).cdf x) = a*(a+2)/(3*(a+1)^2) := by
  have ha0 : 0≤a := by linarith
  have hpow : Integrable (fun x : Fin 2 → I => (x 0:ℝ)^a*(x 1:ℝ)^a) :=
    bounded_cube_product_integrable _ _ (by fun_prop) (by fun_prop)
      (fun u => ⟨Real.rpow_nonneg u.property.1 _,Real.rpow_le_one u.property.1 u.property.2 ha0⟩)
      (fun u => ⟨Real.rpow_nonneg u.property.1 _,Real.rpow_le_one u.property.1 u.property.2 ha0⟩)
  have hkernel (t : I) : Integrable (fun x : Fin 2 → I => rafteryKernel a (x 0) t*rafteryKernel a (x 1) t) :=
    bounded_cube_product_integrable _ _
      ((rafteryKernel_joint_measurable a).comp (measurable_id.prodMk measurable_const))
      ((rafteryKernel_joint_measurable a).comp (measurable_id.prodMk measurable_const))
      (fun u => ⟨rafteryKernel_nonneg a u t,rafteryKernel_le_one ha0 u t⟩)
      (fun u => ⟨rafteryKernel_nonneg a u t,rafteryKernel_le_one ha0 u t⟩)
  have hc (x : Fin 2 → I) : (rafteryPower a ha).cdf x =
      (x 0:ℝ)^a*(x 1:ℝ)^a/a+(a-1)/a*∫ t : I, rafteryKernel a (x 0) t*rafteryKernel a (x 1) t := by
    have hx : x=![x 0,x 1] := by ext i; fin_cases i <;> rfl
    conv_lhs => rw [hx,rafteryPower_cdf]
    rfl
  simp_rw [hc]
  rw [integral_add (hpow.div_const _) ((raftery_joint_integrable ha0).integral_prod_left.const_mul _),
    integral_div,integral_const_mul,integral_integral_swap (raftery_joint_integrable ha0),
    integral_cube_product (fun u : I => (u:ℝ)^a) (fun u : I => (u:ℝ)^a) hpow,
    integral_unit_rpow_nonneg a ha0]
  have hk (t : I) : (∫ x : Fin 2 → I, rafteryKernel a (x 0) t*rafteryKernel a (x 1) t) =
      (1-a*(t:ℝ)/(a+1))^2 := by
    rw [integral_cube_product (fun u => rafteryKernel a u t) (fun u => rafteryKernel a u t) (hkernel t),
      integral_rafteryKernel_coordinate ha0]
    ring
  simp_rw [hk]
  have hi1 : Integrable (fun t : I => (t:ℝ)) := Copula.integrable_continuous_unit volume continuous_subtype_val
  have hi2 : Integrable (fun t : I => (t:ℝ)^2) := Copula.integrable_continuous_unit volume (continuous_subtype_val.pow 2)
  have he (t : I) : (1-a*(t:ℝ)/(a+1))^2 = 1-(2*a/(a+1))*(t:ℝ)+(a/(a+1))^2*(t:ℝ)^2 := by ring
  simp_rw [he]
  have hiA : Integrable (fun t : I => 1-(2*a/(a+1))*(t:ℝ)) :=
    (integrable_const (1:ℝ)).sub (hi1.const_mul _)
  rw [integral_add hiA (hi2.const_mul _),
    integral_sub (integrable_const (1:ℝ)) (hi1.const_mul _),integral_const_mul,integral_const_mul,
    Copula.integral_unit_id,Copula.integral_unit_pow]
  simp only [integral_const,Measure.real_def,measure_univ,ENNReal.toReal_one,one_smul]
  field_simp [show a≠0 by linarith,show a+1≠0 by linarith]
  ring

theorem rafteryPower_spearmanRho {a : ℝ} (ha : 1<a) :
    (rafteryPower a ha).spearmanRho = (a-1)*(a+3)/(a+1)^2 := by
  rw [Copula.spearmanRho_eq_integral_cdf,Copula.toMeasure_independence]
  change 12*(∫ x : Fin 2 → I, (rafteryPower a ha).cdf x)-3 = _
  rw [integral_rafteryPower_cdf ha]
  field_simp [show a+1≠0 by linarith]
  ring

theorem raftery_spearmanRho (δ : I) :
    (raftery δ).spearmanRho = (δ:ℝ)*(4-3*(δ:ℝ))/(2-(δ:ℝ))^2 := by
  by_cases h0 : δ=0
  · subst δ; rw [raftery_zero]; norm_num
  by_cases h1 : δ=1
  · subst δ; rw [raftery_one]; norm_num
  simp only [raftery,h0,h1,dite_false]
  rw [rafteryPower_spearmanRho]
  have hd : 1-(δ:ℝ)≠0 := sub_ne_zero.mpr (fun h => h1 (Subtype.ext h.symm))
  have hp : 2-(δ:ℝ)≠0 := by linarith [δ.property.2]
  have he : 1/(1-(δ:ℝ))+1 = (2-(δ:ℝ))/(1-(δ:ℝ)) := by field_simp; ring
  rw [he]
  field_simp [hd,hp]
  ring

end Verification
