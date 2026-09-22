import Verification.DiagonalHole
import Verification.ExclusionBandDensity
import Copula.Dependence.Density

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval ENNReal

namespace Verification

private noncomputable def halfUnit : I := ⟨1/2,by norm_num,by norm_num⟩

noncomputable def medianLow (u : I) : ℝ := if (u : ℝ) ≤ 1/2 then 1 else 0
noncomputable def medianHigh (u : I) : ℝ := 1-medianLow u

theorem medianLow_measurable : Measurable medianLow :=
  Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_const measurable_const

theorem medianHigh_measurable : Measurable medianHigh := measurable_const.sub medianLow_measurable

theorem medianLow_mem (u : I) : medianLow u ∈ Icc 0 1 := by unfold medianLow; split_ifs <;> norm_num

theorem medianHigh_mem (u : I) : medianHigh u ∈ Icc 0 1 := by
  have h := medianLow_mem u
  unfold medianHigh
  constructor <;> linarith [h.1,h.2]

theorem medianLow_integrable : Integrable medianLow :=
  (integrable_const (1 : ℝ)).mono' medianLow_measurable.aestronglyMeasurable
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs,abs_of_nonneg (medianLow_mem u).1]; exact (medianLow_mem u).2)

theorem medianHigh_integrable : Integrable medianHigh := (integrable_const (1 : ℝ)).sub medianLow_integrable

theorem medianLow_prefix (t : I) : (∫ u in Iic t, medianLow u)=min (t : ℝ) (1/2) := by
  have he : medianLow=(Iic (halfUnit : I)).indicator (fun _ => (1 : ℝ)) := by
    funext u
    rfl
  rw [he,integral_indicator measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic,
    Iic_inter_Iic,setIntegral_one_eq_measureReal,Measure.real,unitInterval.volume_Iic,
    ENNReal.toReal_ofReal (unitInterval.nonneg _)]
  change min (1/2 : ℝ) (t : ℝ)=min (t : ℝ) (1/2)
  exact min_comm _ _

theorem medianHigh_prefix (t : I) : (∫ u in Iic t, medianHigh u)=max 0 ((t : ℝ)-1/2) := by
  unfold medianHigh
  rw [integral_sub (integrable_const _) medianLow_integrable.integrableOn,medianLow_prefix]
  simp only [integral_const,smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply_univ,
    unitInterval.volume_Iic,ENNReal.toReal_ofReal t.property.1]
  rw [min_def,max_def]
  split_ifs <;> linarith

theorem medianLow_integral : (∫ u : I, medianLow u)=1/2 := by
  have h := medianLow_prefix 1
  have he : Iic (1 : I)=univ := by ext u; exact iff_true_intro u.property.2
  rw [he,Measure.restrict_univ] at h
  norm_num at h
  exact h

theorem medianHigh_integral : (∫ u : I, medianHigh u)=1/2 := by
  unfold medianHigh
  rw [integral_sub (integrable_const _) medianLow_integrable,medianLow_integral]
  norm_num

noncomputable def medianOffDensity (p : I × I) : ℝ :=
  2*(medianLow p.1*medianHigh p.2+medianHigh p.1*medianLow p.2)

theorem medianOffDensity_measurable : Measurable medianOffDensity := by
  unfold medianOffDensity
  exact measurable_const.mul (((medianLow_measurable.comp measurable_fst).mul
    (medianHigh_measurable.comp measurable_snd)).add
      ((medianHigh_measurable.comp measurable_fst).mul (medianLow_measurable.comp measurable_snd)))

theorem medianOffDensity_nonneg (p : I × I) : 0 ≤ medianOffDensity p :=
  mul_nonneg (by norm_num) (add_nonneg
    (mul_nonneg (medianLow_mem _).1 (medianHigh_mem _).1)
    (mul_nonneg (medianHigh_mem _).1 (medianLow_mem _).1))

theorem medianOffDensity_integral (t : I) : (∫ u : I, medianOffDensity (u,t))=1 := by
  unfold medianOffDensity
  dsimp only
  rw [integral_const_mul,integral_add (medianLow_integrable.mul_const _) (medianHigh_integrable.mul_const _),
    integral_mul_const,integral_mul_const,medianLow_integral,medianHigh_integral]
  unfold medianHigh
  ring

noncomputable def diagonalHoleCorner : ExclusionBand := diagonalHoleBand (1/2) (1/2) (by norm_num) (by norm_num)

theorem diagonalHoleCorner_density (u v : I) (hv : (v : ℝ) ≠ 1/2) :
    diagonalHoleCorner.density (u,v)=medianOffDensity (u,v) := by
  have he : diagonalHoleCorner.lower u=(if (u : ℝ) ≤ 1/2 then 0 else 1/2) := by
    change diagonalHoleLower (1/2) (1/2) u=_
    unfold diagonalHoleLower
    by_cases hu : (u : ℝ) ≤ 1/2
    · rw [ite_eq_left hu,ite_eq_left hu]
    · rw [ite_eq_right hu,ite_eq_right hu,ite_eq_left (by linarith)]
      norm_num
  change (if diagonalHoleCorner.lower u ≤ (v : ℝ) ∧ (v : ℝ) ≤ diagonalHoleCorner.lower u+1/2
    then 0 else 1/(1-(1/2 : ℝ)))=_
  rw [he]
  rcases lt_or_gt_of_ne hv with hv | hv
  · have hvl : (v : ℝ) ≤ 1/2 := hv.le
    have hvn : ¬(1/2 : ℝ) ≤ v := not_le.mpr hv
    by_cases hu : (u : ℝ) ≤ 1/2 <;>
      norm_num [medianOffDensity,medianHigh,medianLow,hu,hvl,hvn,v.property.1,v.property.2]
  · have hvl : (1/2 : ℝ) ≤ v := hv.le
    have hvn : ¬(v : ℝ) ≤ 1/2 := not_le.mpr hv
    by_cases hu : (u : ℝ) ≤ 1/2 <;>
      norm_num [medianOffDensity,medianHigh,medianLow,hu,hvl,hvn,v.property.1,v.property.2]

theorem diagonalHoleCorner_columnDensity : diagonalHoleCorner.columnDensity=ᵐ[volume] (fun _ => 1) := by
  filter_upwards [volume.ae_ne (halfUnit : I)] with v hv
  have hv' : (v : ℝ) ≠ 1/2 := fun h => hv (Subtype.ext h)
  unfold ExclusionBand.columnDensity
  simp_rw [diagonalHoleCorner_density _ _ hv']
  exact medianOffDensity_integral v

theorem diagonalHoleCorner_marginal : diagonalHoleCorner.marginal=volume := by
  rw [ExclusionBand.marginal,ExclusionBand.map_snd]
  have he : (fun v => ENNReal.ofReal (diagonalHoleCorner.columnDensity v))=ᵐ[volume] (fun _ => (1 : ℝ≥0∞)) := by
    filter_upwards [diagonalHoleCorner_columnDensity] with v hv
    rw [hv]; norm_num
  rw [withDensity_congr_ae he]
  exact withDensity_one

theorem diagonalHoleCorner_copula_density : diagonalHoleCorner.copula.toMeasure=
    (volume : Measure (Fin 2 → I)).withDensity (fun x => ENNReal.ofReal (medianOffDensity (x 0,x 1))) := by
  rw [ExclusionBand.copula_raw_density _ diagonalHoleCorner_marginal]
  apply withDensity_congr_ae
  have he : ∀ᵐ x : Fin 2 → I, x 1 ≠ halfUnit := Measure.ae_eval_ne _ _ _
  filter_upwards [he] with x hx
  rw [diagonalHoleCorner_density _ _ (fun h => hx (Subtype.ext h))]

theorem medianOffDensity_cube_integrable : Integrable (fun x : Fin 2 → I => medianOffDensity (x 0,x 1)) := by
  refine (integrable_const (4 : ℝ)).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (medianOffDensity_measurable.comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))).aestronglyMeasurable
  · rw [Real.norm_eq_abs,abs_of_nonneg (medianOffDensity_nonneg _)]
    unfold medianOffDensity medianHigh medianLow
    split_ifs <;> norm_num

theorem medianOffDensity_cube_prefix (u v : I) :
    (∫ x in Iic ![u,v], medianOffDensity (x 0,x 1))=
      2*(min (u : ℝ) (1/2)*max 0 ((v : ℝ)-1/2)+max 0 ((u : ℝ)-1/2)*min (v : ℝ) (1/2)) := by
  have hi (f g : I → ℝ) (hf : Measurable f) (hg : Measurable g)
      (hb : ∀ t, |f t| ≤ 1) (hc : ∀ t, |g t| ≤ 1) :
      Integrable (fun x : Fin 2 → I => f (x 0)*g (x 1)) :=
    (integrable_const (1 : ℝ)).mono' ((hf.comp (measurable_pi_apply 0)).mul
      (hg.comp (measurable_pi_apply 1))).aestronglyMeasurable
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_mul]; exact (mul_le_mul (hb _) (hc _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hl (t : I) : |medianLow t| ≤ 1 := by rw [abs_of_nonneg (medianLow_mem t).1]; exact (medianLow_mem t).2
  have hh (t : I) : |medianHigh t| ≤ 1 := by rw [abs_of_nonneg (medianHigh_mem t).1]; exact (medianHigh_mem t).2
  unfold medianOffDensity
  dsimp only
  rw [integral_const_mul,integral_add (hi _ _ medianLow_measurable medianHigh_measurable hl hh).integrableOn
    (hi _ _ medianHigh_measurable medianLow_measurable hh hl).integrableOn,
    Copula.integral_cube_Iic_mul,Copula.integral_cube_Iic_mul,
    medianLow_prefix,medianHigh_prefix,medianHigh_prefix,medianLow_prefix]

end Verification
