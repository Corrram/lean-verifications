import Papers.Rockel2026XiFootrule.SIEquality
import Copula.Classical.Bivariate

/-! # Remark 2.3: an asymmetric SI equality copula

This constructs the source's example with A(v)=v/2, B(v)=(v+1)/2,
and middle level v. Closed cut conventions give a monotone kernel version;
the source's open intervals agree almost everywhere.
-/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule

noncomputable def asymmetricLowerCut (v : I) : I :=
  ⟨(v : ℝ) / 2, by constructor <;> linarith [v.property.1, v.property.2]⟩

noncomputable def asymmetricUpperCut (v : I) : I :=
  ⟨((v : ℝ) + 1) / 2, by constructor <;> linarith [v.property.1, v.property.2]⟩

noncomputable def asymmetricKernel (v u : I) : ℝ :=
  threeLevel (asymmetricLowerCut v) (asymmetricUpperCut v) v u

private theorem asymmetricKernel_formula (v u : I) :
    asymmetricKernel v u = if (u : ℝ) ≤ (v : ℝ) / 2 then 1
      else if (u : ℝ) ≤ ((v : ℝ) + 1) / 2 then (v : ℝ) else 0 := by
  unfold asymmetricKernel threeLevel lowerStep
  change (1 - (v : ℝ)) * (if (u : ℝ) ≤ v / 2 then 1 else 0) +
    (v : ℝ) * (if (u : ℝ) ≤ (v + 1) / 2 then 1 else 0) = _
  split_ifs <;> simp_all
  linarith

private theorem asymmetricKernel_integrable (v : I) : Integrable (asymmetricKernel v) :=
  integrable_threeLevel _ _ _

private theorem asymmetricKernel_mem (v u : I) : asymmetricKernel v u ∈ Icc 0 1 := by
  rw [asymmetricKernel_formula]
  split_ifs <;> simp [v.property]

private theorem asymmetricKernel_monotone (u : I) : Monotone (fun v => asymmetricKernel v u) := by
  intro v w hvw
  have hw : (v : ℝ) ≤ w := hvw
  simp only [asymmetricKernel_formula]
  split_ifs <;> linarith [v.property.1, v.property.2, w.property.1, w.property.2]

private theorem asymmetricKernel_antitone (v : I) : Antitone (asymmetricKernel v) := by
  intro u w huw
  have hw : (u : ℝ) ≤ w := huw
  simp only [asymmetricKernel_formula]
  split_ifs <;> linarith [v.property.1, v.property.2]

private noncomputable def asymmetricCDF (u v : I) : ℝ :=
  (1 - (v : ℝ)) * min (u : ℝ) ((v : ℝ) / 2) +
    (v : ℝ) * min (u : ℝ) (((v : ℝ) + 1) / 2)

private theorem integral_asymmetricKernel (u v : I) :
    (∫ t in Iic u, asymmetricKernel v t) = asymmetricCDF u v :=
  integral_threeLevel_Iic _ _ _ _

private theorem asymmetricCDF_classical :
    Copula.IsClassical (fun z : Fin 2 → I => asymmetricCDF (z 0) (z 1)) := by
  apply Copula.IsClassical.ofBivariate asymmetricCDF
  · intro v
    simp [asymmetricCDF, min_eq_left (by linarith [v.property.1] : (0 : ℝ) ≤ v / 2),
      min_eq_left (by linarith [v.property.1] : (0 : ℝ) ≤ (v + 1) / 2)]
  · intro u
    simp [asymmetricCDF, min_eq_right u.property.1]
  · intro v
    change (1 - (v : ℝ)) * min 1 ((v : ℝ) / 2) +
      (v : ℝ) * min 1 (((v : ℝ) + 1) / 2) = v
    rw [
      min_eq_right (by linarith [v.property.2] : (v : ℝ) / 2 ≤ 1),
      min_eq_right (by linarith [v.property.2] : ((v : ℝ) + 1) / 2 ≤ 1)]
    ring
  · intro u
    norm_num [asymmetricCDF, min_eq_left u.property.2]
  · intro a b c d hab hcd
    have hc := Copula.integral_Iic_add_Ioc_unit (asymmetricKernel_integrable c) hab
    have hd := Copula.integral_Iic_add_Ioc_unit (asymmetricKernel_integrable d) hab
    have hle := setIntegral_mono_on (asymmetricKernel_integrable c).integrableOn
      (asymmetricKernel_integrable d).integrableOn measurableSet_Ioc
      (fun t (_ : t ∈ Ioc a b) => asymmetricKernel_monotone t hcd)
    simp only [integral_asymmetricKernel] at hc hd
    linarith

/-- The actual copula specified by Remark 2.3's conditional-CDF profile. -/
noncomputable def asymmetricEquality : Copula 2 :=
  Copula.ofClassical _ asymmetricCDF_classical

theorem asymmetricEquality_cdf (u v : I) :
    asymmetricEquality.cdf ![u, v] =
      (1 - (v : ℝ)) * min (u : ℝ) ((v : ℝ) / 2) +
        (v : ℝ) * min (u : ℝ) (((v : ℝ) + 1) / 2) := by
  simp [asymmetricEquality, asymmetricCDF]

private theorem asymmetricEquality_primitive (u v : I) :
    asymmetricEquality.cdf ![u, v] = ∫ t in Iic u, asymmetricKernel v t := by
  rw [integral_asymmetricKernel, asymmetricEquality_cdf]
  rfl

private theorem asymmetricEquality_kernel_closed (v : I) :
    (fun u => asymmetricEquality.conditionalCDF u v) =ᵐ[volume] asymmetricKernel v := by
  apply Copula.conditionalCDF_ae_eq_of_integral _ v (asymmetricKernel_integrable v)
  · intro u
    exact (asymmetricKernel_mem v u).1
  · intro u
    exact (asymmetricEquality_primitive u v).symm

theorem asymmetricEquality_isSI : asymmetricEquality.IsSI := by
  intro a b c v hab hbc
  simp only [asymmetricEquality_primitive]
  exact Copula.integral_Iic_concave_of_antitone (asymmetricKernel_integrable v)
    (asymmetricKernel_antitone v) a b c hab hbc

theorem asymmetricEquality_conditionalCDF (v : I) :
    (fun u => asymmetricEquality.conditionalCDF u v) =ᵐ[volume]
      fun u => (if (u : ℝ) < (v : ℝ) / 2 then (1 : ℝ) else 0) +
        (v : ℝ) * (if (v : ℝ) / 2 < (u : ℝ) ∧ (u : ℝ) < ((v : ℝ) + 1) / 2 then 1 else 0) := by
  exact (asymmetricEquality_kernel_closed v).trans
    (threeLevel_eq_open_ae _ _ (by change (v : ℝ) / 2 ≤ (v + 1) / 2; linarith) _)

theorem asymmetricEquality_derivative (v : I) :
    (fun u : I => deriv (Copula.cdfSection asymmetricEquality v) (u : ℝ)) =ᵐ[volume]
      fun u => (if (u : ℝ) < (v : ℝ) / 2 then (1 : ℝ) else 0) +
        (v : ℝ) * (if (v : ℝ) / 2 < (u : ℝ) ∧ (u : ℝ) < ((v : ℝ) + 1) / 2 then 1 else 0) :=
  (asymmetricEquality.conditionalCDF_eq_deriv v).symm.trans (asymmetricEquality_conditionalCDF v)


theorem asymmetricEquality_xi_eq_footrule :
    asymmetricEquality.chatterjeeXi = asymmetricEquality.spearmanFootrule := by
  apply (si_equality_iff_conditional_threeLevel asymmetricEquality asymmetricEquality_isSI).mpr
  have hA : Monotone asymmetricLowerCut := by
    intro v w hvw
    change (v : ℝ) / 2 ≤ (w : ℝ) / 2
    exact div_le_div_of_nonneg_right hvw (by norm_num)
  have hB : Monotone asymmetricUpperCut := by
    intro v w hvw
    change ((v : ℝ) + 1) / 2 ≤ ((w : ℝ) + 1) / 2
    have h : (v : ℝ) ≤ w := hvw
    linarith
  refine ⟨asymmetricLowerCut, asymmetricUpperCut, id, hA, hB, hA.measurable,
    hB.measurable, measurable_id, ?_⟩
  exact Filter.Eventually.of_forall asymmetricEquality_conditionalCDF

theorem asymmetricEquality_coefficients :
    asymmetricEquality.chatterjeeXi = 1 / 2 ∧ asymmetricEquality.spearmanFootrule = 1 / 2 := by
  have hd (v : I) : asymmetricEquality.cdf ![v, v] = (v : ℝ) / 2 + (v : ℝ) ^ 2 / 2 := by
    rw [asymmetricEquality_cdf,
      min_eq_right (by linarith [v.property.1] : (v : ℝ) / 2 ≤ v),
      min_eq_left (by linarith [v.property.2] : (v : ℝ) ≤ (v + 1) / 2)]
    ring
  have hf : asymmetricEquality.spearmanFootrule = 1 / 2 := by
    rw [Copula.spearmanFootrule]
    simp_rw [hd]
    rw [integral_add (Copula.integrable_continuous_unit volume (by fun_prop))
      (Copula.integrable_continuous_unit volume (by fun_prop)), integral_div, integral_div,
      Copula.integral_unit_id, Copula.integral_unit_pow]
    norm_num
  exact ⟨asymmetricEquality_xi_eq_footrule.trans hf, hf⟩

/-- Exact unequal transposed CDF values certify genuine asymmetry. -/
theorem asymmetricEquality_asymmetry_witness :
    asymmetricEquality.cdf ![⟨1 / 4, by constructor <;> norm_num⟩, Copula.unitHalf] = 1 / 4 ∧
      asymmetricEquality.cdf ![Copula.unitHalf, ⟨1 / 4, by constructor <;> norm_num⟩] = 7 / 32 := by
  constructor <;> rw [asymmetricEquality_cdf] <;> norm_num [Copula.unitHalf]

theorem asymmetricEquality_not_exchangeable : ¬asymmetricEquality.IsExchangeable := by
  intro h
  have he := (Copula.isExchangeable_iff _).mp h
    ⟨1 / 4, by constructor <;> norm_num⟩ Copula.unitHalf
  rw [asymmetricEquality_asymmetry_witness.1, asymmetricEquality_asymmetry_witness.2] at he
  norm_num at he

end Papers.Rockel2026XiFootrule
