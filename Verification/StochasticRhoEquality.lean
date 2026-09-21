import Verification.MonotoneMomentEquality
import Copula.Rank.ConditionalDistance
import Copula.Rank.ChatterjeeExamples

/-! # Equality in the stochastic xi-rho bound

The scalar moment defect forces conditional CDFs to be constant or binary.
Monotonicity in the response threshold excludes mixing these two types at
interior thresholds. This argument includes singular copulas.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

theorem conditionalCDF_constant_or_binary_of_moment_eq (C : Copula 2)
    (hC : C.IsSI) (v : I)
    (he : (∫ u : I, C.conditionalCDF u v ^ 2) =
      2 * (∫ u : I, C.cdf ![u, v]) - (v : ℝ) + (v : ℝ) ^ 2) :
    (∀ᵐ u : I, C.conditionalCDF u v = (v : ℝ)) ∨
      (∀ᵐ u : I, C.conditionalCDF u v = 0 ∨ C.conditionalCDF u v = 1) := by
  obtain ⟨g, hg, hb, ha⟩ := conditionalCDF_antitone_version C hC v
  have hm : (∫ u : I, g u) = (v : ℝ) :=
    (integral_congr_ae ha).symm.trans (C.integral_conditionalCDF v)
  have hF (u : I) : (∫ w in Iic u, g w) = C.cdf ![u, v] := by
    rw [C.cdf_eq_integral_conditionalCDF]
    exact integral_congr_ae (ae_restrict_of_ae ha.symm)
  have hsq : (∫ u : I, C.conditionalCDF u v ^ 2) = ∫ u : I, g u ^ 2 :=
    integral_congr_ae (ha.fun_comp (fun z : ℝ => z ^ 2))
  have he' : (∫ u : I, g u ^ 2) = 2 * (∫ u : I, ∫ w in Iic u, g w) -
      (∫ u : I, g u) + (∫ u : I, g u) ^ 2 := by
    simp_rw [hF, hm]
    exact hsq.symm.trans he
  rcases ae_constant_or_binary_of_moment_eq hg hb he' with hc | hc
  · left
    filter_upwards [ha, hc] with u hu hconst
    simpa only [hu, hm] using hconst
  · right
    filter_upwards [ha, hc] with u hu hbin
    simpa only [hu] using hbin

theorem conditionalCDF_constant_or_binary_of_xi_eq_rho (C : Copula 2)
    (hC : C.IsSI) (he : C.chatterjeeXi = C.spearmanRho) :
    ∀ᵐ v : I, (∀ᵐ u : I, C.conditionalCDF u v = (v : ℝ)) ∨
      (∀ᵐ u : I, C.conditionalCDF u v = 0 ∨ C.conditionalCDF u v = 1) := by
  have hi : Integrable (fun p : I × I => C.cdf ![p.1, p.2])
      ((volume : Measure I).prod volume) :=
    (C.continuous_cdf.comp (by fun_prop)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hv : Integrable (fun v : I => (v : ℝ)) :=
    Copula.integrable_continuous_unit volume continuous_subtype_val
  have hs : Integrable (fun v : I => (v : ℝ) ^ 2) :=
    Copula.integrable_continuous_unit volume (by fun_prop)
  have hd : Integrable (fun v : I => 2 * (∫ u : I, C.cdf ![u, v]) - (v : ℝ)) :=
    (hi.integral_prod_right.const_mul 2).sub hv
  have ha : Integrable (fun v : I => 2 * (∫ u : I, C.cdf ![u, v]) - (v : ℝ) + (v : ℝ) ^ 2) :=
    hd.add hs
  have hz : (∫ v : I, 2 * (∫ u : I, C.cdf ![u, v]) - (v : ℝ) + (v : ℝ) ^ 2 -
      ∫ u : I, C.conditionalCDF u v ^ 2) = 0 := by
    rw [integral_sub ha C.integrable_integral_conditionalCDF_sq, integral_add hd hs,
      integral_sub (hi.integral_prod_right.const_mul 2) hv, integral_const_mul,
      Copula.integral_unit_id, Copula.integral_unit_pow]
    rw [spearmanRho_eq_iterated_cdf] at he
    unfold Copula.chatterjeeXi at he
    norm_num
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun v => sub_nonneg.mpr (conditionalCDF_sq_le_cdf_integral C hC v))
    (ha.sub C.integrable_integral_conditionalCDF_sq)).mp hz
  filter_upwards [hae] with v hv
  apply conditionalCDF_constant_or_binary_of_moment_eq C hC v
  simp only [Pi.zero_apply] at hv
  linarith

theorem conditionalCDF_monotone_threshold (C : Copula 2) (u : I) :
    Monotone (C.conditionalCDF u) := by
  intro v w hvw
  exact measureReal_mono (Iic_subset_Iic.mpr hvw)

theorem ae_unit_interior : ∀ᵐ v : I, 0 < (v : ℝ) ∧ (v : ℝ) < 1 := by
  filter_upwards [volume.ae_ne (0 : I), volume.ae_ne (1 : I)] with v hv0 hv1
  constructor
  · exact lt_of_le_of_ne v.property.1 (fun h => hv0 (Subtype.ext h.symm))
  · exact lt_of_le_of_ne v.property.2 (fun h => hv1 (Subtype.ext h))

/-- A constant conditional CDF at one interior threshold excludes a binary
conditional CDF at every other interior threshold. -/
theorem not_binary_of_constant_interior (C : Copula 2) (v w : I)
    (hv : 0 < (v : ℝ) ∧ (v : ℝ) < 1) (hw : 0 < (w : ℝ) ∧ (w : ℝ) < 1)
    (hc : ∀ᵐ u : I, C.conditionalCDF u v = (v : ℝ)) :
    ¬(∀ᵐ u : I, C.conditionalCDF u w = 0 ∨ C.conditionalCDF u w = 1) := by
  intro hb
  rcases le_total w v with hwv | hvw
  · have hz : ∀ᵐ u : I, C.conditionalCDF u w = 0 := by
      filter_upwards [hc, hb] with u hu hub
      have hle := conditionalCDF_monotone_threshold C u hwv
      rcases hub with h0 | h1
      · exact h0
      · rw [hu, h1] at hle
        linarith [hv.2]
    have hm := integral_congr_ae hz
    rw [C.integral_conditionalCDF] at hm
    simp only [integral_zero] at hm
    linarith [hw.1]
  · have ho : ∀ᵐ u : I, C.conditionalCDF u w = 1 := by
      filter_upwards [hc, hb] with u hu hub
      have hle := conditionalCDF_monotone_threshold C u hvw
      rcases hub with h0 | h1
      · rw [hu, h0] at hle
        linarith [hv.1]
      · exact h1
    have hm := integral_congr_ae ho
    rw [C.integral_conditionalCDF] at hm
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hm
    linarith [hw.2]

theorem xi_eq_one_of_conditionalCDF_binary (C : Copula 2)
    (hb : ∀ᵐ v : I, ∀ᵐ u : I, C.conditionalCDF u v = 0 ∨ C.conditionalCDF u v = 1) :
    C.chatterjeeXi = 1 := by
  have he : (fun v : I => ∫ u : I, C.conditionalCDF u v ^ 2) =ᵐ[volume] fun v => (v : ℝ) := by
    filter_upwards [hb] with v hv
    rw [← C.integral_conditionalCDF v]
    apply integral_congr_ae
    filter_upwards [hv] with u hu
    rcases hu with hu | hu <;> simp only [hu] <;> norm_num
  unfold Copula.chatterjeeXi
  rw [integral_congr_ae he, Copula.integral_unit_id]
  norm_num

/-- The full equality classification for arbitrary SI copulas. -/
theorem isSI_xi_eq_rho_iff (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi = C.spearmanRho ↔ C = Copula.independence 2 ∨ C = Copula.comonotonic 2 := by
  constructor
  · intro he
    have ha := conditionalCDF_constant_or_binary_of_xi_eq_rho C hC he
    by_cases hex : ∃ v : I, (0 < (v : ℝ) ∧ (v : ℝ) < 1) ∧
        (∀ᵐ u : I, C.conditionalCDF u v = (v : ℝ))
    · obtain ⟨v, hv, hc⟩ := hex
      left
      apply Copula.ext_conditionalCDF_ae
      filter_upwards [ha, ae_unit_interior] with w hw hwi
      have hconst : ∀ᵐ u : I, C.conditionalCDF u w = (w : ℝ) :=
        hw.resolve_right (not_binary_of_constant_interior C v w hv hwi hc)
      filter_upwards [hconst, Copula.conditionalCDF_independence w] with u hu hpi
      exact hu.trans hpi.symm
    · right
      apply (isSI_xi_eq_one_iff C hC).mp
      apply xi_eq_one_of_conditionalCDF_binary
      filter_upwards [ha, ae_unit_interior] with v hv hvi
      exact hv.resolve_left (fun hc => hex ⟨v, hvi, hc⟩)
  · rintro (rfl | rfl) <;> simp

/-- The full equality classification for arbitrary SD copulas. -/
theorem isSD_xi_eq_neg_rho_iff (C : Copula 2) (hC : C.IsSD) :
    C.chatterjeeXi = -C.spearmanRho ↔ C = Copula.independence 2 ∨ C = Copula.countermonotonic := by
  constructor
  · intro he
    have hr : (C.reflect {1}).chatterjeeXi = (C.reflect {1}).spearmanRho := by
      simpa only [xi_reflect_second, Copula.spearmanRho_reflect_second] using he
    rcases (isSI_xi_eq_rho_iff _ ((Copula.isSI_reflect_second_iff C).mpr hC)).mp hr with hp | hm
    · left
      apply (Copula.chatterjeeXi_eq_zero_iff C).mp
      have hz := congrArg Copula.chatterjeeXi hp
      simpa only [xi_reflect_second, Copula.chatterjeeXi_independence] using hz
    · right
      have hr := congrArg (fun D : Copula 2 => D.reflect {1}) hm
      simpa only [Copula.reflect_reflect, Copula.reflect_comonotonic_eq_countermonotonic] using hr
  · rintro (rfl | rfl) <;> simp

/-- Equality in xi <= abs(rho) holds exactly at W, independence, and M. -/
theorem stochastic_xi_eq_abs_rho_iff (C : Copula 2) (hC : C.IsSI ∨ C.IsSD) :
    C.chatterjeeXi = |C.spearmanRho| ↔
      C = Copula.countermonotonic ∨ C = Copula.independence 2 ∨ C = Copula.comonotonic 2 := by
  constructor
  · intro he
    rcases hC with hsi | hsd
    · have hn : 0 ≤ C.spearmanRho := C.chatterjeeXi_nonneg.trans (xi_le_rho_of_isSI C hsi)
      rw [abs_of_nonneg hn] at he
      exact Or.inr ((isSI_xi_eq_rho_iff C hsi).mp he)
    · have hn : C.spearmanRho ≤ 0 := by
        linarith [C.chatterjeeXi_nonneg, xi_le_neg_rho_of_isSD C hsd]
      rw [abs_of_nonpos hn] at he
      rcases (isSD_xi_eq_neg_rho_iff C hsd).mp he with hp | hw
      · exact Or.inr (Or.inl hp)
      · exact Or.inl hw
  · rintro (rfl | rfl | rfl) <;> simp

end Verification
