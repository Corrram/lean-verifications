import Papers.AnsariRockel2026XiRho.StochasticBounds
import Verification.StochasticRhoEquality

/-! # Theorem 2 and the equality cases in Lemma 8

The copula statements have no density or parametric-family restriction.
For the scalar lemma, equality of functions is almost everywhere: integrals
cannot distinguish choices on null sets, including interval endpoints.
The proof uses pairwise moment defects, rather than the source's
maximum-principle argument.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Papers.AnsariRockel2026XiRho

/-- The functional F_v from Lemma 8; its admissible functions have mean v. -/
noncomputable def decreasingFunctional (g : I → ℝ) : ℝ :=
  ∫ u : I, 2 * ((1 - (u : ℝ)) * g u) - g u ^ 2

private theorem decreasingFunctional_eq {g : I → ℝ} (hg : Antitone g)
    (hb : ∀ u, g u ∈ Icc 0 1) :
    decreasingFunctional g =
      2 * (∫ u : I, ∫ w in Iic u, g w) - ∫ u : I, g u ^ 2 := by
  have hw : Integrable (fun u : I => (1 - (u : ℝ)) * g u) :=
    Verification.integrable_unit_bounded
      ((measurable_const.sub measurable_subtype_coe).mul hg.measurable)
      (fun u => ⟨mul_nonneg (sub_nonneg.mpr u.property.2) (hb u).1, by
        nlinarith [u.property.1, u.property.2, (hb u).1, (hb u).2]⟩)
  have hs : Integrable (fun u => g u ^ 2) :=
    Verification.integrable_unit_bounded (hg.measurable.pow_const 2)
      (fun u => ⟨sq_nonneg _, by nlinarith [(hb u).1, (hb u).2]⟩)
  rw [decreasingFunctional, integral_sub (hw.const_mul 2) hs, integral_const_mul,
    ← Verification.integral_lower_integral hg.measurable hb]

/-- Lemma 8, inequality, including the mean endpoints. -/
theorem lemma8_bound {g : I → ℝ} (hg : Antitone g) (hb : ∀ u, g u ∈ Icc 0 1)
    (v : I) (hm : (∫ u : I, g u) = (v : ℝ)) :
    (v : ℝ) * (1 - (v : ℝ)) ≤ decreasingFunctional g := by
  have h := Verification.integral_sq_le_twice_lower_integral hg hb
  rw [hm] at h
  rw [decreasingFunctional_eq hg hb]
  nlinarith

/-- Lemma 8, equality classification modulo null sets. -/
theorem lemma8_equality {g : I → ℝ} (hg : Antitone g) (hb : ∀ u, g u ∈ Icc 0 1)
    (v : I) (hm : (∫ u : I, g u) = (v : ℝ)) :
    decreasingFunctional g = (v : ℝ) * (1 - (v : ℝ)) ↔
      (∀ᵐ u : I, g u = (v : ℝ)) ∨ g =ᵐ[volume] (Iic v).indicator (fun _ => (1 : ℝ)) := by
  rw [← Verification.moment_eq_iff_ae_constant_or_lower_indicator hg hb v hm,
    decreasingFunctional_eq hg hb]
  constructor <;> intro h <;> nlinarith

theorem si_xi_eq_rho_iff (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi = C.spearmanRho ↔ C = Copula.independence 2 ∨ C = Copula.comonotonic 2 :=
  Verification.isSI_xi_eq_rho_iff C hC

theorem sd_xi_eq_neg_rho_iff (C : Copula 2) (hC : C.IsSD) :
    C.chatterjeeXi = -C.spearmanRho ↔ C = Copula.independence 2 ∨ C = Copula.countermonotonic :=
  Verification.isSD_xi_eq_neg_rho_iff C hC

/-- Theorem 2: the full equality classification. -/
theorem stochastic_xi_eq_abs_rho_iff (C : Copula 2) (hC : C.IsSI ∨ C.IsSD) :
    C.chatterjeeXi = |C.spearmanRho| ↔
      C = Copula.countermonotonic ∨ C = Copula.independence 2 ∨ C = Copula.comonotonic 2 :=
  Verification.stochastic_xi_eq_abs_rho_iff C hC

theorem stochastic_xi_lt_abs_rho (C : Copula 2) (hC : C.IsSI ∨ C.IsSD)
    (hw : C ≠ Copula.countermonotonic) (hp : C ≠ Copula.independence 2)
    (hm : C ≠ Copula.comonotonic 2) : C.chatterjeeXi < |C.spearmanRho| := by
  apply lt_of_le_of_ne (stochastic_xi_le_abs_rho C hC)
  intro he
  rcases (stochastic_xi_eq_abs_rho_iff C hC).mp he with h | h | h
  · exact hw h
  · exact hp h
  · exact hm h

end Papers.AnsariRockel2026XiRho
