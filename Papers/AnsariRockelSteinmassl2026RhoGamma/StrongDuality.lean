import Papers.AnsariRockelSteinmassl2026RhoGamma.SlopeCoverage
import Papers.AnsariRockelSteinmassl2026RhoGamma.SignAttainment

/-! # Unconditional attained transport duality for every positive multiplier -/

open MeasureTheory ProbabilityTheory
open scoped unitInterval
open Copula.RankRegion

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

private theorem large_slope_feasible {t : ℝ} (ht : 1 ≤ t) (x : Fin 2 → I) :
    magnitudeCost t x ≤ (x 0 : ℝ) * (t - x 0) / 2 + (x 1 : ℝ) * (t - x 1) / 2 := by
  rcases (x 0).property with ⟨h00, h01⟩
  rcases (x 1).property with ⟨h10, h11⟩
  unfold magnitudeCost
  rcases le_total (x 0 : ℝ) (x 1 : ℝ) with h | h
  · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith)]
    have hh := mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ t - ((x 1 : ℝ) - x 0) by linarith)
    nlinarith
  · rw [min_eq_right h, max_eq_left h, abs_of_nonpos (by linarith)]
    have hh := mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ t - ((x 0 : ℝ) - x 1) by linarith)
    nlinarith

/-- No contact or optimizer assumption: both are constructed for every t>0. -/
theorem transport_primal_dual_attained {t : ℝ} (ht : 0 < t) :
    ∃ (D : Copula 2) (f : I → ℝ), Continuous f ∧
      (∀ x : Fin 2 → I, magnitudeCost t x ≤ f (x 0) + f (x 1)) ∧
      (∀ᵐ x ∂D.toMeasure, magnitudeCost t x = f (x 0) + f (x 1)) := by
  by_cases ht1 : t < 1
  · obtain ⟨A, rfl⟩ := supporting_slope_covered ht ht1
    exact ⟨A.magnitudes, fun u => A.dual u,
      A.continuous_dual.comp continuous_subtype_val, fun x => A.dual_feasible (x 0) (x 1),
      A.magnitude_contact⟩
  · refine ⟨Copula.comonotonic 2, fun u => (u : ℝ) * (t - u) / 2, by fun_prop,
      large_slope_feasible (le_of_not_gt ht1), ?_⟩
    rw [Copula.toMeasure_comonotonic]
    apply (ae_map_iff (by fun_prop) (isClosed_eq (continuous_magnitudeCost t) (by fun_prop)).measurableSet).2
    filter_upwards [] with u
    dsimp [magnitudeCost]
    rw [min_self, max_self, abs_of_nonpos (by linarith [u.property.2])]
    ring

/-- Feasible symmetric continuous dual potentials, as in equation (33). -/
def dualCosts (t : ℝ) : Set ℝ :=
  {v | ∃ f : I → ℝ, Continuous f ∧
    (∀ x : Fin 2 → I, magnitudeCost t x ≤ f (x 0) + f (x 1)) ∧ v = 2 * ∫ u : I, f u}

/-- Remark 3.4: the primal supremum is the attained dual infimum. -/
theorem transport_strong_duality {t : ℝ} (ht : 0 < t) :
    IsLeast (dualCosts t) (transportValue t) := by
  obtain ⟨D, f, hf, hfeasible, hcontact⟩ := transport_primal_dual_attained ht
  have hv := transport_contact_value D t hf hcontact
  have hopt := (transport_contact_optimal D t hf hfeasible hcontact).1
  have hg : IsGreatest (Set.range (fun E : Copula 2 => ∫ x, magnitudeCost t x ∂E.toMeasure))
      (∫ x, magnitudeCost t x ∂D.toMeasure) := by
    refine ⟨⟨D, rfl⟩, ?_⟩
    rintro _ ⟨E, rfl⟩
    exact hopt E
  have he : transportValue t = 2 * ∫ u : I, f u := hg.csSup_eq.trans hv
  constructor
  · exact ⟨f, hf, hfeasible, he⟩
  · rintro v ⟨g, hg, hgf, rfl⟩
    rw [he, ← hv]
    exact transport_weak_duality D t hg hgf

/-- Equality with the dual infimum, with no supplied certificate. -/
theorem transportValue_eq_dual_infimum {t : ℝ} (ht : 0 < t) :
    transportValue t = sInf (dualCosts t) :=
  (transport_strong_duality ht).csInf_eq.symm

end Papers.AnsariRockelSteinmassl2026RhoGamma
