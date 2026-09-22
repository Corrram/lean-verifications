import Verification.DualContactRigidity
import Verification.CopulaGraphUniqueness
import Mathlib.Topology.Order.ProjIcc

/-! # Uniqueness of copulas saturating a strictly Lipschitz distance dual -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval NNReal Topology

namespace Verification

noncomputable def dualForward (g : ℝ → ℝ) (θ : ℝ) (a : I) : I :=
  projIcc 0 1 (by norm_num) ((a : ℝ) + (θ - deriv g a) / 2)

theorem measurable_dualForward (g : ℝ → ℝ) (θ : ℝ) : Measurable (dualForward g θ) := by
  unfold dualForward
  exact continuous_projIcc.measurable.comp
    (measurable_subtype_coe.add ((measurable_const.sub
      ((measurable_deriv g).comp measurable_subtype_coe)).div_const 2))

private theorem contact_forward (g : ℝ → ℝ) (v : ℝ≥0) (θ : ℝ)
    (hg : LipschitzWith v g)
    (hf : ∀ a b : ℝ, g a + g b ≤ (b-a)^2 - θ * |b-a|)
    (a b : I) (hab : a < b) (hd : DifferentiableAt ℝ g a)
    (he : g a + g b = ((b : ℝ)-a)^2 - θ * |(b : ℝ)-a|) :
    dualForward g θ a = b ∧ (a : ℝ) + (θ-v)/2 ≤ b := by
  have hb := dual_upper_contact g θ a b hf hab hd he
  constructor
  · unfold dualForward
    rw [← hb, projIcc_of_mem _ b.property]
  · have hder : deriv g a ≤ v := (abs_le.mp (by
      simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz hg (x₀ := (a : ℝ)))).2
    linarith

/-- Equality in the distance dual forces support on one forward graph and its transpose. -/
theorem dual_contact_graph_support (C : Copula 2) (g : ℝ → ℝ) (v : ℝ≥0) (θ : ℝ)
    (hg : LipschitzWith v g) (hθ : (v : ℝ) < θ)
    (hf : ∀ a b : ℝ, g a + g b ≤ (b-a)^2 - θ * |b-a|)
    (hC : ∀ᵐ x ∂C.toMeasure,
      g (x 0) + g (x 1) = ((x 1 : ℝ)-x 0)^2 - θ * |(x 1 : ℝ)-x 0|) :
    ForwardGraphSupport C (dualForward g θ) ((θ-v)/2) := by
  have hd : ∀ᵐ u : I, DifferentiableAt ℝ g (u : ℝ) := by
    apply ae_of_ae_map measurable_subtype_coe.aemeasurable
    rw [unitInterval.measurePreserving_coe.map_eq]
    exact ae_restrict_of_ae hg.ae_differentiableAt
  have hd' (i : Fin 2) : ∀ᵐ x ∂C.toMeasure, DifferentiableAt ℝ g (x i : ℝ) := by
    apply ae_of_ae_map (f := fun x : Fin 2 → I => x i)
      (p := fun u : I => DifferentiableAt ℝ g (u : ℝ))
      (measurable_pi_apply i).aemeasurable
    rw [C.map_eval]
    exact hd
  filter_upwards [hC, hd' 0, hd' 1] with x he hd0 hd1
  rcases lt_trichotomy (x 0) (x 1) with hlt | heq | hgt
  · obtain ⟨ht, hgap⟩ := contact_forward g v θ hg hf (x 0) (x 1) hlt hd0 he
    refine Or.inl ⟨?_, hgap⟩
    funext i
    fin_cases i
    · rfl
    · exact ht
  · rw [heq] at he
    have hn := dual_potential_negative g v θ hg hθ hf (x 1)
    simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), abs_zero, mul_zero] at he
    linarith
  · have he' : g (x 1) + g (x 0) = ((x 0 : ℝ)-x 1)^2 - θ * |(x 0 : ℝ)-x 1| := by
      rw [add_comm, sub_sq_comm, abs_sub_comm]
      exact he
    obtain ⟨ht, hgap⟩ := contact_forward g v θ hg hf (x 1) (x 0) hgt hd1 he'
    refine Or.inr ⟨?_, hgap⟩
    funext i
    fin_cases i
    · exact ht
    · rfl

/-- The global dual inequality and a strict Lipschitz gap imply uniqueness, even
among nonsymmetric copulas and singular measures. -/
theorem copula_dual_contact_unique (C D : Copula 2) (g : ℝ → ℝ) (v : ℝ≥0) (θ : ℝ)
    (hg : LipschitzWith v g) (hθ : (v : ℝ) < θ)
    (hf : ∀ a b : ℝ, g a + g b ≤ (b-a)^2 - θ * |b-a|)
    (hC : ∀ᵐ x ∂C.toMeasure,
      g (x 0) + g (x 1) = ((x 1 : ℝ)-x 0)^2 - θ * |(x 1 : ℝ)-x 0|)
    (hD : ∀ᵐ x ∂D.toMeasure,
      g (x 0) + g (x 1) = ((x 1 : ℝ)-x 0)^2 - θ * |(x 1 : ℝ)-x 0|) : C = D :=
  copula_forward_graph_unique C D (dualForward g θ) (measurable_dualForward g θ)
    ((θ-v)/2) (by linarith)
    (dual_contact_graph_support C g v θ hg hθ hf hC)
    (dual_contact_graph_support D g v θ hg hθ hf hD)

end Verification
