import Copula.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Tactic

/-! # Uniqueness from marginals on a forward contact graph -/

open MeasureTheory Set
open scoped unitInterval

namespace Verification

private theorem forward_preimage_cut (τ : I → I) {q : ℝ} (μ : Measure I)
    (hμ : ∀ᵐ x : I ∂μ, (x : ℝ) + q ≤ τ x) (n : ℕ) (s : Set I)
    (hs : s ⊆ {x : I | (x : ℝ) < (n + 1) * q}) :
    μ (τ ⁻¹' s) = μ (τ ⁻¹' s ∩ {x : I | (x : ℝ) < n * q}) := by
  apply measure_congr
  filter_upwards [hμ] with x hx
  apply propext
  change (τ x ∈ s) ↔ τ x ∈ s ∧ (x : ℝ) < n * q
  constructor
  · intro h
    exact ⟨h, by have hh := hs h; dsimp only [mem_ofPred_eq] at hh; linarith⟩
  · exact And.left

/-- Two pairs of finite measures on a forward graph are determined by their two marginals.
The strict positive shift makes the marginal recursion terminate after finitely many strips. -/
theorem forward_graph_marginals_unique (τ : I → I) (hτ : Measurable τ)
    (q : ℝ) (hq : 0 < q) (α β γ δ : Measure I)
    [IsFiniteMeasure α] [IsFiniteMeasure β] [IsFiniteMeasure γ] [IsFiniteMeasure δ]
    (hα : ∀ᵐ x : I ∂α, (x : ℝ) + q ≤ τ x)
    (hβ : ∀ᵐ x : I ∂β, (x : ℝ) + q ≤ τ x)
    (hγ : ∀ᵐ x : I ∂γ, (x : ℝ) + q ≤ τ x)
    (hδ : ∀ᵐ x : I ∂δ, (x : ℝ) + q ≤ τ x)
    (h₁ : α + β.map τ = γ + δ.map τ)
    (h₂ : β + α.map τ = δ + γ.map τ) : α = γ ∧ β = δ := by
  have hind (n : ℕ) : ∀ s : Set I, MeasurableSet s →
      s ⊆ {x : I | (x : ℝ) < n * q} → α s = γ s ∧ β s = δ s := by
    induction n with
    | zero =>
      intro s _ hs
      have he : s = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hh := hs hx
        dsimp only [mem_ofPred_eq] at hh
        norm_num at hh
        exact (not_lt_of_ge x.property.1) hh
      simp [he]
    | succ n ih =>
      intro s hs hcut
      have hcut' : s ⊆ {x : I | (x : ℝ) < (n + 1) * q} := by
        simpa only [Nat.cast_add, Nat.cast_one] using hcut
      let t := τ ⁻¹' s ∩ {x : I | (x : ℝ) < n * q}
      have ht : MeasurableSet t := (hτ hs).inter (measurableSet_lt measurable_subtype_coe measurable_const)
      have htcut : t ⊆ {x : I | (x : ℝ) < n * q} := inter_subset_right
      obtain ⟨ha, hb⟩ := ih t ht htcut
      have hmapα : α.map τ s = γ.map τ s := by
        rw [Measure.map_apply hτ hs, Measure.map_apply hτ hs,
          forward_preimage_cut τ α hα n s hcut', forward_preimage_cut τ γ hγ n s hcut']
        exact ha
      have hmapβ : β.map τ s = δ.map τ s := by
        rw [Measure.map_apply hτ hs, Measure.map_apply hτ hs,
          forward_preimage_cut τ β hβ n s hcut', forward_preimage_cut τ δ hδ n s hcut']
        exact hb
      have he₁ := congrArg (fun μ : Measure I => μ s) h₁
      have he₂ := congrArg (fun μ : Measure I => μ s) h₂
      simp only [Measure.add_apply] at he₁ he₂
      rw [hmapβ] at he₁
      rw [hmapα] at he₂
      exact ⟨(ENNReal.add_left_inj (measure_ne_top _ _)).mp he₁,
        (ENNReal.add_left_inj (measure_ne_top _ _)).mp he₂⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / q)
  have hn' : (1 : ℝ) < n * q := (div_lt_iff₀ hq).mp hn
  have hs (s : Set I) : s ⊆ {x : I | (x : ℝ) < n * q} :=
    fun x _ => lt_of_le_of_lt x.property.2 hn'
  exact ⟨Measure.ext (fun s h => (hind n s h (hs s)).1),
    Measure.ext (fun s h => (hind n s h (hs s)).2)⟩

end Verification
