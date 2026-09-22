import Verification.ForwardGraphUniqueness
import Copula.Rank.Conditional

/-! # A copula on a forward graph and its transpose is unique -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

noncomputable def upperGraph (τ : I → I) (u : I) : Fin 2 → I := ![u, τ u]
noncomputable def lowerGraph (τ : I → I) (u : I) : Fin 2 → I := ![τ u, u]

def ForwardGraphSupport (C : Copula 2) (τ : I → I) (q : ℝ) : Prop :=
  ∀ᵐ x ∂C.toMeasure,
    (upperGraph τ (x 0) = x ∧ (x 0 : ℝ) + q ≤ x 1) ∨
    (lowerGraph τ (x 1) = x ∧ (x 1 : ℝ) + q ≤ x 0)

private def upperTriangle : Set (Fin 2 → I) := {x | x 0 < x 1}
private theorem upperTriangle_measurable : MeasurableSet upperTriangle :=
  measurableSet_lt (measurable_pi_apply 0) (measurable_pi_apply 1)

private noncomputable def upperSource (C : Copula 2) : Measure I :=
  (C.toMeasure.restrict upperTriangle).map (fun x => x 0)
private noncomputable def lowerSource (C : Copula 2) : Measure I :=
  (C.toMeasure.restrict upperTriangleᶜ).map (fun x => x 1)

private instance (C : Copula 2) : IsFiniteMeasure (upperSource C) :=
  inferInstanceAs (IsFiniteMeasure ((C.toMeasure.restrict upperTriangle).map _))
private instance (C : Copula 2) : IsFiniteMeasure (lowerSource C) :=
  inferInstanceAs (IsFiniteMeasure ((C.toMeasure.restrict upperTriangleᶜ).map _))

private theorem upper_support (C : Copula 2) (τ : I → I) (q : ℝ) (hq : 0 < q)
    (hC : ForwardGraphSupport C τ q) :
    ∀ᵐ x ∂C.toMeasure.restrict upperTriangle,
      upperGraph τ (x 0) = x ∧ (x 0 : ℝ) + q ≤ τ (x 0) := by
  filter_upwards [ae_restrict_of_ae hC, ae_restrict_mem upperTriangle_measurable] with x hx ht
  rcases hx with ⟨he, hd⟩ | ⟨_, hd⟩
  · refine ⟨he, ?_⟩
    have he' : τ (x 0) = x 1 := congrArg (fun z => z 1) he
    rwa [he']
  · have ht' : (x 0 : ℝ) < x 1 := ht
    linarith

private theorem lower_support (C : Copula 2) (τ : I → I) (q : ℝ) (hq : 0 < q)
    (hC : ForwardGraphSupport C τ q) :
    ∀ᵐ x ∂C.toMeasure.restrict upperTriangleᶜ,
      lowerGraph τ (x 1) = x ∧ (x 1 : ℝ) + q ≤ τ (x 1) := by
  filter_upwards [ae_restrict_of_ae hC, ae_restrict_mem upperTriangle_measurable.compl] with x hx ht
  rcases hx with ⟨_, hd⟩ | ⟨he, hd⟩
  · have ht' : (x 1 : ℝ) ≤ x 0 := le_of_not_gt ht
    linarith
  · refine ⟨he, ?_⟩
    have he' : τ (x 1) = x 0 := congrArg (fun z => z 0) he
    rwa [he']

private theorem graph_decomposition (C : Copula 2) (τ : I → I) (hτ : Measurable τ)
    (q : ℝ) (hq : 0 < q) (hC : ForwardGraphSupport C τ q) :
    (upperSource C).map (upperGraph τ) + (lowerSource C).map (lowerGraph τ) = C.toMeasure := by
  have hu : Measurable (upperGraph τ) := by unfold upperGraph; fun_prop
  have hl : Measurable (lowerGraph τ) := by unfold lowerGraph; fun_prop
  have he₁ : (upperSource C).map (upperGraph τ) = C.toMeasure.restrict upperTriangle := by
    rw [upperSource, Measure.map_map hu (measurable_pi_apply 0)]
    calc
      _ = (C.toMeasure.restrict upperTriangle).map id :=
        Measure.map_congr ((upper_support C τ q hq hC).mono fun _ h => h.1)
      _ = _ := Measure.map_id
  have he₂ : (lowerSource C).map (lowerGraph τ) = C.toMeasure.restrict upperTriangleᶜ := by
    rw [lowerSource, Measure.map_map hl (measurable_pi_apply 1)]
    calc
      _ = (C.toMeasure.restrict upperTriangleᶜ).map id :=
        Measure.map_congr ((lower_support C τ q hq hC).mono fun _ h => h.1)
      _ = _ := Measure.map_id
  rw [he₁, he₂]
  exact Measure.restrict_add_restrict_compl upperTriangle_measurable

/-- Uniform marginals determine a copula supported on a forward graph and its transpose. -/
theorem copula_forward_graph_unique (C D : Copula 2) (τ : I → I) (hτ : Measurable τ)
    (q : ℝ) (hq : 0 < q) (hC : ForwardGraphSupport C τ q) (hD : ForwardGraphSupport D τ q) :
    C = D := by
  have hs (E : Copula 2) (hE : ForwardGraphSupport E τ q) :
      (∀ᵐ u : I ∂upperSource E, (u : ℝ) + q ≤ τ u) ∧
      (∀ᵐ u : I ∂lowerSource E, (u : ℝ) + q ≤ τ u) := by
    have hm : MeasurableSet {u : I | (u : ℝ) + q ≤ τ u} :=
      measurableSet_le (measurable_subtype_coe.add_const q) (measurable_subtype_coe.comp hτ)
    constructor
    · exact (ae_map_iff (measurable_pi_apply 0).aemeasurable hm).2
        ((upper_support E τ q hq hE).mono fun _ h => h.2)
    · exact (ae_map_iff (measurable_pi_apply 1).aemeasurable hm).2
        ((lower_support E τ q hq hE).mono fun _ h => h.2)
  have hmarg (E : Copula 2) (hE : ForwardGraphSupport E τ q) :
      upperSource E + (lowerSource E).map τ = volume ∧
      lowerSource E + (upperSource E).map τ = volume := by
    have hu : Measurable (upperGraph τ) := by unfold upperGraph; fun_prop
    have hl : Measurable (lowerGraph τ) := by unfold lowerGraph; fun_prop
    have h (i : Fin 2) := congrArg (fun μ : Measure (Fin 2 → I) => μ.map (fun x => x i))
      (graph_decomposition E τ hτ q hq hE)
    simp only [Measure.map_add _ _ (measurable_pi_apply _),
      Measure.map_map (measurable_pi_apply _) hu,
      Measure.map_map (measurable_pi_apply _) hl, E.map_eval] at h
    constructor
    · simpa only [Function.comp_def, upperGraph, lowerGraph, Matrix.cons_val_zero,
        Measure.map_id'] using h 0
    · simpa only [Function.comp_def, upperGraph, lowerGraph, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Measure.map_id', add_comm] using h 1
  obtain ⟨hα, hβ⟩ := forward_graph_marginals_unique τ hτ q hq
    (upperSource C) (lowerSource C) (upperSource D) (lowerSource D)
    (hs C hC).1 (hs C hC).2 (hs D hD).1 (hs D hD).2
    ((hmarg C hC).1.trans (hmarg D hD).1.symm)
    ((hmarg C hC).2.trans (hmarg D hD).2.symm)
  apply Copula.ext
  rw [← graph_decomposition C τ hτ q hq hC, ← graph_decomposition D τ hτ q hq hD, hα, hβ]

end Verification
