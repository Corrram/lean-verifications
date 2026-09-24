import Copula.Dependence.Density
import Mathlib.MeasureTheory.Integral.Prod

/-! # Fubini for lower orthants of the bivariate unit cube -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

theorem integral_cube_Iic_iterated {f : (Fin 2 → I) → ℝ} (hf : Integrable f) (u v : I) :
    (∫ x in Iic ![u,v], f x) = ∫ s in Iic u, ∫ t in Iic v, f ![s,t] := by
  have hm := (volume_preserving_finTwoArrow I).symm MeasurableEquiv.finTwoArrow
  have he := hm.setIntegral_preimage_emb MeasurableEquiv.finTwoArrow.symm.measurableEmbedding f (Iic ![u,v])
  have hs : MeasurableEquiv.finTwoArrow.symm ⁻¹' Iic ![u,v] = Iic u ×ˢ Iic v := by
    ext p
    change (∀ i : Fin 2, (![p.1,p.2] i) ≤ ![u,v] i) ↔ p.1 ≤ u ∧ p.2 ≤ v
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hs] at he
  rw [← he]
  have hi := hm.integrable_comp_of_integrable hf
  exact setIntegral_prod _ hi.integrableOn

private theorem integral_fin_two_unit (f : (Fin 2 → I) → ℝ)
    (hf : Integrable f) :
    (∫ x, f x) = ∫ u : I, ∫ v : I, f ![u, v] := by
  let e : (Fin 2 → I) ≃ᵐ I × I := MeasurableEquiv.finTwoArrow
  have hp : MeasurePreserving e (volume : Measure (Fin 2 → I))
      (volume : Measure (I × I)) := volume_preserving_finTwoArrow I
  have hi : Integrable (fun p : I × I => f (e.symm p)) :=
    hp.symm.integrable_comp_of_integrable hf
  have h := hp.integral_comp' (fun p : I × I => f (e.symm p))
  rw [Measure.volume_eq_prod I I] at hi h
  rw [integral_prod _ hi] at h
  have heta (x : Fin 2 → I) : ![x 0, x 1] = x := by
    ext i
    fin_cases i <;> simp
  simpa [e, MeasurableEquiv.finTwoArrow, heta] using h

private theorem integral_unit_Ioc_real (f : ℝ → ℝ) (a b : I) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b, f (t : ℝ)) =
      ∫ t in (a : ℝ)..(b : ℝ), f t := by
  classical
  rw [← integral_indicator measurableSet_Ioc]
  have he : (Set.Ioc a b).indicator (fun t : I => f (t : ℝ)) =
      fun t : I => (Set.Ioc (a : ℝ) (b : ℝ)).indicator f (t : ℝ) := rfl
  rw [he, Copula.integral_unitInterval, intervalIntegral.integral_of_le zero_le_one,
    setIntegral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hab]
  have hs : Set.Ioc (0 : ℝ) 1 ∩ Set.Ioc (a : ℝ) (b : ℝ) =
      Set.Ioc (a : ℝ) (b : ℝ) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioc]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨⟨lt_of_le_of_lt a.property.1 h.1,
        h.2.trans b.property.2⟩, h⟩
  rw [hs]

private theorem integral_cube_Ioc_two (f : (Fin 2 → I) → ℝ)
    (a b c d : I)
    (hf : IntegrableOn f
      (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i)))) :
    (∫ x in Set.pi Set.univ
      (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i)), f x) =
      ∫ u in Set.Ioc a b, ∫ v in Set.Ioc c d, f ![u, v] := by
  classical
  let s : Set (Fin 2 → I) :=
    Set.pi Set.univ (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i))
  have hs : MeasurableSet s := by
    dsimp [s]
    exact MeasurableSet.pi Set.countable_univ (fun i _ => by fin_cases i <;> simp)
  change (∫ x in s, f x) = _
  rw [← integral_indicator hs, integral_fin_two_unit _ (hf.integrable_indicator hs)]
  have he (u v : I) : s.indicator f ![u, v] =
      (Set.Ioc a b).indicator
        (fun u : I => (Set.Ioc c d).indicator (fun v : I => f ![u, v]) v) u := by
    have hmem : (![u, v] ∈ s) ↔ u ∈ Set.Ioc a b ∧ v ∈ Set.Ioc c d := by
      simp [s, Set.mem_pi, Fin.forall_fin_two]
    by_cases hu : u ∈ Set.Ioc a b <;> by_cases hv : v ∈ Set.Ioc c d
    all_goals simp [Set.indicator, hmem, hu, hv]
  change (∫ u : I, ∫ v : I, s.indicator f ![u, v]) = _
  simp_rw [he]
  simp_rw [integral_indicator₂]
  rw [integral_indicator measurableSet_Ioc]
  simp_rw [integral_indicator measurableSet_Ioc]

theorem integral_cube_Ioc_two_real (F : ℝ → ℝ → ℝ)
    (a b c d : I) (hab : a ≤ b) (hcd : c ≤ d)
    (hF : IntegrableOn
      (fun x : Fin 2 → I => F (x 0 : ℝ) (x 1 : ℝ))
      (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i)))) :
    (∫ x in Set.pi Set.univ
      (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i)),
      F (x 0 : ℝ) (x 1 : ℝ)) =
      ∫ u in (a : ℝ)..(b : ℝ), ∫ v in (c : ℝ)..(d : ℝ), F u v := by
  calc
    _ = ∫ u in Set.Ioc a b, ∫ v in Set.Ioc c d,
        F (u : ℝ) (v : ℝ) := integral_cube_Ioc_two _ a b c d hF
    _ = ∫ u in Set.Ioc a b, ∫ v in (c : ℝ)..(d : ℝ),
        F (u : ℝ) v := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u _
      exact integral_unit_Ioc_real (fun v => F (u : ℝ) v) c d hcd
    _ = _ := integral_unit_Ioc_real
      (fun u => ∫ v in (c : ℝ)..(d : ℝ), F u v) a b hab

end Verification
