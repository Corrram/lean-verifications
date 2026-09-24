import Verification.Nelsen13Integrals
import Verification.Nelsen13Dependence

open ProbabilityTheory MeasureTheory Set
open Copula
open scoped unitInterval

namespace Verification

theorem nelsen13_toMeasure_density {θ : ℝ} (hθ : 1 ≤ θ) :
    (nelsen13 θ (by linarith)).toMeasure =
      (volume : Measure (Fin 2 → I)).withDensity (fun x => ENNReal.ofReal (n13Density θ x)) := by
  have hp : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  symm
  apply measure_eq_copula_of_positive_rectangles _ _ (withDensity_absolutelyContinuous _ _)
  intro a b c d ha hab hc hcd
  let s : Set (Fin 2 → I) := Set.pi Set.univ (fun i : Fin 2 => Ioc (![a,c] i) (![b,d] i))
  have hs : MeasurableSet s := MeasurableSet.pi Set.countable_univ
    (fun i _ => by fin_cases i <;> simp)
  have hi := n13Density_integrable_rectangle hp.le a b c d ha hc
  have hn : 0 ≤ᵐ[(volume : Measure (Fin 2 → I)).restrict s] n13Density θ :=
    Filter.Eventually.of_forall (n13Density_nonneg hθ)
  change ((volume : Measure (Fin 2 → I)).withDensity (fun x => ENNReal.ofReal (n13Density θ x))) s = _
  rw [withDensity_apply _ hs, ← ofReal_integral_eq_lintegral_ofReal hi hn,
    n13Density_rectangle_eq_measure hp a b c d ha hab hc hcd]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem nelsen13_hasMTP2Density {θ : ℝ} (hθ : 1 ≤ θ) :
    (nelsen13 θ (by linarith)).HasMTP2Density :=
  ⟨n13Density θ, n13Density_measurable θ, n13Density_nonneg hθ,
    n13Density_mtp2 hθ, nelsen13_toMeasure_density hθ⟩

theorem nelsen13_density_tp2_iff (θ : ℝ) (hθ : 0 ≤ θ) :
    (nelsen13 θ hθ).HasMTP2Density ↔ 1 ≤ θ :=
  ⟨nelsen13_density_tp2_requires_one θ hθ, nelsen13_hasMTP2Density⟩

end Verification
