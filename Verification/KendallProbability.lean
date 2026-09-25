import Copula.Rank.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! # Kendall's tau as a probability of coordinatewise comparison

Fubini identifies the self-CDF integral with the probability that the first
of two independent copula observations is below the second coordinatewise.
-/

open ProbabilityTheory MeasureTheory Set
open scoped unitInterval

namespace Verification

theorem kendallTau_probability (C : Copula 2) :
    C.kendallTau=4*(C.toMeasure.prod C.toMeasure).real
      {p : (Fin 2 → I)×(Fin 2 → I) | p.1≤p.2}-1 := by
  let S := {p : (Fin 2 → I)×(Fin 2 → I) | p.1≤p.2}
  have hs : MeasurableSet S := measurableSet_le measurable_fst measurable_snd
  have hi : Integrable (S.indicator (fun _ => (1:ℝ))) (C.toMeasure.prod C.toMeasure) :=
    (integrable_const _).indicator hs
  have he : (C.toMeasure.prod C.toMeasure).real S=∫ y, C.cdf y ∂C.toMeasure := by
    rw [← integral_indicator_one hs]
    change (∫ p, S.indicator (fun _ => (1:ℝ)) p ∂C.toMeasure.prod C.toMeasure)=_
    rw [integral_prod_symm _ hi]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      simpa only [S,indicator,mem_ofPred_eq,Copula.cdf,mem_Iic,Pi.one_apply] using
        integral_indicator_one (μ := C.toMeasure) (s := Iic y) measurableSet_Iic
  rw [he]
  rfl

end Verification
