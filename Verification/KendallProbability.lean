import Copula.Rank.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! # Rank coefficients as probabilities of coordinatewise comparison

Fubini identifies cross-CDF integrals with probabilities that one independent
copula observation is below another coordinatewise. This gives Kendall tau
using two copies of the copula and Spearman rho using an independent copula.
-/

open ProbabilityTheory MeasureTheory Set
open scoped unitInterval

namespace Verification

theorem integral_cdf_probability (C D : Copula 2) :
    (∫ y, C.cdf y ∂D.toMeasure)=(C.toMeasure.prod D.toMeasure).real
      {p : (Fin 2 → I)×(Fin 2 → I) | p.1≤p.2} := by
  let S := {p : (Fin 2 → I)×(Fin 2 → I) | p.1≤p.2}
  have hs : MeasurableSet S := measurableSet_le measurable_fst measurable_snd
  have hi : Integrable (S.indicator (fun _ => (1:ℝ))) (C.toMeasure.prod D.toMeasure) :=
    (integrable_const _).indicator hs
  symm
  rw [← integral_indicator_one hs]
  change (∫ p, S.indicator (fun _ => (1:ℝ)) p ∂C.toMeasure.prod D.toMeasure)=_
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simpa only [S,indicator,mem_ofPred_eq,Copula.cdf,mem_Iic,Pi.one_apply] using
      integral_indicator_one (μ := C.toMeasure) (s := Iic y) measurableSet_Iic

theorem spearmanRho_probability (C : Copula 2) :
    C.spearmanRho=12*((Copula.independence 2).toMeasure.prod C.toMeasure).real
      {p : (Fin 2 → I)×(Fin 2 → I) | p.1≤p.2}-3 := by
  have he := integral_cdf_probability (Copula.independence 2) C
  simp only [Copula.cdf_independence,Fin.prod_univ_two] at he
  rw [Copula.spearmanRho,he]

theorem kendallTau_probability (C : Copula 2) :
    C.kendallTau=4*(C.toMeasure.prod C.toMeasure).real
      {p : (Fin 2 → I)×(Fin 2 → I) | p.1≤p.2}-1 := by
  rw [Copula.kendallTau,integral_cdf_probability]

end Verification
