import Verification.TP2Integration
import Copula.Rectangle
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal

namespace Verification

theorem density_rectangle_integral (C : Copula 2) (f : (Fin 2 → I) → ℝ)
    (hf : Measurable f)
    (hd : C.toMeasure=(volume : Measure (Fin 2 → I)).withDensity (fun x => ENNReal.ofReal (f x)))
    (S T : Set I) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    C.toMeasure {x | x 0 ∈ S ∧ x 1 ∈ T} = ∫⁻ a in S, ∫⁻ b in T, ENNReal.ofReal (f ![a,b]) := by
  let g : I × I → ℝ≥0∞ := fun p => ENNReal.ofReal (f ![p.1,p.2])
  have hg : Measurable g := hf.ennreal_ofReal.comp (by fun_prop)
  have he : (fun x : Fin 2 → I => g (MeasurableEquiv.finTwoArrow x)) = fun x => ENNReal.ofReal (f x) := by
    funext x
    change ENNReal.ofReal (f ![x 0,x 1]) = ENNReal.ofReal (f x)
    apply congrArg (fun z => ENNReal.ofReal (f z))
    ext i
    fin_cases i <;> rfl
  have hs : MeasurableSet {x : Fin 2 → I | x 0 ∈ S ∧ x 1 ∈ T} :=
    (hS.preimage (measurable_pi_apply 0)).inter (hT.preimage (measurable_pi_apply 1))
  rw [hd,withDensity_apply _ hs]
  rw [← he]
  change (∫⁻ x in MeasurableEquiv.finTwoArrow ⁻¹' (S ×ˢ T), g (MeasurableEquiv.finTwoArrow x)) = _
  rw [(volume_preserving_finTwoArrow I).setLIntegral_comp_preimage (hS.prod hT) hg]
  exact setLIntegral_prod g hg.aemeasurable

theorem measureReal_coordinate_rectangle (C : Copula 2) (a b c d : I) (hab : a ≤ b) (hcd : c ≤ d) :
    C.toMeasure.real {x | x 0 ∈ Ioc a b ∧ x 1 ∈ Ioc c d} =
      C.cdf ![b,d]-C.cdf ![a,d]-C.cdf ![b,c]+C.cdf ![a,c] := by
  have he : {x : Fin 2 → I | x 0 ∈ Ioc a b ∧ x 1 ∈ Ioc c d} =
      Set.pi univ (fun i => Ioc (![a,c] i) (![b,d] i)) := by
    ext x
    simp [Fin.forall_fin_two]
  rw [he,C.measureReal_rectangle_two _ _ (by intro i; fin_cases i <;> assumption)]
  rfl

end Verification
