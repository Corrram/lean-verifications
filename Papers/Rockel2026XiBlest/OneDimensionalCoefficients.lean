import Papers.Rockel2026XiBlest.NormalizationSubstitution

/-! # The one-dimensional coefficient integrals in Lemma 4.1 -/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.Rockel2026XiBlest

noncomputable def sectionSquare (b q : ℝ) : ℝ :=
  1-quadraticUpper b q+b^2*(quadraticF q (quadraticUpper b q)-quadraticF q (quadraticLower q))
noncomputable def sectionWeighted (b q : ℝ) : ℝ :=
  (1-(quadraticUpper b q)^3)/3+b*(quadraticS q (quadraticUpper b q)-quadraticS q (quadraticLower q))

@[fun_prop] theorem continuous_sectionSquare (b : ℝ) : Continuous (sectionSquare b) := by
  unfold sectionSquare quadraticUpper quadraticLower quadraticF
  fun_prop
@[fun_prop] theorem continuous_sectionWeighted (b : ℝ) : Continuous (sectionWeighted b) := by
  unfold sectionWeighted quadraticUpper quadraticLower quadraticS
  fun_prop

/-- Equations (23)-(24), with the derivative of the actual normalization map. -/
theorem one_dimensional_coefficients (b : ℝ) (hb : 0 < b) :
    (extremalCopula b hb.le).chatterjeeXi=
      6*(∫ q in (-1/b)..1,sectionSquare b q*(-deriv (normalizationMean b) q))-2 ∧
    blestNu (extremalCopula b hb.le)=
      12*(∫ q in (-1/b)..1,sectionWeighted b q*(-deriv (normalizationMean b) q))-2 := by
  constructor
  · rw [← normalization_substitution b hb (sectionSquare b) (continuous_sectionSquare b)]
    unfold Copula.chatterjeeXi
    congr 2
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v => by
      calc
        _ = ∫ u : I,unitClamp (b*((1-(u : ℝ))^2-extremalQ b hb v))^2 :=
          integral_congr_ae ((extremal_conditionalCDF b hb v).fun_comp (fun x : ℝ => x^2))
        _ = _ := (section_formulas b (extremalQ b hb v) hb (extremalQ_mem b hb v)).2.1
  · rw [blest_conditional_formula,← normalization_substitution b hb (sectionWeighted b) (continuous_sectionWeighted b)]
    congr 2
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v => by
      calc
        _ = ∫ u : I,(1-(u : ℝ))^2*unitClamp (b*((1-(u : ℝ))^2-extremalQ b hb v)) :=
          integral_congr_ae ((extremal_conditionalCDF b hb v).mono fun u hu => by
            dsimp only at hu ⊢; rw [hu])
        _ = _ := (section_formulas b (extremalQ b hb v) hb (extremalQ_mem b hb v)).2.2

/-- Correct expansion of the lower-clamped square moment. -/
theorem lower_square_polynomial (r : ℝ) :
    quadraticF (r^2) 1-quadraticF (r^2) r=1/5-2*r^2/3+r^4-8*r^5/15 := by
  unfold quadraticF
  ring

/-- The preprint's displayed G_iv polynomial omits part of F(r;r^2). -/
theorem printed_lower_square_polynomial_false :
    quadraticF ((1/2 : ℝ)^2) 1-quadraticF ((1/2 : ℝ)^2) (1/2) ≠
      1/5-2*(1/2 : ℝ)^2/3+(1/2 : ℝ)^4-(1/2 : ℝ)^5/5 := by
  norm_num [quadraticF]

end Papers.Rockel2026XiBlest
