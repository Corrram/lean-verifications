import Papers.Rockel2026XiBlest.NormalizationContinuity
import Verification.QuadraticSectionIntegrals

/-! # The section formulas in Lemma 4.1 -/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.Rockel2026XiBlest

private theorem reflected_section (b q : ℝ) (m k : ℕ) :
    (∫ t : I,(1-(t : ℝ))^m*unitClamp (b*((1-(t : ℝ))^2-q))^k)=
      ∫ x in (0 : ℝ)..1,x^m*unitClamp (b*(x^2-q))^k := by
  calc
    _ = ∫ x : I,(x : ℝ)^m*unitClamp (b*((x : ℝ)^2-q))^k := by
      simpa only [unitInterval.coe_symm_eq] using
        integral_unit_reflection (fun x : I => (x : ℝ)^m*unitClamp (b*((x : ℝ)^2-q))^k)
    _ = _ := Copula.integral_unitInterval (fun x => x^m*unitClamp (b*(x^2-q))^k)

/-- Equations (20)-(22); s is X_a and r is X_s, so the plateau length is 1-s. -/
theorem section_formulas (b q : ℝ) (hb : 0 < b) (hq : q ∈ Icc (-1/b) 1) :
    let r := quadraticLower q
    let s := quadraticUpper b q
    (∫ t : I,unitClamp (b*((1-(t : ℝ))^2-q)))=1-s+b*(quadraticT q s-quadraticT q r) ∧
    (∫ t : I,unitClamp (b*((1-(t : ℝ))^2-q))^2)=1-s+b^2*(quadraticF q s-quadraticF q r) ∧
    (∫ t : I,(1-(t : ℝ))^2*unitClamp (b*((1-(t : ℝ))^2-q)))=
      (1-s^3)/3+b*(quadraticS q s-quadraticS q r) := by
  dsimp only
  have h1 := (reflected_section b q 0 1).trans (quadratic_section_moment b q hb hq 0 1 (by norm_num))
  have h2 := (reflected_section b q 0 2).trans (quadratic_section_moment b q hb hq 0 2 (by norm_num))
  have h3 := (reflected_section b q 2 1).trans (quadratic_section_moment b q hb hq 2 1 (by norm_num))
  simp only [pow_zero,pow_one,one_mul] at h1 h2 h3
  rw [(integral_quadratic_polynomials q _ _).1,intervalIntegral.integral_const] at h1
  rw [(integral_quadratic_polynomials q _ _).2.1,intervalIntegral.integral_const] at h2
  have hp : (∫ x in quadraticUpper b q..1,x^2)=(1-(quadraticUpper b q)^3)/3 := by
    have h := (integral_quadratic_polynomials 0 (quadraticUpper b q) 1).1
    simp only [sub_zero,quadraticT,zero_mul,one_pow] at h
    linarith
  rw [(integral_quadratic_polynomials q _ _).2.2,hp] at h3
  simp only [smul_eq_mul,mul_one] at h1 h2 h3
  exact ⟨by linarith,by linarith,by linarith⟩

end Papers.Rockel2026XiBlest
