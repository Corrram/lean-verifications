import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Verification

/-- The normalized symmetric corner minor, before substituting p=q-1. -/
def plackettMinorPolynomial (q p t : ℝ) : ℝ :=
  (8*q^9*p^1+-16*q^8*p^2)*t^0+
    (-56*q^8*p^2+136*q^7*p^3)*t^1+
    (44*q^8*p^2+16*q^7*p^3+-406*q^6*p^4)*t^2+
    (-160*q^7*p^3+560*q^5*p^5+448*q^6*p^4)*t^3+
    (64*q^7*p^3+-532*q^4*p^6+-728*q^5*p^5+-112*q^6*p^4)*t^4+
    (344*q^3*p^7+784*q^4*p^6+224*q^5*p^5)*t^5+
    (-145*q^2*p^8+-560*q^3*p^7+-280*q^4*p^6)*t^6+
    (36*q^1*p^9+256*q^2*p^8+224*q^3*p^7)*t^7+
    (-68*q^1*p^9+-4*q^0*p^10+-112*q^2*p^8)*t^8+
    (8*q^0*p^10+32*q^1*p^9)*t^9+
    (-4*q^0*p^10)*t^10

theorem plackettMinorPolynomial_identity (q p t : ℝ) :
    q^4*(q^2-4*q*p*t*(1-t))^3-
      (q-2*p*t*(1-t))^2*(q-p*t)^8 = t^2*plackettMinorPolynomial q p t := by
  unfold plackettMinorPolynomial
  ring

theorem plackettMinorPolynomial_zero (q : ℝ) :
    plackettMinorPolynomial q (q-1) 0 = 8*q^8*(q-1)*(2-q) := by
  unfold plackettMinorPolynomial
  ring

end Verification
