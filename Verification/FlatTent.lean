import Verification.TwoStripRatio
import Verification.RampIntegrals

/-! # Flat-topped tents and their exact first two moments -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

noncomputable def flatTent (a : I) (v : I) : ℝ := min (a : ℝ) (medianWedge v)

noncomputable def flatTentDisplacement (a : I) : StripDisplacement where
  toFun := flatTent a
  zero := by simp [flatTent,medianWedge,a.property.1]
  one := by simp [flatTent,medianWedge,a.property.1]
  lipschitz := by
    intro v w
    have h := abs_min_sub_min_le_max (a : ℝ) (medianWedge v) (a : ℝ) (medianWedge w)
    simp only [sub_self,abs_zero,max_eq_right (abs_nonneg (medianWedge v-medianWedge w))] at h
    exact h.trans (medianWedge_lipschitz v w)

theorem flatTent_ramps (a v : I) (ha : (a : ℝ) ≤ 1/2) :
    flatTent a v = (a : ℝ)-ramp a v-ramp a (unitInterval.symm v) := by
  simp only [flatTent,medianWedge,ramp,unitInterval.coe_symm_eq,min_def,max_def]
  split_ifs <;> linarith [a.property.1,v.property.1,v.property.2]

theorem flatTent_ramps_disjoint (a v : I) (ha : (a : ℝ) ≤ 1/2) :
    ramp a v*ramp a (unitInterval.symm v) = 0 := by
  simp only [ramp,unitInterval.coe_symm_eq,max_def]
  split_ifs <;> nlinarith [sq_nonneg ((a : ℝ)-(v : ℝ))]

theorem integral_flatTent (a : I) (ha : (a : ℝ) ≤ 1/2) :
    (∫ v : I, flatTent a v) = (a : ℝ)*(1-(a : ℝ)) := by
  have hi : Integrable (fun v : I => ramp a v) := Copula.integrable_continuous_unit volume (continuous_ramp a)
  have hj : Integrable (fun v : I => ramp a (unitInterval.symm v)) := Copula.integrable_continuous_unit volume ((continuous_ramp a).comp unitInterval.continuous_symm)
  simp_rw [flatTent_ramps a _ ha]
  have h1 := integral_sub ((integrable_const (a : ℝ)).sub hi) hj
  have h2 := integral_sub (integrable_const (a : ℝ)) hi
  dsimp only [Pi.sub_apply] at h1 h2
  rw [h1,h2,integral_unit_reflection,integral_ramp]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  ring

theorem integral_flatTent_sq (a : I) (ha : (a : ℝ) ≤ 1/2) :
    (∫ v : I, flatTent a v^2) = (a : ℝ)^2-4*(a : ℝ)^3/3 := by
  have he (v : I) : flatTent a v^2 =
      (a : ℝ)^2-2*(a : ℝ)*(ramp a v+ramp a (unitInterval.symm v))+
        (ramp a v^2+ramp a (unitInterval.symm v)^2) := by
    rw [flatTent_ramps a v ha]
    nlinarith only [flatTent_ramps_disjoint a v ha]
  have hi : Integrable (fun v : I => ramp a v) := Copula.integrable_continuous_unit volume (continuous_ramp a)
  have hj : Integrable (fun v : I => ramp a (unitInterval.symm v)) := Copula.integrable_continuous_unit volume ((continuous_ramp a).comp unitInterval.continuous_symm)
  have hi2 : Integrable (fun v : I => ramp a v^2) := Copula.integrable_continuous_unit volume ((continuous_ramp a).pow 2)
  have hj2 : Integrable (fun v : I => ramp a (unitInterval.symm v)^2) := Copula.integrable_continuous_unit volume (((continuous_ramp a).comp unitInterval.continuous_symm).pow 2)
  simp_rw [he]
  have h1 := integral_add ((integrable_const ((a : ℝ)^2)).sub ((hi.add hj).const_mul (2*(a : ℝ)))) (hi2.add hj2)
  have h2 := integral_sub (integrable_const ((a : ℝ)^2)) ((hi.add hj).const_mul (2*(a : ℝ)))
  have h3 := integral_add hi hj
  have h4 := integral_add hi2 hj2
  dsimp only [Pi.sub_apply,Pi.add_apply] at h1 h2 h3 h4
  rw [h1,h2,integral_const_mul,h3,h4,integral_unit_reflection (ramp a),integral_unit_reflection (fun v => ramp a v^2),
    integral_ramp,integral_ramp_sq]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  ring

theorem xi_flatTent (a : I) (ha : (a : ℝ) ≤ 1/2) :
    (twoStrip (flatTentDisplacement a)).chatterjeeXi = 2*(a : ℝ)^2*(3-4*(a : ℝ)) := by
  rw [xi_twoStrip]
  change 6*(∫ v : I, flatTent a v^2) = _
  rw [integral_flatTent_sq a ha]
  ring

theorem correlationRatio_flatTent (a : I) (ha : (a : ℝ) ≤ 1/2) :
    correlationRatio (twoStrip (flatTentDisplacement a)) = 12*(a : ℝ)^2*(1-(a : ℝ))^2 := by
  rw [correlationRatio_twoStrip]
  change 12*(∫ v : I, flatTent a v)^2 = _
  rw [integral_flatTent a ha]
  ring

end Verification
