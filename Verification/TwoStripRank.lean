import Verification.TwoStrip
import Verification.TentArea
import Copula.Rank.Concordance
import Copula.Rank.Symmetry

/-! # Rho and tau of arbitrary two-strip displacements -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

@[fun_prop] theorem continuous_medianWedge : Continuous medianWedge := by
  unfold medianWedge
  fun_prop

theorem integral_medianWedge : (∫ u : I, medianWedge u) = 1 / 4 := by
  have he : medianWedge = fun u : I => medianTent 1 u := by
    funext u
    by_cases hu : (u : ℝ) ≤ 1 / 2
    · simp only [medianWedge, medianTent, abs_of_nonpos (by linarith : (u : ℝ) - 1 / 2 ≤ 0)]
      rw [min_eq_left (by linarith), max_eq_right (by linarith [u.property.1])]
      ring
    · simp only [medianWedge, medianTent, abs_of_nonneg (by linarith : 0 ≤ (u : ℝ) - 1 / 2)]
      rw [min_eq_right (by linarith), max_eq_right (by linarith [u.property.2])]
      ring
  rw [he, integral_medianTent (by norm_num) (by norm_num)]
  norm_num

theorem rho_twoStrip (g : StripDisplacement) :
    (twoStrip g).spearmanRho = 3 * (∫ v : I, g v) := by
  rw [Copula.spearmanRho_eq_integral_cdf]
  have he : (twoStrip g).cdf = fun x : Fin 2 → I =>
      (x 0 : ℝ) * x 1 + medianWedge (x 0) * g (x 1) := by
    funext x
    have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
    conv_lhs => rw [hx, cdf_twoStrip]
  rw [he, integral_add, Copula.integral_independence_mul,
    Copula.integral_independence_mul, Copula.integral_unit_id, integral_medianWedge]
  · ring
  · exact Copula.integrable_continuous_cube _ (by fun_prop)
  · exact Copula.integrable_continuous_cube _
      ((continuous_medianWedge.comp (continuous_apply 0)).mul
        (g.continuous.comp (continuous_apply 1)))

theorem twoStrip_mix_reflect_first (g : StripDisplacement) :
    (twoStrip g).mix ((twoStrip g).reflect {0}) Copula.unitHalf = Copula.independence 2 := by
  apply Copula.ext_cdf_two
  intro u v
  rw [Copula.cdf_mix, Copula.cdf_reflect_first, cdf_twoStrip, cdf_twoStrip]
  simp only [Copula.cdf_independence, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, medianWedge, unitInterval.coe_symm_eq, sub_sub_cancel]
  rw [min_comm (1 - (u : ℝ)) (u : ℝ)]
  change (1 / 2 : ℝ) * _ + (1 - 1 / 2) * _ = _
  ring

theorem concordanceQ_reflect_first_self (C : Copula 2) :
    C.concordanceQ (C.reflect {0}) = 0 := by
  have h := Copula.concordanceQ_comm C (C.reflect {0})
  rw [Copula.concordanceQ, Copula.concordanceQ,
    Copula.integral_reflect _ _ _ C.continuous_cdf.measurable] at h
  have he : (C.reflect {0}).cdf = fun x : Fin 2 → I =>
      (x 1 : ℝ) - C.cdf (Copula.reflectPoint {0} x) := by
    funext x
    have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
    conv_lhs => rw [hx, Copula.cdf_reflect_first]
    congr 1
    congr 1
    ext i
    fin_cases i <;> simp [Copula.reflectPoint]
  rw [he, integral_sub, Copula.integral_coe_eval] at h
  · rw [Copula.concordanceQ, Copula.integral_reflect _ _ _ C.continuous_cdf.measurable]
    linarith
  · exact Copula.integrable_continuous_cube _ (by fun_prop)
  · exact Copula.integrable_continuous_cube _
      (C.continuous_cdf.comp (by
        apply continuous_pi
        intro i
        by_cases hi : i ∈ ({0} : Finset (Fin 2))
        · simpa only [Copula.reflectPoint, ite_eq_left hi, Function.comp_def] using
            unitInterval.continuous_symm.comp (continuous_apply i)
        · simpa only [Copula.reflectPoint, ite_eq_right hi] using (continuous_apply i)))

theorem tau_twoStrip (g : StripDisplacement) :
    (twoStrip g).kendallTau = 2 * (∫ v : I, g v) := by
  have h := Copula.concordanceQ_mix_right (twoStrip g) (twoStrip g)
    ((twoStrip g).reflect {0}) Copula.unitHalf
  rw [twoStrip_mix_reflect_first, Copula.concordanceQ_independence,
    Copula.concordanceQ_self, concordanceQ_reflect_first_self, rho_twoStrip] at h
  change 3 * (∫ v : I, g v) / 3 = (1 / 2 : ℝ) * (twoStrip g).kendallTau +
    (1 - 1 / 2) * 0 at h
  linarith

end Verification
