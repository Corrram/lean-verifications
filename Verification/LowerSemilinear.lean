import Copula.Rank.ConditionalDerivative
import Verification.Mixture
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Lower semilinear copulas and their xi--footrule bound

The standard lower semilinear representation is C(u,v)=min(u,v) q(max(u,v)),
where q(t)/t is nonincreasing for positive t. The chosen value q(0) does not
change the copula. This condition is the usual diagonal constraint delta(t)/t^2.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval NNReal

namespace Verification

structure LowerSemilinearData (C : Copula 2) where
  q : I → ℝ
  nonneg : ∀ t, 0 ≤ q t
  ratio_antitone : AntitoneOn (fun t : I => q t / (t : ℝ)) (Ioi 0)
  cdf_eq : ∀ u v : I, C.cdf ![u,v] = (min u v : I) * q (max u v)

def IsLowerSemilinear (C : Copula 2) : Prop := Nonempty (LowerSemilinearData C)

namespace LowerSemilinearData

variable {C : Copula 2} (D : LowerSemilinearData C)

theorem cdf_of_le (u v : I) (h : u ≤ v) : C.cdf ![u,v] = (u : ℝ) * D.q v := by
  rw [D.cdf_eq, min_eq_left h, max_eq_right h]

theorem cdf_of_ge (u v : I) (h : v ≤ u) : C.cdf ![u,v] = (v : ℝ) * D.q u := by
  rw [D.cdf_eq, min_eq_right h, max_eq_left h]

theorem ratio_cross (u v : I) (hu : 0 < u) (huv : u ≤ v) :
    (u : ℝ) * D.q v ≤ (v : ℝ) * D.q u := by
  have hh := D.ratio_antitone hu (hu.trans_le huv) huv
  have h := (div_le_div_iff₀ (show (0 : ℝ) < v from hu.trans_le huv) hu).mp hh
  nlinarith only [h]

/-- Every section has Lipschitz constant q(v), even when the LSL copula is not SI. -/
theorem section_diff_le (u w v : I) (huw : u ≤ w) :
    C.cdf ![w,v] - C.cdf ![u,v] ≤ ((w : ℝ)-u) * D.q v := by
  by_cases hv0 : v = 0
  · subst v
    rw [C.cdf_eq_zero_of_coord_eq_zero _ 1 rfl,
      C.cdf_eq_zero_of_coord_eq_zero _ 1 rfl]
    simpa only [sub_self] using mul_nonneg
      (sub_nonneg.mpr (show (u : ℝ) ≤ w from huw)) (D.nonneg 0)
  have hv : 0 < v := lt_of_le_of_ne v.property.1 (Ne.symm hv0)
  by_cases hwv : w ≤ v
  · rw [D.cdf_of_le w v hwv, D.cdf_of_le u v (huw.trans hwv)]
    ring_nf
    exact le_rfl
  have hvw : v ≤ w := le_of_not_ge hwv
  by_cases huv : u ≤ v
  · rw [D.cdf_of_ge w v hvw, D.cdf_of_le u v huv]
    nlinarith only [D.ratio_cross v w hv hvw]
  have hvu : v ≤ u := le_of_not_ge huv
  have hu : (0 : ℝ) < u := hv.trans_le hvu
  rw [D.cdf_of_ge w v hvw, D.cdf_of_ge u v hvu]
  have h₁ := D.ratio_cross u w hu huw
  have h₂ := D.ratio_cross v u hv hvu
  have h₃ := mul_le_mul_of_nonneg_left h₁ v.property.1
  have h₄ := mul_nonneg (sub_nonneg.mpr (show (u : ℝ) ≤ w from huw))
    (sub_nonneg.mpr h₂)
  nlinarith only [h₃, h₄, hu]

theorem section_lipschitz (v : I) :
    LipschitzWith ⟨D.q v, D.nonneg v⟩ (fun u : I => C.cdf ![u,v]) := by
  apply LipschitzWith.of_dist_le_mul
  intro u w
  wlog huw : u ≤ w generalizing u w
  · simpa only [dist_comm] using this w u (le_of_not_ge huw)
  have hm : C.cdf ![u,v] ≤ C.cdf ![w,v] := by
    apply C.monotone_cdf
    intro i
    fin_cases i
    · exact huw
    · exact le_rfl
  rw [Real.dist_eq, Subtype.dist_eq, Real.dist_eq,
    abs_of_nonpos (sub_nonpos.mpr hm), abs_of_nonpos (sub_nonpos.mpr (show (u : ℝ) ≤ w from huw))]
  have h := D.section_diff_le u w v huw
  change -(C.cdf ![u,v] - C.cdf ![w,v]) ≤ D.q v * -((u : ℝ)-w)
  nlinarith only [h]

theorem conditionalCDF_le (v : I) :
    ∀ᵐ u : I, C.conditionalCDF u v ≤ D.q v := by
  have hl : LipschitzWith ⟨D.q v, D.nonneg v⟩ (Copula.cdfSection C v) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h₁ := (D.section_lipschitz v).dist_le_mul
      (projIcc 0 1 zero_le_one x) (projIcc 0 1 zero_le_one y)
    have h₂ : dist (projIcc 0 1 zero_le_one x) (projIcc 0 1 zero_le_one y) ≤ dist x y := by
      simpa only [NNReal.coe_one, one_mul] using
        (LipschitzWith.projIcc zero_le_one).dist_le_mul x y
    exact h₁.trans (mul_le_mul_of_nonneg_left h₂ (D.nonneg v))
  filter_upwards [C.conditionalCDF_eq_deriv v] with u hu
  rw [hu]
  have hn : ‖deriv (Copula.cdfSection C v) (u : ℝ)‖ ≤ D.q v :=
    norm_deriv_le_of_lipschitz hl
  rw [Real.norm_eq_abs] at hn
  exact (abs_le.mp hn).2

include D in
theorem square_integral_le (v : I) :
    (∫ u : I, C.conditionalCDF u v ^ 2) ≤ C.cdf ![v,v] := by
  rw [D.cdf_of_le v v le_rfl]
  calc
    _ ≤ ∫ u : I, D.q v * C.conditionalCDF u v := by
      apply integral_mono_ae (C.integrable_conditionalCDF_sq v)
        ((C.integrable_conditionalCDF v).const_mul _)
      filter_upwards [D.conditionalCDF_le v] with u hu
      nlinarith [C.conditionalCDF_nonneg u v]
    _ = (v : ℝ) * D.q v := by
      rw [integral_const_mul, C.integral_conditionalCDF, mul_comm]

include D in
/-- The LSL inequality follows from its section bound, without an SI hypothesis. -/
theorem xi_le_footrule : C.chatterjeeXi ≤ C.spearmanFootrule := by
  have h := integral_mono C.integrable_integral_conditionalCDF_sq
    (Copula.integrable_continuous_unit volume (by fun_prop : Continuous (fun v : I => C.cdf ![v,v])))
    (fun v => D.square_integral_le v)
  unfold Copula.chatterjeeXi Copula.spearmanFootrule
  linarith

end LowerSemilinearData
end Verification
