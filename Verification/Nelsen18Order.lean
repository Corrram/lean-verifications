import Verification.Nelsen18
import Copula.Order.Orthant
import Mathlib.Analysis.MeanInequalitiesPow

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

theorem n18Inv_power {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (u : I) :
    n18Inv η u = (n18Inv θ u)^(η/θ) := by
  unfold n18Inv
  split_ifs with hu
  · rw [Real.zero_rpow (div_pos hη hθ).ne']
  · rw [← Real.exp_mul]
    congr 1
    field_simp

theorem n18Psi_power {θ η t : ℝ} (hθ : 0 < θ) (hη : 0 < η) (ht : 0 ≤ t) :
    n18Psi η (t^(η/θ)) = n18Psi θ t := by
  have hr : 0 < η/θ := div_pos hη hθ
  have he : (Real.exp (-θ))^(η/θ) = Real.exp (-η) := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  by_cases hz : t = 0
  · subst t
    simp [n18Psi,n18Core,Real.zero_rpow hr.ne',min_eq_left (Real.exp_pos _).le]
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
  by_cases hb : t ≤ Real.exp (-θ)
  · have hb' : t^(η/θ) ≤ Real.exp (-η) := by
      rw [← he]
      exact Real.rpow_le_rpow ht hb hr.le
    rw [n18Psi,n18Psi,min_eq_left hb,min_eq_left hb']
    unfold n18Core
    rw [Real.log_rpow htpos]
    congr 1
    field_simp
  · have hb' : Real.exp (-θ) ≤ t := (lt_of_not_ge hb).le
    have hh : Real.exp (-η) ≤ t^(η/θ) := by
      rw [← he]
      exact Real.rpow_le_rpow (Real.exp_pos _).le hb' hr.le
    rw [n18Psi,n18Psi,min_eq_right hb',min_eq_right hh,n18Core_cutoff hθ.ne',n18Core_cutoff hη.ne']

theorem nelsen18_lowerOrthant_monotone {θ η : ℝ} (hθ : 2 ≤ θ) (hθη : θ ≤ η) :
    (nelsen18 θ hθ).LowerOrthantLE (nelsen18 η (hθ.trans hθη)) := by
  have hp : 0 < θ := by linarith
  have hq : 0 < η := hp.trans_le hθη
  have hr : 1 ≤ η/θ := (one_le_div hp).mpr hθη
  intro x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx,nelsen18_cdf,nelsen18_cdf]
  split_ifs with hz
  · exact le_rfl
  · have hh := Real.add_rpow_le_rpow_add (n18Inv_nonneg θ (x 0)) (n18Inv_nonneg θ (x 1)) hr
    rw [← n18Inv_power hp hq,← n18Inv_power hp hq] at hh
    have hn := add_nonneg (n18Inv_nonneg η (x 0)) (n18Inv_nonneg η (x 1))
    have hm := (n18Generator η (hθ.trans hθη)).antitone hn (hn.trans hh) hh
    change n18Psi η ((n18Inv θ (x 0)+n18Inv θ (x 1))^(η/θ)) ≤ _ at hm
    rw [n18Psi_power hp hq (add_nonneg (n18Inv_nonneg θ (x 0)) (n18Inv_nonneg θ (x 1)))] at hm
    exact hm

end Verification
