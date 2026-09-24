import Verification.PlackettConditional
import Verification.PlackettContinuity

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

/-- The defining cross-product odds equation holds even at independence and on the boundary. -/
theorem plackett_odds_equation {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    θ*((u:ℝ)-(plackett θ hθ).cdf ![u,v])*((v:ℝ)-(plackett θ hθ).cdf ![u,v]) =
      (plackett θ hθ).cdf ![u,v]*(1-(u:ℝ)-(v:ℝ)+(plackett θ hθ).cdf ![u,v]) := by
  by_cases hne : θ=1
  · subst θ; rw [plackett_one]
    simp only [cdf_independence,Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
    ring
  let c := (plackett θ hθ).cdf ![u,v]
  have he : c*(2*(θ-1)) = plackettA θ u v-Real.sqrt (plackettD θ u v) :=
    (eq_div_iff (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hne))).mp (plackett_cdf hθ hne u v)
  have hs := Real.sq_sqrt (plackettD_pos hθ u.property v.property).le
  have he' : Real.sqrt (plackettD θ u v) = plackettA θ u v-c*(2*(θ-1)) := by linarith
  rw [he'] at hs
  unfold plackettD at hs
  have hp : (θ-1)*((θ-1)*c^2-plackettA θ u v*c+θ*(u:ℝ)*(v:ℝ)) = 0 := by nlinarith [hs]
  have hq := (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hne)
  dsimp [plackettA] at hq
  change θ*((u:ℝ)-c)*((v:ℝ)-c) = c*(1-(u:ℝ)-(v:ℝ)+c)
  nlinarith [hq]

theorem plackett_lowerOrthant_monotone {θ η : ℝ} (hθ : 0 < θ) (hθη : θ ≤ η) :
    (plackett θ hθ).LowerOrthantLE (plackett η (hθ.trans_le hθη)) := by
  intro x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx]
  let u := x 0
  let v := x 1
  let c := (plackett θ hθ).cdf ![u,v]
  let d := (plackett η (hθ.trans_le hθη)).cdf ![u,v]
  have hc0 : 0 ≤ c := (plackett θ hθ).cdf_nonneg _
  have hd0 : 0 ≤ d := (plackett η (hθ.trans_le hθη)).cdf_nonneg _
  have hcu : c ≤ (u:ℝ) := (plackett θ hθ).cdf_le_coord ![u,v] 0
  have hcv : c ≤ (v:ℝ) := (plackett θ hθ).cdf_le_coord ![u,v] 1
  have hdu : d ≤ (u:ℝ) := (plackett η (hθ.trans_le hθη)).cdf_le_coord ![u,v] 0
  have hdv : d ≤ (v:ℝ) := (plackett η (hθ.trans_le hθη)).cdf_le_coord ![u,v] 1
  have hcl : (u:ℝ)+(v:ℝ)-1 ≤ c := by
    have hh := (plackett θ hθ).sum_sub_dim_add_one_le_cdf ![u,v]
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Nat.cast_ofNat] at hh
    change (u:ℝ)+(v:ℝ)-2+1 ≤ c at hh
    linarith
  have hX : 0 ≤ (u:ℝ)+(v:ℝ)-c-d := by linarith
  have hY : 0 ≤ 1-(u:ℝ)-(v:ℝ)+c+d := by linarith
  have hK : 0 < η*((u:ℝ)+(v:ℝ)-c-d)+(1-(u:ℝ)-(v:ℝ)+c+d) := by
    have hp : 0 < η := hθ.trans_le hθη
    by_cases hz : (u:ℝ)+(v:ℝ)-c-d = 0
    · rw [hz,mul_zero,zero_add]; linarith
    · have hh := mul_pos hp (lt_of_le_of_ne hX (Ne.symm hz))
      linarith
  have hc := plackett_odds_equation hθ u v
  have hd := plackett_odds_equation (hθ.trans_le hθη) u v
  change θ*((u:ℝ)-c)*((v:ℝ)-c) = c*(1-(u:ℝ)-(v:ℝ)+c) at hc
  change η*((u:ℝ)-d)*((v:ℝ)-d) = d*(1-(u:ℝ)-(v:ℝ)+d) at hd
  have hn := mul_nonneg (sub_nonneg.mpr hθη)
    (mul_nonneg (sub_nonneg.mpr hcu) (sub_nonneg.mpr hcv))
  have he : (d-c)*(η*((u:ℝ)+(v:ℝ)-c-d)+(1-(u:ℝ)-(v:ℝ)+c+d)) =
      (η-θ)*((u:ℝ)-c)*((v:ℝ)-c) := by nlinarith [hc,hd]
  have hp : 0 ≤ d-c := (mul_nonneg_iff_of_pos_right hK).mp (by rw [he]; nlinarith [hn])
  change c ≤ d
  linarith

theorem plackett_schur_above_one {θ η : ℝ} (hθ : 0 < θ) (h1 : 1 ≤ θ) (hθη : θ ≤ η) :
    (plackett θ hθ).SchurBothLE (plackett η (hθ.trans_le hθη)) := by
  have hc := plackett_isCI hθ h1
  have hd := plackett_isCI (hθ.trans_le hθη) (h1.trans hθη)
  have ho := plackett_lowerOrthant_monotone hθ hθη
  constructor
  · exact (schurLE_iff_lowerOrthantLE_isSI _ _ hc.1 hd.1).mpr ho
  · rw [plackett_transpose,plackett_transpose]
    exact (schurLE_iff_lowerOrthantLE_isSI _ _ hc.1 hd.1).mpr ho

theorem plackett_schur_below_one {θ η : ℝ} (hθ : 0 < θ) (hη : η ≤ 1) (hθη : θ ≤ η) :
    (plackett η (hθ.trans_le hθη)).SchurBothLE (plackett θ hθ) := by
  have hc := plackett_isCD hθ (hθη.trans hη)
  have hd := plackett_isCD (hθ.trans_le hθη) hη
  have ho := plackett_lowerOrthant_monotone hθ hθη
  constructor
  · exact (schurLE_iff_lowerOrthantLE_isSD _ _ hd.1 hc.1).mpr ho
  · rw [plackett_transpose,plackett_transpose]
    exact (schurLE_iff_lowerOrthantLE_isSD _ _ hd.1 hc.1).mpr ho

theorem plackett_lowerOrthant_iff {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) :
    (plackett θ hθ).LowerOrthantLE (plackett η hη) ↔ θ ≤ η := by
  constructor
  · intro h
    have hh := h ![unitHalf,unitHalf]
    rw [plackett_midpoint hθ,plackett_midpoint hη] at hh
    have hnθ : 0 < 2*(Real.sqrt θ+1) := by positivity
    have hnη : 0 < 2*(Real.sqrt η+1) := by positivity
    have hi := (div_le_div_iff₀ hnθ hnη).mp hh
    have hs : Real.sqrt θ ≤ Real.sqrt η := by nlinarith
    nlinarith [Real.sq_sqrt hθ.le,Real.sq_sqrt hη.le,Real.sqrt_nonneg θ,Real.sqrt_nonneg η]
  · exact plackett_lowerOrthant_monotone hθ

end Verification
