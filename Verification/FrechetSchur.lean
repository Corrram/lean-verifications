import Copula.Families.Frechet
import Copula.Order.SchurMixture
import Copula.Order.SymmetricSchur
import Copula.Symmetry
import Copula.Reflection.Bivariate
import Copula.Rank.Integration
import Verification.XiPredictorReflection

/-! # Schur order in the Fréchet and Mardia families

Reflecting the first coordinate swaps the `M` and `W` weights of a Fréchet copula and
preserves Schur equivalence. Hence every Fréchet copula whose weight pair lies in
`{λ₁(a,b)+λ₂(b,a) : λ₁,λ₂≥0, λ₁+λ₂≤1}` is Schur-below `Frechet(a,b)` (a mixture of two
Schur-equivalent copulas with independence). For Mardia, `t=θ/η∈[0,1]` gives
`λ₁=(t²+t³)/2`, `λ₂=(t²-t³)/2`. This proves Schur monotonicity in `|θ|` on each sign
(Table 5 / Appendix A.4.2, `*` cell), and on the unmixed Fréchet axes.
-/

open MeasureTheory Set ProbabilityTheory Copula
open scoped unitInterval

namespace Verification.FrechetSchur

theorem frechet_cdf_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) (u v : I) :
    (frechet a b ha hb hab).cdf ![u, v] =
      a * min (u : ℝ) v + b * max 0 ((u : ℝ) + v - 1) + (1 - a - b) * ((u : ℝ) * v) := by
  rw [cdf_frechet, cdf_comonotonic_two, cdf_countermonotonic, cdf_independence]
  simp [Fin.prod_univ_two]

theorem frechet_reflect_first (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (frechet a b ha hb hab).reflect {0} = frechet b a hb ha (by linarith) := by
  apply ext_cdf_two
  intro u v
  rw [cdf_reflect_first, frechet_cdf_two, frechet_cdf_two]
  simp only [unitInterval.coe_symm_eq]
  have hu0 := u.2.1; have hu1 := u.2.2; have hv0 := v.2.1; have hv1 := v.2.2
  rcases le_total (1 - (u : ℝ)) v with h1 | h1 <;> rcases le_total (u : ℝ) v with h2 | h2
  all_goals
    simp only [min_def, max_def]
    split_ifs <;> linarith

theorem frechet_isExchangeable (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (frechet a b ha hb hab).IsExchangeable := by
  rw [isExchangeable_iff]
  intro u v
  rw [frechet_cdf_two, frechet_cdf_two, min_comm]
  ring_nf

theorem frechet_swap_schurLE (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (frechet b a hb ha (by linarith)).SchurLE (frechet a b ha hb hab) := by
  rw [← frechet_reflect_first a b ha hb hab]
  exact (schurLE_of_rearrangement _ _ unitInterval.measurePreserving_symm
    (conditionalCDF_reflect_first _)).1

/-- A convex combination of `(a,b)`, `(b,a)` and `(0,0)` is Schur-below `Frechet(a,b)`. -/
theorem frechet_schurLE_of_combo {a b l₁ l₂ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)
    (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (hl : l₁ + l₂ ≤ 1)
    (ha' : 0 ≤ l₁ * a + l₂ * b) (hb' : 0 ≤ l₁ * b + l₂ * a)
    (hab' : (l₁ * a + l₂ * b) + (l₁ * b + l₂ * a) ≤ 1) :
    (frechet (l₁ * a + l₂ * b) (l₁ * b + l₂ * a) ha' hb' hab').SchurLE
      (frechet a b ha hb hab) := by
  set F := frechet a b ha hb hab
  set F' := frechet b a hb ha (by linarith)
  by_cases hs : l₁ + l₂ = 0
  · have h1 : l₁ = 0 := by linarith
    have h2 : l₂ = 0 := by linarith
    have he : frechet (l₁ * a + l₂ * b) (l₁ * b + l₂ * a) ha' hb' hab' = independence 2 := by
      apply ext_cdf_two; intro u v
      rw [frechet_cdf_two, cdf_independence]; simp [h1, h2, Fin.prod_univ_two]
    rw [he]; exact schurLE_independence _
  have hsp : 0 < l₁ + l₂ := lt_of_le_of_ne (add_nonneg hl₁ hl₂) (Ne.symm hs)
  let r : I := ⟨l₁ / (l₁ + l₂), div_nonneg hl₁ hsp.le, (div_le_one hsp).mpr (by linarith)⟩
  let s : I := ⟨l₁ + l₂, hsp.le, hl⟩
  have he : frechet (l₁ * a + l₂ * b) (l₁ * b + l₂ * a) ha' hb' hab' =
      (F.mix F' r).mix (independence 2) s := by
    apply ext_cdf_two; intro u v
    rw [cdf_mix, cdf_mix, frechet_cdf_two, frechet_cdf_two, frechet_cdf_two, cdf_independence]
    simp only [r, s, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  rw [he]
  have hin : (F.mix F' r).SchurLE F :=
    (SchurLE.refl F).mix (frechet_swap_schurLE a b ha hb hab) r
  exact hin.mix (schurLE_independence F) s

theorem mardia_weights (θ : ℝ) (hθ : |θ| ≤ 1) :
    mardia θ hθ = frechet (θ ^ 2 * (1 + θ) / 2) (θ ^ 2 * (1 - θ) / 2)
      (div_nonneg (mul_nonneg (sq_nonneg θ) (by linarith [(abs_le.mp hθ).1])) (by norm_num))
      (div_nonneg (mul_nonneg (sq_nonneg θ) (by linarith [(abs_le.mp hθ).2])) (by norm_num))
      (by have := (abs_le.mp hθ).1; have := (abs_le.mp hθ).2; nlinarith [sq_nonneg θ]) := rfl

/-- Mardia: if `θ=tη` with `t∈[0,1]`, then `C_θ ≤_∂S C_η`. -/
theorem mardia_schurLE_of_ratio {θ η : ℝ} (hθ : |θ| ≤ 1) (hη : |η| ≤ 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hte : θ = t * η) :
    (mardia θ hθ).SchurLE (mardia η hη) := by
  set a := η ^ 2 * (1 + η) / 2
  set b := η ^ 2 * (1 - η) / 2
  have ha : 0 ≤ a := div_nonneg (mul_nonneg (sq_nonneg η) (by linarith [(abs_le.mp hη).1]))
    (by norm_num)
  have hb : 0 ≤ b := div_nonneg (mul_nonneg (sq_nonneg η) (by linarith [(abs_le.mp hη).2]))
    (by norm_num)
  have hab : a + b ≤ 1 := by
    have := (abs_le.mp hη).1; have := (abs_le.mp hη).2; dsimp [a, b]; nlinarith [sq_nonneg η]
  set l₁ := (t ^ 2 + t ^ 3) / 2
  set l₂ := (t ^ 2 - t ^ 3) / 2
  have hl₁ : 0 ≤ l₁ := by positivity
  have ht3 : t ^ 3 ≤ t ^ 2 := by
    have := pow_le_pow_of_le_one ht0 ht1 (show 2 ≤ 3 by norm_num); linarith
  have hl₂ : 0 ≤ l₂ := by dsimp [l₂]; linarith
  have hl : l₁ + l₂ ≤ 1 := by
    have : t ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
    dsimp [l₁, l₂]; linarith
  have e1 : θ ^ 2 * (1 + θ) / 2 = l₁ * a + l₂ * b := by
    rw [hte]; dsimp [l₁, l₂, a, b]; ring
  have e2 : θ ^ 2 * (1 - θ) / 2 = l₁ * b + l₂ * a := by
    rw [hte]; dsimp [l₁, l₂, a, b]; ring
  have hθ1 := (abs_le.mp hθ).1
  have hc := frechet_schurLE_of_combo ha hb hab hl₁ hl₂ hl
    (by rw [← e1]; exact div_nonneg (mul_nonneg (sq_nonneg θ) (by linarith)) (by norm_num))
    (by rw [← e2]; have := (abs_le.mp hθ).2; apply div_nonneg _ (by norm_num);
        exact mul_nonneg (sq_nonneg θ) (by linarith))
    (by rw [← e1, ← e2]; have := (abs_le.mp hθ).1; have := (abs_le.mp hθ).2;
        nlinarith [sq_nonneg θ])
  rw [mardia_weights, mardia_weights]
  convert hc using 2

theorem mardia_isExchangeable (θ : ℝ) (hθ : |θ| ≤ 1) : (mardia θ hθ).IsExchangeable :=
  frechet_isExchangeable _ _ _ _ _

/-- Table 5 (`*` cell): Mardia increases in both-direction Schur order on `θ≥0`. -/
theorem mardia_schur_nonnegative {θ η : ℝ} (hθ : 0 ≤ θ) (hθη : θ ≤ η) (hη : η ≤ 1) :
    (mardia θ (abs_le.mpr ⟨by linarith, by linarith⟩)).SchurBothLE
      (mardia η (abs_le.mpr ⟨by linarith, hη⟩)) := by
  rw [schurBothLE_iff_of_exchangeable (mardia_isExchangeable _ _)
    (mardia_isExchangeable _ _)]
  rcases (hθ.trans hθη).lt_or_eq with hηp | hη0
  · exact mardia_schurLE_of_ratio _ _ (div_nonneg hθ hηp.le) ((div_le_one hηp).mpr hθη)
      (div_mul_cancel₀ θ hηp.ne').symm
  · have hθ0 : θ = 0 := by linarith
    subst hθ0
    exact mardia_schurLE_of_ratio _ _ le_rfl zero_le_one (by ring)

/-- Table 5 (`*` cell): Mardia decreases in both-direction Schur order on `θ≤0`. -/
theorem mardia_schur_nonpositive {θ η : ℝ} (hθ : -1 ≤ θ) (hθη : θ ≤ η) (hη : η ≤ 0) :
    (mardia η (abs_le.mpr ⟨by linarith, by linarith⟩)).SchurBothLE
      (mardia θ (abs_le.mpr ⟨hθ, by linarith⟩)) := by
  rw [schurBothLE_iff_of_exchangeable (mardia_isExchangeable _ _)
    (mardia_isExchangeable _ _)]
  rcases (hθη.trans hη).lt_or_eq with hθn | hθ0
  · exact mardia_schurLE_of_ratio _ _ (div_nonneg_of_nonpos hη hθn.le)
      ((div_le_one_of_neg hθn).mpr hθη) (div_mul_cancel₀ η hθn.ne).symm
  · have hη0 : η = 0 := by linarith
    subst hη0
    exact mardia_schurLE_of_ratio _ _ le_rfl zero_le_one (by ring)

/-- Fréchet: on the axis `b=0`, Schur order increases with the `M` weight. -/
theorem frechet_schur_mono_first {a a' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') (ha' : a' ≤ 1) :
    (frechet a 0 ha le_rfl (by linarith)).SchurBothLE
      (frechet a' 0 (ha.trans haa) le_rfl (by linarith)) := by
  rw [schurBothLE_iff_of_exchangeable (frechet_isExchangeable _ _ _ _ _)
    (frechet_isExchangeable _ _ _ _ _)]
  rcases (ha.trans haa).lt_or_eq with hp | h0
  · have hc := frechet_schurLE_of_combo (a := a') (b := 0) (l₁ := a / a') (l₂ := 0)
      (ha.trans haa) le_rfl (by linarith) (div_nonneg ha hp.le) le_rfl
      (by rw [add_zero]; exact (div_le_one hp).mpr haa)
      (by rw [div_mul_cancel₀ _ hp.ne']; linarith) (by simp)
      (by rw [div_mul_cancel₀ _ hp.ne']; linarith)
    convert hc using 2
    · rw [div_mul_cancel₀ _ hp.ne']; ring
    · ring
  · have : a = 0 := by linarith
    subst this; subst h0; rfl

/-- Fréchet: on the axis `a=0`, Schur order increases with the `W` weight. -/
theorem frechet_schur_mono_second {b b' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b') (hb' : b' ≤ 1) :
    (frechet 0 b le_rfl hb (by linarith)).SchurBothLE
      (frechet 0 b' le_rfl (hb.trans hbb) (by linarith)) := by
  rw [schurBothLE_iff_of_exchangeable (frechet_isExchangeable _ _ _ _ _)
    (frechet_isExchangeable _ _ _ _ _)]
  rcases (hb.trans hbb).lt_or_eq with hp | h0
  · have hc := frechet_schurLE_of_combo (a := 0) (b := b') (l₁ := b / b') (l₂ := 0)
      le_rfl (hb.trans hbb) (by linarith) (div_nonneg hb hp.le) le_rfl
      (by rw [add_zero]; exact (div_le_one hp).mpr hbb)
      (by simp) (by rw [div_mul_cancel₀ _ hp.ne']; linarith)
      (by rw [div_mul_cancel₀ _ hp.ne']; linarith)
    convert hc using 2
    · ring
    · rw [div_mul_cancel₀ _ hp.ne']; ring
  · have : b = 0 := by linarith
    subst this; subst h0; rfl

end Verification.FrechetSchur
