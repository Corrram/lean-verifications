import Copula.Families.Clayton.CDF
import Copula.Families.Clayton.Negative
import Copula.Families.Clayton.Limits
import Copula.Dependence.Clayton
import Copula.Dependence.ClaytonNegative
import Copula.Dependence.ConditionalMonotonicity
import Copula.Reflection.Bivariate
import Verification.SchurOrthantEquivalence
import Verification.ConcaveFourPoint
import Copula.Order.SymmetricSchur
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! # Lower-orthant and Schur parameter order of the signed Clayton family

The signed family is the positive Clayton copula for `θ>0`, independence at `θ=0`, and the
truncated negative branch for `-1≤θ<0`. Within the positive branch the comparison reduces to
superadditivity of `x ↦ (1+x)^r-1` (`r≥1`), within the negative branch to the concave
four-point inequality for `x ↦ x^r` (`r≤1`), and across zero to PQD/NQD. CI and CD transfer
the orthant order to the Schur order.
-/

open Set Filter Real ProbabilityTheory Copula
open scoped unitInterval Topology

namespace Verification

/-- The signed Clayton family (junk value `Π` below `-1`). -/
noncomputable def claytonSigned (θ : ℝ) : Copula 2 :=
  if h : 0 < θ then clayton 2 θ h
  else if h' : θ < 0 ∧ -1 ≤ θ then claytonNegative θ h'.2 h'.1
  else independence 2

theorem claytonSigned_pos {θ : ℝ} (h : 0 < θ) : claytonSigned θ = clayton 2 θ h := by
  simp [claytonSigned, h]

theorem claytonSigned_zero : claytonSigned 0 = independence 2 := by
  simp [claytonSigned]

theorem claytonSigned_neg {θ : ℝ} (hθ : -1 ≤ θ) (hn : θ < 0) :
    claytonSigned θ = claytonNegative θ hθ hn := by
  simp [claytonSigned, not_lt.mpr hn.le, hn, hθ]

/-- Convex four-point inequality: `f b + f c ≤ f a + f d` for `a ≤ b,c ≤ d`, `a+d=b+c`. -/
theorem convex_four_point {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f)
    {a b c d : ℝ} (ha : a ∈ s) (hd : d ∈ s) (hab : a ≤ b) (hbd : b ≤ d)
    (hs : a + d = b + c) :
    f b + f c ≤ f a + f d := by
  by_cases he : a = d
  · have hb : b = a := le_antisymm (hbd.trans_eq he.symm) hab
    have hc : c = a := by linarith
    rw [hb, hc, ← he]
  have hpos : 0 < d - a := sub_pos.mpr (lt_of_le_of_ne (hab.trans hbd) he)
  let t : ℝ := (b - a) / (d - a)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hab) hpos.le
  have ht1 : t ≤ 1 := (div_le_one hpos).mpr (by linarith)
  have hb : (1 - t) * a + t * d = b := by dsimp [t]; field_simp; ring
  have hc : t * a + (1 - t) * d = c := by
    rw [show c = a + d - b by linarith]; dsimp [t]; field_simp; ring
  have h1 := hf.2 ha hd (sub_nonneg.mpr ht1) ht0 (by ring : (1 - t) + t = 1)
  have h2 := hf.2 ha hd ht0 (sub_nonneg.mpr ht1) (by ring : t + (1 - t) = 1)
  simp only [smul_eq_mul, hb, hc] at h1 h2
  nlinarith

/-- For `r≥1` and `A,B≥1`: `A^r+B^r ≤ (A+B-1)^r+1`. -/
theorem rpow_add_sub_one_le {r A B : ℝ} (hr : 1 ≤ r) (hA : 1 ≤ A) (hB : 1 ≤ B) :
    A ^ r + B ^ r ≤ (A + B - 1) ^ r + 1 := by
  have hf := convexOn_rpow hr
  have h := convex_four_point hf (a := 1) (b := A) (c := B) (d := A + B - 1)
    (show (1:ℝ) ∈ Ici 0 by norm_num) (show A + B - 1 ∈ Ici (0:ℝ) by
      simp only [mem_Ici]; linarith) hA (by linarith) (by ring)
  rw [one_rpow] at h
  linarith

/-- For `0<r≤1`, `x,y∈[0,1]`, `x+y≥1`: `(x+y-1)^r+1 ≤ x^r+y^r`. -/
theorem rpow_concave_four {r x y : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy1 : y ≤ 1) (hs : 1 ≤ x + y) :
    (x + y - 1) ^ r + 1 ≤ x ^ r + y ^ r := by
  have hc : ConcaveOn ℝ (Ici 0) (fun t : ℝ => t ^ r) := Real.concaveOn_rpow hr0 hr1
  have hm : MonotoneOn (fun t : ℝ => t ^ r) (Ici 0) := fun a ha b _ hab =>
    Real.rpow_le_rpow ha hab hr0
  have h := concave_monotone_four_point hc hm (a := x + y - 1) (b := x) (c := y) (d := 1)
    (by linarith) (by linarith) hx1 (by linarith) (by linarith)
  simpa [one_rpow] using h

/-- Positive branch: the Clayton CDF increases with the parameter. -/
theorem clayton_cdf_mono {θ η : ℝ} (hθ : 0 < θ) (hθη : θ ≤ η) (u v : I) :
    (clayton 2 θ hθ).cdf ![u, v] ≤ (clayton 2 η (hθ.trans_le hθη)).cdf ![u, v] := by
  have hη : 0 < η := hθ.trans_le hθη
  by_cases hz : (u : ℝ) = 0 ∨ (v : ℝ) = 0
  · rcases hz with hz | hz
    · have hu : u = 0 := Subtype.ext hz
      rw [(clayton 2 θ hθ).cdf_eq_zero_of_coord_eq_zero ![u, v] 0 (by simp [hu]),
        (clayton 2 η hη).cdf_eq_zero_of_coord_eq_zero ![u, v] 0 (by simp [hu])]
    · have hv : v = 0 := Subtype.ext hz
      rw [(clayton 2 θ hθ).cdf_eq_zero_of_coord_eq_zero ![u, v] 1 (by simp [hv]),
        (clayton 2 η hη).cdf_eq_zero_of_coord_eq_zero ![u, v] 1 (by simp [hv])]
  push Not at hz
  have hu : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 (Ne.symm hz.1)
  have hv : 0 < (v : ℝ) := lt_of_le_of_ne v.2.1 (Ne.symm hz.2)
  have hpos : ∀ i, 0 < ((![u, v] : Fin 2 → I) i : ℝ) := by
    intro i; fin_cases i <;> simpa
  rw [cdf_clayton_of_pos θ hθ _ hpos, cdf_clayton_of_pos η hη _ hpos]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  set A := (u : ℝ) ^ (-θ)
  set B := (v : ℝ) ^ (-θ)
  have hA : 1 ≤ A := one_le_rpow_of_pos_of_le_one_of_nonpos hu u.2.2 (by linarith)
  have hB : 1 ≤ B := one_le_rpow_of_pos_of_le_one_of_nonpos hv v.2.2 (by linarith)
  set r := η / θ
  have hr : 1 ≤ r := (one_le_div hθ).mpr hθη
  have huη : (u : ℝ) ^ (-η) = A ^ r := by
    rw [← rpow_mul hu.le]; congr 1; dsimp [r]; field_simp
  have hvη : (v : ℝ) ^ (-η) = B ^ r := by
    rw [← rpow_mul hv.le]; congr 1; dsimp [r]; field_simp
  rw [huη, hvη]
  have hkey := rpow_add_sub_one_le hr hA hB
  have hS : 1 ≤ A + B - 1 := by linarith
  have hlhs : 1 + (A - 1 + (B - 1)) = A + B - 1 := by ring
  have hrhs : 1 + (A ^ r - 1 + (B ^ r - 1)) = A ^ r + B ^ r - 1 := by ring
  rw [hlhs, hrhs]
  have hpos2 : 0 < A ^ r + B ^ r - 1 := by
    have : 1 ≤ A ^ r := one_le_rpow hA (by linarith)
    have : 1 ≤ B ^ r := one_le_rpow hB (by linarith)
    linarith
  have hmono := rpow_le_rpow_of_nonpos hpos2
    (show A ^ r + B ^ r - 1 ≤ (A + B - 1) ^ r by linarith)
    (neg_nonpos.mpr (inv_pos.mpr hη).le)
  rw [← rpow_mul (by linarith : (0:ℝ) ≤ A + B - 1)] at hmono
  have hexp : r * -η⁻¹ = -θ⁻¹ := by dsimp [r]; field_simp
  rw [hexp] at hmono
  exact hmono

/-- Negative branch: the truncated Clayton CDF increases with the parameter. -/
theorem claytonNegative_cdf_mono {θ η : ℝ} (hθ : -1 ≤ θ) (hθη : θ ≤ η) (hη : η < 0)
    (u v : I) :
    (claytonNegative θ hθ (hθη.trans_lt hη)).cdf ![u, v] ≤
      (claytonNegative η (hθ.trans hθη) hη).cdf ![u, v] := by
  have hθn : θ < 0 := hθη.trans_lt hη
  by_cases hz : u = 0 ∨ v = 0
  · rcases hz with hz | hz
    · rw [(claytonNegative θ hθ hθn).cdf_eq_zero_of_coord_eq_zero ![u, v] 0 (by simp [hz]),
        (claytonNegative η _ hη).cdf_eq_zero_of_coord_eq_zero ![u, v] 0 (by simp [hz])]
    · rw [(claytonNegative θ hθ hθn).cdf_eq_zero_of_coord_eq_zero ![u, v] 1 (by simp [hz]),
        (claytonNegative η _ hη).cdf_eq_zero_of_coord_eq_zero ![u, v] 1 (by simp [hz])]
  push Not at hz
  have hne : ∀ i, (![u, v] : Fin 2 → I) i ≠ 0 := by
    intro i; fin_cases i <;> simpa using (by first | exact hz.1 | exact hz.2)
  rw [cdf_claytonNegative θ hθ hθn _ hne, cdf_claytonNegative η _ hη _ hne]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hu : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 (fun e => hz.1 (Subtype.ext e.symm))
  have hv : 0 < (v : ℝ) := lt_of_le_of_ne v.2.1 (fun e => hz.2 (Subtype.ext e.symm))
  set p := -θ
  set q := -η
  have hp : 0 < p := by dsimp [p]; linarith
  have hq : 0 < q := by dsimp [q]; linarith
  have hqp : q ≤ p := by dsimp [p, q]; linarith
  set x := (u : ℝ) ^ p
  set y := (v : ℝ) ^ p
  have hx0 : 0 ≤ x := rpow_nonneg hu.le p
  have hy0 : 0 ≤ y := rpow_nonneg hv.le p
  have hx1 : x ≤ 1 := rpow_le_one hu.le u.2.2 hp.le
  have hy1 : y ≤ 1 := rpow_le_one hv.le v.2.2 hp.le
  set r := q / p
  have hr0 : 0 ≤ r := div_nonneg hq.le hp.le
  have hr1 : r ≤ 1 := (div_le_one hp).mpr hqp
  have hux : (u : ℝ) ^ q = x ^ r := by
    rw [← rpow_mul hu.le]; congr 1; dsimp [r]; field_simp
  have hvy : (v : ℝ) ^ q = y ^ r := by
    rw [← rpow_mul hv.le]; congr 1; dsimp [r]; field_simp
  rw [hux, hvy]
  have hRHS : 0 ≤ (max 0 (x ^ r + y ^ r - 1)) ^ q⁻¹ :=
    rpow_nonneg (le_max_left _ _) _
  rcases le_or_gt (x + y - 1) 0 with hs | hs
  · rw [max_eq_left hs, zero_rpow (inv_pos.mpr hp).ne']
    exact hRHS
  have hkey := rpow_concave_four hr0 hr1 hx0 hx1 hy1 (by linarith)
  have hpos : 0 < x ^ r + y ^ r - 1 := by
    have := rpow_pos_of_pos hs r; linarith
  rw [max_eq_right hs.le, max_eq_right hpos.le]
  have h1 : (x + y - 1) ^ p⁻¹ = ((x + y - 1) ^ r) ^ q⁻¹ := by
    rw [← rpow_mul hs.le]; congr 1; dsimp [r]; field_simp
  rw [h1]
  exact rpow_le_rpow (rpow_nonneg hs.le r) (by linarith) (inv_pos.mpr hq).le

theorem claytonSigned_isCI {θ : ℝ} (hθ : 0 ≤ θ) : (claytonSigned θ).IsCI := by
  rcases hθ.lt_or_eq with h | h
  · rw [claytonSigned_pos h]; exact isCI_clayton_positive θ h
  · subst h; rw [claytonSigned_zero]; exact isCI_independence

theorem claytonSigned_isCD {θ : ℝ} (hθ : -1 ≤ θ) (h0 : θ ≤ 0) : (claytonSigned θ).IsCD := by
  rcases h0.lt_or_eq with h | h
  · rw [claytonSigned_neg hθ h]; exact isCD_clayton_negative θ hθ h
  · subst h; rw [claytonSigned_zero]; exact isCD_independence

/-- Table 3: the signed Clayton family increases in lower-orthant order on `[-1,∞)`. -/
theorem claytonSigned_lowerOrthant_mono {θ η : ℝ} (hθ : -1 ≤ θ) (hθη : θ ≤ η) :
    (claytonSigned θ).LowerOrthantLE (claytonSigned η) := by
  intro x
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  rw [hx]
  rcases lt_trichotomy θ 0 with hθ0 | hθ0 | hθ0
  · rcases lt_or_ge η 0 with hη0 | hη0
    · rw [claytonSigned_neg hθ hθ0, claytonSigned_neg (hθ.trans hθη) hη0]
      exact claytonNegative_cdf_mono hθ hθη hη0 _ _
    · have h1 := (claytonSigned_isCD hθ hθ0.le).isNQD (x 0) (x 1)
      have h2 := (claytonSigned_isCI hη0).isPQD (x 0) (x 1)
      linarith
  · subst hθ0
    have h2 := (claytonSigned_isCI hθη).isPQD (x 0) (x 1)
    rw [claytonSigned_zero, cdf_independence]
    simpa [Fin.prod_univ_two] using h2
  · rw [claytonSigned_pos hθ0, claytonSigned_pos (hθ0.trans_le hθη)]
    exact clayton_cdf_mono hθ0 hθη _ _

theorem lowerOrthantLE_transpose {C D : Copula 2} (h : C.LowerOrthantLE D) :
    C.transpose.LowerOrthantLE D.transpose := by
  intro x
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  rw [hx, cdf_transpose, cdf_transpose]
  exact h ![x 1, x 0]

/-- Table 3: Schur order increases with `θ` on `θ≥0`. -/
theorem claytonSigned_schur_nonnegative {θ η : ℝ} (hθ : 0 ≤ θ) (hθη : θ ≤ η) :
    (claytonSigned θ).SchurBothLE (claytonSigned η) := by
  have hc := claytonSigned_isCI hθ
  have hd := claytonSigned_isCI (hθ.trans hθη)
  have ho := claytonSigned_lowerOrthant_mono (by linarith : (-1:ℝ) ≤ θ) hθη
  exact ⟨(schurLE_iff_lowerOrthantLE_isSI _ _ hc.1 hd.1).mpr ho,
    (schurLE_iff_lowerOrthantLE_isSI _ _ hc.2 hd.2).mpr (lowerOrthantLE_transpose ho)⟩

/-- Table 3: Schur order decreases with `θ` on `-1≤θ≤0`. -/
theorem claytonSigned_schur_nonpositive {θ η : ℝ} (hθ : -1 ≤ θ) (hθη : θ ≤ η) (hη : η ≤ 0) :
    (claytonSigned η).SchurBothLE (claytonSigned θ) := by
  have hc := claytonSigned_isCD hθ (hθη.trans hη)
  have hd := claytonSigned_isCD (hθ.trans hθη) hη
  have ho := claytonSigned_lowerOrthant_mono hθ hθη
  exact ⟨(schurLE_iff_lowerOrthantLE_isSD _ _ hd.1 hc.1).mpr ho,
    (schurLE_iff_lowerOrthantLE_isSD _ _ hd.2 hc.2).mpr (lowerOrthantLE_transpose ho)⟩

/-- Table 2: negative parameters tending to zero give the independence CDF. -/
theorem claytonNegative_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, -1 ≤ θ a) (hn : ∀ a, θ a < 0) (hlim : Tendsto θ l (𝓝 0)) (u v : I) :
    Tendsto (fun a => (claytonNegative (θ a) (hθ a) (hn a)).cdf ![u, v]) l
      (𝓝 ((u : ℝ) * v)) := by
  by_cases hz : u = 0 ∨ v = 0
  · rcases hz with hz | hz
    · simp only [hz, Set.Icc.coe_zero, zero_mul]
      refine tendsto_const_nhds.congr (fun a => ?_)
      exact ((claytonNegative (θ a) (hθ a) (hn a)).cdf_eq_zero_of_coord_eq_zero
        ![0, v] 0 rfl).symm
    · simp only [hz, Set.Icc.coe_zero, mul_zero]
      refine tendsto_const_nhds.congr (fun a => ?_)
      exact ((claytonNegative (θ a) (hθ a) (hn a)).cdf_eq_zero_of_coord_eq_zero
        ![u, 0] 1 rfl).symm
  push Not at hz
  have hu : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 (fun e => hz.1 (Subtype.ext e.symm))
  have hv : 0 < (v : ℝ) := lt_of_le_of_ne v.2.1 (fun e => hz.2 (Subtype.ext e.symm))
  let B : ℝ → ℝ := fun t => (u : ℝ) ^ (-t) + (v : ℝ) ^ (-t) - 1
  have hB0 : B 0 = 1 := by simp [B]
  have hderiv : HasDerivAt B (-log u + -log v) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (u : ℝ) ^ (-t)) (-log u) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).neg.const_rpow hu)
    have h2 : HasDerivAt (fun t : ℝ => (v : ℝ) ^ (-t)) (-log v) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).neg.const_rpow hv)
    exact (h1.add h2).sub_const 1
  have hl : HasDerivAt (fun t => log (B t)) (-log u + -log v) 0 := by
    simpa [hB0] using hderiv.log (by rw [hB0]; exact one_ne_zero)
  have hs : Tendsto (fun t : ℝ => t⁻¹ * log (B t)) (𝓝[<] 0) (𝓝 (-log u + -log v)) := by
    simpa [hB0] using hl.tendsto_slope_zero_left
  have hp : exp (-(-log u + -log v)) = (u : ℝ) * v := by
    rw [show -(-log (u:ℝ) + -log v) = log u + log v by ring, exp_add, exp_log hu, exp_log hv]
  have hBc : ContinuousAt B 0 := hderiv.continuousAt
  have hBpos : ∀ᶠ t in 𝓝[<] (0:ℝ), 0 < B t := by
    have := hBc.eventually (lt_mem_nhds (show (0:ℝ) < B 0 by rw [hB0]; norm_num))
    exact nhdsWithin_le_nhds this
  have hmain : Tendsto (fun t : ℝ => (max 0 (B t)) ^ (-t)⁻¹) (𝓝[<] 0) (𝓝 ((u:ℝ) * v)) := by
    rw [← hp]
    apply (hs.neg.rexp).congr'
    filter_upwards [hBpos] with t ht
    rw [max_eq_right ht.le, rpow_def_of_pos ht]
    congr 1
    rw [inv_neg]; ring
  have ht : Tendsto θ l (𝓝[<] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hn⟩
  have hne : ∀ i, (![u, v] : Fin 2 → I) i ≠ 0 := by
    intro i; fin_cases i
    · simpa using hz.1
    · simpa using hz.2
  refine (hmain.comp ht).congr (fun a => ?_)
  rw [cdf_claytonNegative _ _ _ _ hne]
  simp [B]

end Verification
