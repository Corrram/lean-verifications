import Verification.StochasticBounds
import Mathlib.Analysis.Convex.Slope

/-! # Section 5: median sections and the gap function

The set `S` of median sections of the source is encoded through the slope `p`
of the section: a nonincreasing function with values in `[0,1]` on `[0,1]`
and `∫₀¹ p = 1/2`.  The section itself is `A(u) = ∫₀ᵘ p`, the companion is
`B(u) = 1/2 + u - A(u)`, and the gap function of equation (5.2) is
`w = B - A`.  Only the values of `p` on `[0,1]` matter; the global
monotonicity is a harmless normalization (every nonincreasing `p` on `[0,1]` has such an
extension) that makes interval-integral calculus and the countability of
discontinuities available without side conditions.
-/

open MeasureTheory ProbabilityTheory Set intervalIntegral
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

/-- An element of the set `S` of Section 5: a median section `A(u) = ∫₀ᵘ p`, with `p`
nonincreasing, `0 ≤ p ≤ 1` on `[0,1]` and `∫₀¹ p = 1/2`. -/
structure MedianSection where
  /-- the slope of the median section -/
  p : ℝ → ℝ
  antitone : Antitone p
  nonneg : 0 ≤ p 1
  le_one : p 0 ≤ 1
  integral_eq : ∫ t in (0 : ℝ)..1, p t = 1 / 2

namespace MedianSection

variable (s : MedianSection)

theorem p_nonneg {u : ℝ} (hu : u ≤ 1) : 0 ≤ s.p u := s.nonneg.trans (s.antitone hu)

theorem p_le_one {u : ℝ} (hu : 0 ≤ u) : s.p u ≤ 1 := (s.antitone hu).trans s.le_one

theorem intervalIntegrable_p (a b : ℝ) : IntervalIntegrable s.p volume a b :=
  s.antitone.intervalIntegrable

/-- The median section `A(u) = ∫₀ᵘ p`. -/
noncomputable def A (u : ℝ) : ℝ := ∫ t in (0 : ℝ)..u, s.p t

/-- The companion `B(u) = 1/2 + u - A(u)` of the median section. -/
noncomputable def B (u : ℝ) : ℝ := 1 / 2 + u - s.A u

/-- The gap function `w = B - A` of equation (5.2). -/
noncomputable def gap (u : ℝ) : ℝ := s.B u - s.A u

@[simp] theorem A_zero : s.A 0 = 0 := by simp [A]

theorem A_one : s.A 1 = 1 / 2 := s.integral_eq

theorem A_sub {a b : ℝ} : s.A b - s.A a = ∫ t in a..b, s.p t := by
  unfold A
  rw [integral_interval_sub_left (s.intervalIntegrable_p _ _) (s.intervalIntegrable_p _ _)]

theorem gap_eq (u : ℝ) : s.gap u = 1 / 2 + u - 2 * s.A u := by
  unfold gap B; ring

theorem B_zero : s.B 0 = 1 / 2 := by simp [B]

theorem B_one : s.B 1 = 1 := by simp [B, A_one]

theorem gap_zero : s.gap 0 = 1 / 2 := by simp [gap_eq]

theorem gap_one : s.gap 1 = 1 / 2 := by rw [gap_eq, A_one]; ring

theorem A_mono {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 1) : s.A a ≤ s.A b := by
  have : 0 ≤ ∫ t in a..b, s.p t :=
    integral_nonneg hab (fun t ht => s.p_nonneg (ht.2.trans hb))
  linarith [s.A_sub (a := a) (b := b)]

theorem A_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : s.A b - s.A a ≤ b - a := by
  have h : ∫ t in a..b, s.p t ≤ ∫ t in a..b, (1 : ℝ) :=
    integral_mono_on hab (s.intervalIntegrable_p _ _) intervalIntegrable_const
      (fun t ht => s.p_le_one (ha.trans ht.1))
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
  linarith [s.A_sub (a := a) (b := b)]

theorem abs_A_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1) :
    |s.A b - s.A a| ≤ |b - a| := by
  rcases le_total a b with h | h
  · rw [abs_of_nonneg (by linarith [s.A_mono h hb1]), abs_of_nonneg (by linarith)]
    exact s.A_sub_le ha h
  · rw [abs_of_nonpos (by linarith [s.A_mono h ha1]), abs_of_nonpos (by linarith)]
    linarith [s.A_sub_le hb h]

theorem continuous_A : Continuous s.A :=
  intervalIntegral.continuous_primitive (fun a b => s.intervalIntegrable_p a b) 0

theorem continuous_B : Continuous s.B := by
  unfold B; have := s.continuous_A; fun_prop

theorem continuous_gap : Continuous s.gap := by
  unfold gap; have := s.continuous_A; have := s.continuous_B; fun_prop

theorem A_nonneg {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) : 0 ≤ s.A u := by
  simpa using s.A_mono hu hu1

theorem A_le_half {u : ℝ} (hu1 : u ≤ 1) : s.A u ≤ 1 / 2 := by
  rw [← s.A_one]; exact s.A_mono hu1 le_rfl

theorem A_le_self {u : ℝ} (hu : 0 ≤ u) : s.A u ≤ u := by
  simpa using s.A_sub_le (le_refl 0) hu

theorem A_ge {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) : u - 1 / 2 ≤ s.A u := by
  have := s.A_sub_le hu hu1
  rw [s.A_one] at this
  linarith

theorem half_le_B {u : ℝ} (hu : 0 ≤ u) : 1 / 2 ≤ s.B u := by
  unfold B; linarith [s.A_le_self hu]

theorem B_le_one {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) : s.B u ≤ 1 := by
  unfold B; linarith [s.A_ge hu hu1]

theorem B_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : s.B a ≤ s.B b := by
  unfold B; linarith [s.A_sub_le ha hab]

theorem A_le_B {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) : s.A u ≤ s.B u :=
  (s.A_le_half hu1).trans (s.half_le_B hu)

/-- The gap function lies above the tent `|u - 1/2|` (source, after (5.2)). -/
theorem abs_le_gap {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) : |u - 1 / 2| ≤ s.gap u := by
  rw [gap_eq]
  have h1 := s.A_le_self hu
  have h2 := s.A_le_half hu1
  rw [abs_le]; constructor <;> linarith

theorem gap_nonneg {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) : 0 ≤ s.gap u :=
  (abs_nonneg _).trans (s.abs_le_gap hu hu1)

theorem gap_half : s.gap (1 / 2) = 1 - 2 * s.A (1 / 2) := by rw [gap_eq]; ring

/-- The gap function is `1/2 + ∫₀ᵘ (1 - 2p)`, i.e. `w' = 1 - 2p`. -/
theorem gap_eq_integral (u : ℝ) : s.gap u = 1 / 2 + ∫ t in (0 : ℝ)..u, (1 - 2 * s.p t) := by
  rw [gap_eq, intervalIntegral.integral_sub intervalIntegrable_const
    ((s.intervalIntegrable_p _ _).const_mul 2), intervalIntegral.integral_const_mul]
  simp [A]
  ring

/-- `A` is concave on `[0,1]`. -/
theorem concaveOn_A : ConcaveOn ℝ (Icc (0 : ℝ) 1) s.A := by
  apply concaveOn_of_slope_anti_adjacent (convex_Icc 0 1)
  intro x y z hx hz hxy hyz
  have h1 : (y - x) * s.p y ≤ s.A y - s.A x := by
    have h : ∫ t in x..y, s.p y ≤ ∫ t in x..y, s.p t :=
      integral_mono_on hxy.le intervalIntegrable_const (s.intervalIntegrable_p _ _)
        (fun t ht => s.antitone ht.2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith [s.A_sub (a := x) (b := y)]
  have h2 : s.A z - s.A y ≤ (z - y) * s.p y := by
    have h : ∫ t in y..z, s.p t ≤ ∫ t in y..z, s.p y :=
      integral_mono_on hyz.le (s.intervalIntegrable_p _ _) intervalIntegrable_const
        (fun t ht => s.antitone ht.1)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith [s.A_sub (a := y) (b := z)]
  have hyx : 0 < y - x := by linarith
  have hzy : 0 < z - y := by linarith
  rw [div_le_iff₀ hzy, div_mul_eq_mul_div, le_div_iff₀ hyx]
  nlinarith

/-- The gap function is convex on `[0,1]` (source, after (5.2)). -/
theorem convexOn_gap : ConvexOn ℝ (Icc (0 : ℝ) 1) s.gap := by
  have h1 := (s.concaveOn_A.neg).smul (show (0 : ℝ) ≤ 2 by norm_num)
  have h2 : ConvexOn ℝ (Icc (0 : ℝ) 1) (fun u : ℝ => 1 / 2 + u) :=
    (convexOn_const (1 / 2 : ℝ) (convex_Icc 0 1)).add (convexOn_id (convex_Icc 0 1))
  have h3 := h2.add h1
  convert h3 using 1
  funext u
  simp only [gap_eq, Pi.add_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- The gap function is `1`-Lipschitz on `[0,1]`. -/
theorem abs_gap_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1) :
    |s.gap b - s.gap a| ≤ |b - a| := by
  rcases le_total a b with h | h
  · have h1 := s.A_mono h hb1
    have h2 := s.A_sub_le ha h
    rw [abs_of_nonneg (show 0 ≤ b - a by linarith), gap_eq, gap_eq, abs_le]
    constructor <;> linarith
  · have h1 := s.A_mono h ha1
    have h2 := s.A_sub_le hb h
    rw [abs_of_nonpos (show b - a ≤ 0 by linarith), gap_eq, gap_eq, abs_le]
    constructor <;> linarith

end MedianSection

/-- The median section `A = C(·, 1/2)` of an SI copula belongs to `S` (source, paragraph before
Lemma 5.1): `p` is a nonincreasing version of `∂₁C(·, 1/2)`. -/
theorem exists_medianSection_of_isSI (C : Copula 2) (hC : C.IsSI) :
    ∃ s : MedianSection, ∀ u : I, s.A u = C.cdf ![u, Copula.unitHalf] := by
  obtain ⟨g, hg, hb, he⟩ := Verification.conditionalCDF_antitone_version C hC Copula.unitHalf
  let p : ℝ → ℝ := fun x => g (Set.projIcc (0 : ℝ) 1 zero_le_one x)
  have hp : ∀ t : I, p (t : ℝ) = g t := fun t => by
    simp only [p]; rw [Set.projIcc_val]
  have hpa : Antitone p := fun x y hxy => hg (Set.monotone_projIcc zero_le_one hxy)
  have hint : ∀ u : I, ∫ t in (0 : ℝ)..(u : ℝ), p t = C.cdf ![u, Copula.unitHalf] := by
    intro u
    rw [← Copula.integral_unit_Iic p u, C.cdf_eq_integral_conditionalCDF]
    calc (∫ t in Iic u, p (t : ℝ)) = ∫ t in Iic u, g t :=
          integral_congr_ae (Filter.Eventually.of_forall hp)
      _ = ∫ t in Iic u, C.conditionalCDF t Copula.unitHalf :=
          integral_congr_ae (ae_restrict_of_ae he.symm)
  have h1 : ∫ t in (0 : ℝ)..1, p t = 1 / 2 := by
    have := hint 1
    rw [Copula.cdf_two_one_left] at this
    simpa [Copula.unitHalf] using this
  refine ⟨⟨p, hpa, (hb _).1, (hb _).2, h1⟩, fun u => ?_⟩
  exact hint u

end Papers.OrendayLaresRockel2026XiBeta
