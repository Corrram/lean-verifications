import Papers.Rockel2026ExactBlest.Source.Families
import Papers.Common.Calculus

/-! # The cost and the potentials of Section 4.2 are the companion's

The article defines the cost `d_κ`, the parameters `κ_w`, `κ_b`, the branches
`z_∓` and pieces `R_b^∓`, and the potentials `φ_w, ψ_w, φ_b, ψ_b` by their value
at one point and their piecewise derivative. Proofread reads such a definition as
`φ(x) = φ(a) + ∫_a^x φ'`. This file evaluates these integrals piece by piece with
the fundamental theorem of calculus: each potential is the companion's
(`paperPhiA`, `paperPsiA`, `paperPhiB`, `paperPsiB`), whose derivatives the
companion proves. The support `S_w` is the companion's contact set. -/

namespace Papers.Rockel2026ExactBlest.Source.Bridge
open Papers.Rockel2026ExactBlest.Source Proofread MeasureTheory Set
open scoped unitInterval
open Papers.Common (intervalIntegrable_piece integral_piece intervalIntegrable_two_pieces
  integral_two_pieces intervalIntegrable_three_pieces integral_three_pieces)
open Papers.Rockel2026ExactBlest (paperPhiA paperPsiA paperPhiB paperPsiB cost paperR
  hasDerivAt_paperPhiA hasDerivAt_paperPsiA hasDerivAt_paperPhiB hasDerivAt_paperPsiB
  paperPotentialsA_normalized paperPotentialsB_normalized continuous_phiA continuous_psiA
  continuous_phiB continuous_psiB paperR_formula)

/-! ## Constants and pieces -/

theorem d_eq (k x y : ℝ) : d k x y = cost k x y := rfl
theorem kappa_eq (w : ℝ) : kappa w = (3 - 2 * w) / (2 * w) := rfl
theorem z_def (b : ℝ) : z b = b / (2 * (1 - b)) := rfl
theorem zMinus_eq (b x : ℝ) : zMinus b x = (x + b - 1) / (2 * (1 - b)) := rfl
theorem RMinus_eq (b x : ℝ) : RMinus b x = 2 * (1 - b) * x + 1 - b := rfl
theorem RPlus_eq (b x : ℝ) : RPlus b x = (1 - b) * (1 - 2 * x) / (1 - 2 * b) := rfl

theorem kappa30_A {w : ℝ} (hw : 1 / 2 ≤ w ∧ w < 1) : kappa30 w = kappa w := by
  unfold kappa30
  rw [ite_eq_left hw]

theorem kappa30_B {b : ℝ} (hb : 0 < b ∧ b < 1 / 2) : kappa30 b = 2 * (1 - b) / b := by
  unfold kappa30
  rw [ite_eq_right (fun h => by linarith [h.1, hb.2]), ite_eq_left hb]

theorem kappa_pos {w : ℝ} (hw : 1 / 2 ≤ w ∧ w < 1) : 0 < kappa w := by
  rw [kappa_eq]
  apply div_pos <;> linarith [hw.1, hw.2]

theorem kappa30_pos {b : ℝ} (hb : 0 < b ∧ b < 1 / 2) : 0 < kappa30 b := by
  rw [kappa30_B hb]
  apply div_pos <;> linarith [hb.1, hb.2]

theorem z_pos {b : ℝ} (hb : 0 < b ∧ b < 1 / 2) : 0 < z b := by
  rw [z_def]
  apply div_pos hb.1
  linarith [hb.2]

theorem z_lt {b : ℝ} (hb : 0 < b ∧ b < 1 / 2) : z b < b := by
  rw [z_def, div_lt_iff₀ (by linarith [hb.2])]
  nlinarith [hb.1, hb.2]

theorem paperR_one {b t : ℝ} (h : t ≤ b / (2 * (1 - b))) : paperR b t = 2 * (1 - b) * t + 1 - b := by
  unfold paperR
  rw [ite_eq_left h]

theorem paperR_two {b t : ℝ} (h1 : b / (2 * (1 - b)) < t) (h2 : t ≤ b) :
    paperR b t = (1 - b) * (1 - 2 * t) / (1 - 2 * b) := by
  unfold paperR
  rw [ite_eq_right (not_le.mpr h1), ite_eq_left h2]

theorem paperR_three {b t : ℝ} (h1 : b / (2 * (1 - b)) < t) (h2 : b < t) : paperR b t = 1 - t := by
  unfold paperR
  rw [ite_eq_right (not_le.mpr h1), ite_eq_right (not_le.mpr h2)]

/-- The map `R_b` of the article on the real line. -/
theorem R_coe {b : ℝ} (hb : 0 < b ∧ b < 1 / 2) (t : I) : (R b t : ℝ) = paperR b t := by
  rw [R_eq b hb.1 hb.2]
  exact paperR_formula (unitOf b hb.1 hb.2.le) hb.1 hb.2 t

/-! ## The potentials of the graph regime -/

/-- `φ_w(x) = ∫_{1-w}^x φ_w'` is the companion's `φ_w`, for any integrand that agrees with
the article's derivative on its two pieces. -/
theorem phiA_pieces {g : ℝ → ℝ} {w x : ℝ} (hw : 1 / 2 ≤ w ∧ w < 1) (hx : 0 ≤ x ∧ x ≤ 1)
    (h1 : ∀ t ∈ Ioo 0 (1 - w), g t = (1 - t) * (2 * t - kappa w * (1 - t)))
    (h2 : ∀ t ∈ Ioo (1 - w) 1, g t = (t + w - 1) * (2 * t - kappa w * (t + w - 1))) :
    Prelude.intervalIntegrable g (1 - w) x ∧ 0 + Prelude.intervalIntegral (1 - w) x g = paperPhiA w x := by
  have hF : Continuous (paperPhiA w) := continuous_phiA (1 - w)
  have h0 : paperPhiA w (1 - w) = 0 := (paperPotentialsA_normalized w (by linarith [hw.1])).1
  unfold Prelude.intervalIntegrable Prelude.intervalIntegral
  rw [zero_add]
  rcases le_total (1 - w) x with h | h
  · have hd : ∀ t ∈ Ioo (1 - w) x, HasDerivAt (paperPhiA w)
        ((fun t => (t + w - 1) * (2 * t - (3 - 2 * w) / (2 * w) * (t + w - 1))) t) t := by
      intro t ht
      have hd := hasDerivAt_paperPhiA w t (ne_of_gt ht.1)
      rwa [ite_eq_right (not_le.mpr ht.1)] at hd
    have hc : ContinuousOn (fun t => (t + w - 1) * (2 * t - (3 - 2 * w) / (2 * w) * (t + w - 1)))
        (Icc (1 - w) x) := Continuous.continuousOn (by fun_prop)
    have he : EqOn g (fun t => (t + w - 1) * (2 * t - (3 - 2 * w) / (2 * w) * (t + w - 1))) (Ioo (1 - w) x) :=
      fun t ht => by rw [h2 t ⟨ht.1, lt_of_lt_of_le ht.2 hx.2⟩, kappa_eq]
    refine ⟨intervalIntegrable_piece h hc he, ?_⟩
    rw [integral_piece h hF.continuousOn hd hc he, h0, sub_zero]
  · have hd : ∀ t ∈ Ioo x (1 - w), HasDerivAt (paperPhiA w)
        ((fun t => (1 - t) * (2 * t - (3 - 2 * w) / (2 * w) * (1 - t))) t) t := by
      intro t ht
      have hd := hasDerivAt_paperPhiA w t (ne_of_lt ht.2)
      rwa [ite_eq_left ht.2.le] at hd
    have hc : ContinuousOn (fun t => (1 - t) * (2 * t - (3 - 2 * w) / (2 * w) * (1 - t))) (Icc x (1 - w)) :=
      Continuous.continuousOn (by fun_prop)
    have he : EqOn g (fun t => (1 - t) * (2 * t - (3 - 2 * w) / (2 * w) * (1 - t))) (Ioo x (1 - w)) :=
      fun t ht => by rw [h1 t ⟨lt_of_le_of_lt hx.1 ht.1, ht.2⟩, kappa_eq]
    refine ⟨(intervalIntegrable_piece h hc he).symm, ?_⟩
    rw [intervalIntegral.integral_symm, integral_piece h hF.continuousOn hd hc he, h0]
    ring

/-- `ψ_w(z) = ∫_0^z ψ_w'` is the companion's `ψ_w`. -/
theorem psiA_pieces {g : ℝ → ℝ} {w y : ℝ} (hw : 1 / 2 ≤ w ∧ w < 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (h1 : ∀ t ∈ Ioo 0 w, g t = (t + 1 - w) * (t + 1 - w - 2 * kappa w * t))
    (h2 : ∀ t ∈ Ioo w 1, g t = (1 - t) * (1 - t - 2 * kappa w * t)) :
    Prelude.intervalIntegrable g 0 y ∧ 0 + Prelude.intervalIntegral 0 y g = paperPsiA w y := by
  have hF : Continuous (paperPsiA w) := continuous_psiA (1 - w)
  have h0 : paperPsiA w 0 = 0 := (paperPotentialsA_normalized w (by linarith [hw.1])).2
  unfold Prelude.intervalIntegrable Prelude.intervalIntegral
  rw [zero_add]
  have hd1 : ∀ t ∈ Ioo 0 (min y w), HasDerivAt (paperPsiA w)
      ((fun t => (t + 1 - w) * (t + 1 - w - 2 * ((3 - 2 * w) / (2 * w)) * t)) t) t := by
    intro t ht
    have hd := hasDerivAt_paperPsiA w t (ne_of_lt (lt_of_lt_of_le ht.2 (min_le_right _ _)))
    rwa [ite_eq_left (lt_of_lt_of_le ht.2 (min_le_right _ _)).le] at hd
  have hd2 : ∀ t ∈ Ioo w y, HasDerivAt (paperPsiA w)
      ((fun t => (1 - t) * (1 - t - 2 * ((3 - 2 * w) / (2 * w)) * t)) t) t := by
    intro t ht
    have hd := hasDerivAt_paperPsiA w t (ne_of_gt ht.1)
    rwa [ite_eq_right (not_le.mpr ht.1)] at hd
  have hc1 : ∀ a b : ℝ, ContinuousOn (fun t => (t + 1 - w) * (t + 1 - w - 2 * ((3 - 2 * w) / (2 * w)) * t))
      (Icc a b) := fun _ _ => Continuous.continuousOn (by fun_prop)
  have hc2 : ∀ a b : ℝ, ContinuousOn (fun t => (1 - t) * (1 - t - 2 * ((3 - 2 * w) / (2 * w)) * t))
      (Icc a b) := fun _ _ => Continuous.continuousOn (by fun_prop)
  have he1 : ∀ m ≤ w, EqOn g (fun t => (t + 1 - w) * (t + 1 - w - 2 * ((3 - 2 * w) / (2 * w)) * t)) (Ioo 0 m) :=
    fun m hm t ht => by rw [h1 t ⟨ht.1, lt_of_lt_of_le ht.2 hm⟩, kappa_eq]
  have he2 : EqOn g (fun t => (1 - t) * (1 - t - 2 * ((3 - 2 * w) / (2 * w)) * t)) (Ioo w y) :=
    fun t ht => by rw [h2 t ⟨ht.1, lt_of_lt_of_le ht.2 hy.2⟩, kappa_eq]
  rcases le_total y w with h | h
  · have hd1' : ∀ t ∈ Ioo 0 y, HasDerivAt (paperPsiA w)
        ((fun t => (t + 1 - w) * (t + 1 - w - 2 * ((3 - 2 * w) / (2 * w)) * t)) t) t := by
      intro t ht; exact hd1 t ⟨ht.1, by rw [min_eq_left h]; exact ht.2⟩
    refine ⟨intervalIntegrable_piece hy.1 (hc1 0 y) (he1 y h), ?_⟩
    rw [integral_piece hy.1 hF.continuousOn hd1' (hc1 0 y) (he1 y h), h0, sub_zero]
  · have hd1' : ∀ t ∈ Ioo 0 w, HasDerivAt (paperPsiA w)
        ((fun t => (t + 1 - w) * (t + 1 - w - 2 * ((3 - 2 * w) / (2 * w)) * t)) t) t := by
      intro t ht; exact hd1 t ⟨ht.1, by rw [min_eq_right h]; exact ht.2⟩
    have hw0 : (0 : ℝ) ≤ w := by linarith [hw.1]
    refine ⟨intervalIntegrable_two_pieces hw0 h (hc1 0 w) (he1 w le_rfl) (hc2 w y) he2, ?_⟩
    rw [integral_two_pieces hw0 h hF.continuousOn hd1' (hc1 0 w) (he1 w le_rfl) hd2 (hc2 w y) he2, h0,
      sub_zero]

/-! ## The potentials of the randomized regime -/

/-- `φ_b(x) = ∫_{1-b}^x φ_b'` is the companion's `φ_b`. -/
theorem phiB_pieces {g : ℝ → ℝ} {b x : ℝ} (hb : 0 < b ∧ b < 1 / 2) (hx : 0 ≤ x ∧ x ≤ 1)
    (h1 : ∀ t ∈ Ioo 0 (1 - b), g t = (1 - t) * (2 * t - kappa30 b * (1 - t)))
    (h2 : ∀ t ∈ Ioo (1 - b) 1, g t = zMinus b t * (2 * t - kappa30 b * zMinus b t)) :
    Prelude.intervalIntegrable g (1 - b) x ∧ 0 + Prelude.intervalIntegral (1 - b) x g = paperPhiB b x := by
  have hF : Continuous (paperPhiB b) := continuous_phiB (1 - b)
  have h0 : paperPhiB b (1 - b) = 0 := (paperPotentialsB_normalized b hb.1 hb.2).1
  have hb1 : b ≠ 1 := by linarith [hb.2]
  unfold Prelude.intervalIntegrable Prelude.intervalIntegral
  rw [zero_add]
  rcases le_total (1 - b) x with h | h
  · have hd : ∀ t ∈ Ioo (1 - b) x, HasDerivAt (paperPhiB b)
        ((fun t => ((t + b - 1) / (2 * (1 - b))) * (2 * t - 2 * (1 - b) / b * ((t + b - 1) / (2 * (1 - b))))) t)
        t := by
      intro t ht
      have hd := hasDerivAt_paperPhiB b t hb1 (ne_of_gt ht.1)
      rwa [ite_eq_right (not_le.mpr ht.1)] at hd
    have hc : ContinuousOn
        (fun t => ((t + b - 1) / (2 * (1 - b))) * (2 * t - 2 * (1 - b) / b * ((t + b - 1) / (2 * (1 - b)))))
        (Icc (1 - b) x) := Continuous.continuousOn (by fun_prop)
    have he : EqOn g
        (fun t => ((t + b - 1) / (2 * (1 - b))) * (2 * t - 2 * (1 - b) / b * ((t + b - 1) / (2 * (1 - b)))))
        (Ioo (1 - b) x) :=
      fun t ht => by rw [h2 t ⟨ht.1, lt_of_lt_of_le ht.2 hx.2⟩, kappa30_B hb, zMinus_eq]
    refine ⟨intervalIntegrable_piece h hc he, ?_⟩
    rw [integral_piece h hF.continuousOn hd hc he, h0, sub_zero]
  · have hd : ∀ t ∈ Ioo x (1 - b), HasDerivAt (paperPhiB b)
        ((fun t => (1 - t) * (2 * t - 2 * (1 - b) / b * (1 - t))) t) t := by
      intro t ht
      have hd := hasDerivAt_paperPhiB b t hb1 (ne_of_lt ht.2)
      rwa [ite_eq_left ht.2.le] at hd
    have hc : ContinuousOn (fun t => (1 - t) * (2 * t - 2 * (1 - b) / b * (1 - t))) (Icc x (1 - b)) :=
      Continuous.continuousOn (by fun_prop)
    have he : EqOn g (fun t => (1 - t) * (2 * t - 2 * (1 - b) / b * (1 - t))) (Ioo x (1 - b)) :=
      fun t ht => by rw [h1 t ⟨lt_of_le_of_lt hx.1 ht.1, ht.2⟩, kappa30_B hb]
    refine ⟨(intervalIntegrable_piece h hc he).symm, ?_⟩
    rw [intervalIntegral.integral_symm, integral_piece h hF.continuousOn hd hc he, h0]
    ring

/-- `ψ_b(z) = ∫_0^z ψ_b'` is the companion's `ψ_b`. -/
theorem psiB_pieces {g : ℝ → ℝ} {b y : ℝ} (hb : 0 < b ∧ b < 1 / 2) (hy : 0 ≤ y ∧ y ≤ 1)
    (h1 : ∀ t ∈ Ioo 0 (z b), g t = RMinus b t * (RMinus b t - 2 * kappa30 b * t))
    (h2 : ∀ t ∈ Ioo (z b) b, g t = RPlus b t * (RPlus b t - 2 * kappa30 b * t))
    (h3 : ∀ t ∈ Ioo b 1, g t = (1 - t) * (1 - t - 2 * kappa30 b * t)) :
    Prelude.intervalIntegrable g 0 y ∧ 0 + Prelude.intervalIntegral 0 y g = paperPsiB b y := by
  have hF : Continuous (paperPsiB b) := continuous_psiB (1 - b) (by linarith [hb.2]) (by linarith [hb.1])
  have h0 : paperPsiB b 0 = 0 := (paperPotentialsB_normalized b hb.1 hb.2).2
  have hz0 := z_pos hb
  have hzb := z_lt hb
  unfold Prelude.intervalIntegrable Prelude.intervalIntegral
  rw [zero_add]
  -- the derivative on each piece
  let k : ℝ := 2 * (1 - b) / b
  let f1 : ℝ → ℝ := fun t => (2 * (1 - b) * t + 1 - b) * ((2 * (1 - b) * t + 1 - b) - 2 * k * t)
  let f2 : ℝ → ℝ := fun t => ((1 - b) * (1 - 2 * t) / (1 - 2 * b)) *
    ((1 - b) * (1 - 2 * t) / (1 - 2 * b) - 2 * k * t)
  let f3 : ℝ → ℝ := fun t => (1 - t) * ((1 - t) - 2 * k * t)
  have hc1 : ∀ a c : ℝ, ContinuousOn f1 (Icc a c) := fun _ _ => Continuous.continuousOn (by fun_prop)
  have hc2 : ∀ a c : ℝ, ContinuousOn f2 (Icc a c) := fun _ _ => Continuous.continuousOn (by fun_prop)
  have hc3 : ∀ a c : ℝ, ContinuousOn f3 (Icc a c) := fun _ _ => Continuous.continuousOn (by fun_prop)
  have hd1 : ∀ m ≤ z b, ∀ t ∈ Ioo 0 m, HasDerivAt (paperPsiB b) (f1 t) t := by
    intro m hm t ht
    have ht' : t < b / (2 * (1 - b)) := lt_of_lt_of_le ht.2 hm
    have hd := hasDerivAt_paperPsiB b t (ne_of_lt ht') (ne_of_lt (lt_trans ht' hzb))
    rwa [paperR_one ht'.le] at hd
  have hd2 : ∀ m ≤ b, ∀ t ∈ Ioo (z b) m, HasDerivAt (paperPsiB b) (f2 t) t := by
    intro m hm t ht
    have ht1 : b / (2 * (1 - b)) < t := ht.1
    have hd := hasDerivAt_paperPsiB b t (ne_of_gt ht1) (ne_of_lt (lt_of_lt_of_le ht.2 hm))
    rwa [paperR_two ht1 (lt_of_lt_of_le ht.2 hm).le] at hd
  have hd3 : ∀ t ∈ Ioo b y, HasDerivAt (paperPsiB b) (f3 t) t := by
    intro t ht
    have ht1 : b / (2 * (1 - b)) < t := lt_trans hzb ht.1
    have hd := hasDerivAt_paperPsiB b t (ne_of_gt ht1) (ne_of_gt ht.1)
    rwa [paperR_three ht1 ht.1] at hd
  have he1 : ∀ m ≤ z b, EqOn g f1 (Ioo 0 m) :=
    fun m hm t ht => by rw [h1 t ⟨ht.1, lt_of_lt_of_le ht.2 hm⟩, kappa30_B hb, RMinus_eq]
  have he2 : ∀ m ≤ b, EqOn g f2 (Ioo (z b) m) :=
    fun m hm t ht => by rw [h2 t ⟨ht.1, lt_of_lt_of_le ht.2 hm⟩, kappa30_B hb, RPlus_eq]
  have he3 : EqOn g f3 (Ioo b y) :=
    fun t ht => by rw [h3 t ⟨ht.1, lt_of_lt_of_le ht.2 hy.2⟩, kappa30_B hb]
  rcases le_total y (z b) with hyz | hyz
  · refine ⟨intervalIntegrable_piece hy.1 (hc1 0 y) (he1 y hyz), ?_⟩
    rw [integral_piece hy.1 hF.continuousOn (hd1 y hyz) (hc1 0 y) (he1 y hyz), h0, sub_zero]
  · rcases le_total y b with hyb | hyb
    · refine ⟨intervalIntegrable_two_pieces hz0.le hyz (hc1 0 (z b)) (he1 (z b) le_rfl) (hc2 (z b) y)
        (he2 y hyb), ?_⟩
      rw [integral_two_pieces hz0.le hyz hF.continuousOn (hd1 (z b) le_rfl) (hc1 0 (z b)) (he1 (z b) le_rfl)
        (hd2 y hyb) (hc2 (z b) y) (he2 y hyb), h0, sub_zero]
    · refine ⟨intervalIntegrable_three_pieces hz0.le hzb.le hyb (hc1 0 (z b)) (he1 (z b) le_rfl)
        (hc2 (z b) b) (he2 b le_rfl) (hc3 b y) he3, ?_⟩
      rw [integral_three_pieces hz0.le hzb.le hyb hF.continuousOn (hd1 (z b) le_rfl) (hc1 0 (z b))
        (he1 (z b) le_rfl) (hd2 b le_rfl) (hc2 (z b) b) (he2 b le_rfl) hd3 (hc3 b y) he3, h0, sub_zero]

/-! ## The article's potentials -/

theorem varphi_eq {w x : ℝ} (hw : 1 / 2 ≤ w ∧ w < 1) (hx : 0 ≤ x ∧ x ≤ 1) : varphi w x = paperPhiA w x := by
  unfold varphi
  exact (phiA_pieces hw hx (fun t ht => ite_eq_left ht)
    (fun t ht => (ite_eq_right (fun h => by linarith [h.2, ht.1])).trans (ite_eq_left ht))).2

theorem psi_eq {w y : ℝ} (hw : 1 / 2 ≤ w ∧ w < 1) (hy : 0 ≤ y ∧ y ≤ 1) : psi w y = paperPsiA w y := by
  unfold psi
  exact (psiA_pieces hw hy (fun t ht => ite_eq_left ht)
    (fun t ht => (ite_eq_right (fun h => by linarith [h.2, ht.1])).trans (ite_eq_left ht))).2

theorem varphi33_eq {b x : ℝ} (hb : 0 < b ∧ b < 1 / 2) (hx : 0 ≤ x ∧ x ≤ 1) :
    varphi33 b x = paperPhiB b x := by
  unfold varphi33
  rw [ite_eq_right (fun h => by linarith [h.1, hb.2]), ite_eq_left hb]
  exact (phiB_pieces hb hx (fun t ht => ite_eq_left ht)
    (fun t ht => (ite_eq_right (fun h => by linarith [h.2, ht.1])).trans (ite_eq_left ht))).2

theorem psi34_eq {b y : ℝ} (hb : 0 < b ∧ b < 1 / 2) (hy : 0 ≤ y ∧ y ≤ 1) : psi34 b y = paperPsiB b y := by
  unfold psi34
  rw [ite_eq_right (fun h => by linarith [h.1, hb.2]), ite_eq_left hb]
  exact (psiB_pieces hb hy (fun t ht => ite_eq_left ht)
    (fun t ht => (ite_eq_right (fun h => by linarith [h.2, ht.1])).trans (ite_eq_left ht))
    (fun t ht => (ite_eq_right (fun h => by linarith [h.2, ht.1, z_lt hb])).trans
      ((ite_eq_right (fun h => by linarith [h.2, ht.1])).trans (ite_eq_left ht)))).2

/-! ## The support `S_w` -/

theorem S_iff {w x y : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) :
    S w x y ↔ (x ≤ 1 - w ∧ y = 1 - x) ∨ (1 - w ≤ x ∧ y = x + w - 1) := by
  unfold S
  constructor
  · rintro (⟨t, ⟨-, h1⟩, rfl, rfl⟩ | ⟨t, ⟨h0, -⟩, rfl, rfl⟩)
    · exact Or.inl ⟨h1, rfl⟩
    · exact Or.inr ⟨h0, rfl⟩
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact Or.inl ⟨x, ⟨hx.1, h⟩, rfl, rfl⟩
    · exact Or.inr ⟨x, ⟨h, hx.2⟩, rfl, rfl⟩

end Papers.Rockel2026ExactBlest.Source.Bridge
