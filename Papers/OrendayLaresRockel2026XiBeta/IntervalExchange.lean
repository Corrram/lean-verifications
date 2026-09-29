import Copula.Basic

/-! # The interval exchange `T_b` of Proposition 4.2

For `b ∈ [-1, 1]` put `s_b = (1 + b) / 4 ∈ [0, 1/2]`. The map `T_b : [0,1] → [0,1]` swaps
the two middle intervals `(s_b, 1/2]` and `(1/2, 1 - s_b]` of equal length `1/2 - s_b`
(by translations) and fixes the two outer ones:
`T_b(u) = u + 1/2 - s_b` for `s_b < u ≤ 1/2`, `u - 1/2 + s_b` for `1/2 < u ≤ 1 - s_b`,
and `u` otherwise. We work first with a real cut point `s ∈ [0, 1/2]` and specialize
to `s = (1 + b) / 4` in `intervalExchange`.
-/

open MeasureTheory Set
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

/-- The piecewise translation `T` on the real line with cut point `s`. -/
noncomputable def xchgReal (s u : ℝ) : ℝ :=
  if s < u ∧ u ≤ 1 / 2 then u + 1 / 2 - s
  else if 1 / 2 < u ∧ u ≤ 1 - s then u - 1 / 2 + s
  else u

theorem xchgReal_mem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    xchgReal s u ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hu0, hu1⟩ := hu
  unfold xchgReal
  split_ifs with h1 h2
  · constructor <;> linarith [h1.1, h1.2]
  · constructor <;> linarith [h2.1, h2.2]
  · exact ⟨hu0, hu1⟩

theorem xchgReal_xchgReal {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) (u : ℝ) :
    xchgReal s (xchgReal s u) = u := by
  obtain ⟨hs0, hs1⟩ := hs
  by_cases h1 : s < u ∧ u ≤ 1 / 2
  · have e : xchgReal s u = u + 1 / 2 - s := by rw [xchgReal, ite_eq_left h1]
    rw [e]
    have h2 : 1 / 2 < u + 1 / 2 - s ∧ u + 1 / 2 - s ≤ 1 - s := ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have h3 : ¬ (s < u + 1 / 2 - s ∧ u + 1 / 2 - s ≤ 1 / 2) := fun h => by linarith [h.2, h1.1]
    rw [xchgReal, ite_eq_right h3, ite_eq_left h2]
    ring
  · by_cases h2 : 1 / 2 < u ∧ u ≤ 1 - s
    · have e : xchgReal s u = u - 1 / 2 + s := by rw [xchgReal, ite_eq_right h1, ite_eq_left h2]
      rw [e]
      have h3 : s < u - 1 / 2 + s ∧ u - 1 / 2 + s ≤ 1 / 2 := ⟨by linarith [h2.1], by linarith [h2.2]⟩
      rw [xchgReal, ite_eq_left h3]
      ring
    · have e : xchgReal s u = u := by rw [xchgReal, ite_eq_right h1, ite_eq_right h2]
      rw [e, e]

/-- Reflection equivariance of `T` away from the three cut points `s`, `1/2`, `1 - s`. -/
theorem xchgReal_one_sub {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) {u : ℝ}
    (h1 : u ≠ s) (h2 : u ≠ 1 / 2) (h3 : u ≠ 1 - s) :
    xchgReal s (1 - u) = 1 - xchgReal s u := by
  obtain ⟨hs0, hs1⟩ := hs
  unfold xchgReal
  rcases lt_trichotomy u s with hu | hu | hu
  · have a1 : ¬ (s < u ∧ u ≤ 1 / 2) := fun h => by linarith [h.1]
    have a2 : ¬ (1 / 2 < u ∧ u ≤ 1 - s) := fun h => by linarith [h.1]
    have a3 : ¬ (s < 1 - u ∧ 1 - u ≤ 1 / 2) := fun h => by linarith [h.2]
    have a4 : ¬ (1 / 2 < 1 - u ∧ 1 - u ≤ 1 - s) := fun h => by linarith [h.2]
    simp only [a1, a2, a3, a4, ite_false]
  · exact absurd hu h1
  · rcases lt_trichotomy u (1 / 2) with hv | hv | hv
    · have a1 : s < u ∧ u ≤ 1 / 2 := ⟨hu, hv.le⟩
      have a3 : ¬ (s < 1 - u ∧ 1 - u ≤ 1 / 2) := fun h => by linarith [h.2]
      have a4 : 1 / 2 < 1 - u ∧ 1 - u ≤ 1 - s := ⟨by linarith, by linarith⟩
      simp only [a1, a3, a4, and_self, ite_true, ite_false]
      ring
    · exact absurd hv h2
    · rcases lt_trichotomy u (1 - s) with hw | hw | hw
      · have a1 : ¬ (s < u ∧ u ≤ 1 / 2) := fun h => by linarith [h.2]
        have a2 : 1 / 2 < u ∧ u ≤ 1 - s := ⟨hv, hw.le⟩
        have a3 : s < 1 - u ∧ 1 - u ≤ 1 / 2 := ⟨by linarith, by linarith⟩
        simp only [a1, a2, a3, and_self, ite_true, ite_false]
        ring
      · exact absurd hw h3
      · have a1 : ¬ (s < u ∧ u ≤ 1 / 2) := fun h => by linarith [h.2]
        have a2 : ¬ (1 / 2 < u ∧ u ≤ 1 - s) := fun h => by linarith [h.2]
        have a3 : ¬ (s < 1 - u ∧ 1 - u ≤ 1 / 2) := fun h => by linarith [h.1]
        have a4 : ¬ (1 / 2 < 1 - u ∧ 1 - u ≤ 1 - s) := fun h => by linarith [h.1]
        simp only [a1, a2, a3, a4, ite_false]

theorem measurable_xchgReal (s : ℝ) : Measurable (xchgReal s) := by
  unfold xchgReal
  refine Measurable.ite ?_ (by fun_prop) (Measurable.ite ?_ (by fun_prop) measurable_id)
  · exact (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_le measurable_id measurable_const)
  · exact (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_le measurable_id measurable_const)

/-- The interval exchange on `[0,1]` with cut point `s` (the value is clamped to `[0,1]`, which
is inactive for `s ∈ [0,1/2]`, see `coe_xchg`). -/
noncomputable def xchg (s : ℝ) (u : I) : I :=
  Set.projIcc (0 : ℝ) 1 zero_le_one (xchgReal s u)

theorem coe_xchg {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) (u : I) :
    ((xchg s u : I) : ℝ) = xchgReal s u := by
  unfold xchg
  rw [Set.projIcc_of_mem _ (xchgReal_mem hs u.property)]

theorem measurable_xchg (s : ℝ) : Measurable (xchg s) := by
  unfold xchg
  exact continuous_projIcc.measurable.comp
    ((measurable_xchgReal s).comp continuous_subtype_val.measurable)

theorem xchg_xchg {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) (u : I) :
    xchg s (xchg s u) = u := by
  apply Subtype.ext
  rw [coe_xchg hs, coe_xchg hs, xchgReal_xchgReal hs]

theorem xchg_symm {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) {u : I}
    (h1 : (u : ℝ) ≠ s) (h2 : (u : ℝ) ≠ 1 / 2) (h3 : (u : ℝ) ≠ 1 - s) :
    xchg s (unitInterval.symm u) = unitInterval.symm (xchg s u) := by
  apply Subtype.ext
  rw [coe_xchg hs, unitInterval.coe_symm_eq, unitInterval.coe_symm_eq, coe_xchg hs]
  exact xchgReal_one_sub hs h1 h2 h3

/-- The cut point `s_b = (1 + b) / 4`. -/
noncomputable def exchangeCut (b : ℝ) : ℝ := (1 + b) / 4

theorem exchangeCut_mem {b : ℝ} (hb : b ∈ Icc (-1 : ℝ) 1) :
    exchangeCut b ∈ Icc (0 : ℝ) (1 / 2) := by
  unfold exchangeCut
  constructor <;> linarith [hb.1, hb.2]

/-- The interval exchange `T_b` of Proposition 4.2. -/
noncomputable def intervalExchange (b : ℝ) : I → I := xchg (exchangeCut b)

/-- The defining formula of `T_b`. -/
theorem coe_intervalExchange {b : ℝ} (hb : b ∈ Icc (-1 : ℝ) 1) (u : I) :
    ((intervalExchange b u : I) : ℝ) =
      if (1 + b) / 4 < u ∧ (u : ℝ) ≤ 1 / 2 then u + 1 / 2 - (1 + b) / 4
      else if 1 / 2 < (u : ℝ) ∧ (u : ℝ) ≤ 1 - (1 + b) / 4 then u - 1 / 2 + (1 + b) / 4
      else u :=
  coe_xchg (exchangeCut_mem hb) u

theorem ae_coe_ne (c : ℝ) : ∀ᵐ u : I, (u : ℝ) ≠ c := by
  rw [ae_iff]
  apply Set.Subsingleton.measure_zero
  intro a ha b hb
  apply Subtype.ext
  have ha' : (a : ℝ) = c := by simpa using ha
  have hb' : (b : ℝ) = c := by simpa using hb
  rw [ha', hb']

end Papers.OrendayLaresRockel2026XiBeta
