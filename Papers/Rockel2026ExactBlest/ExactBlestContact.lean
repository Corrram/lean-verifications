import Papers.Rockel2026ExactBlest.ExactBlestBetaUniqueness

/-! Complete pointwise contact sets for the eta transport certificates. -/
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval Topology
open Papers.Rockel2026XiBlest
namespace Papers.Rockel2026ExactBlest
noncomputable section
set_option maxHeartbeats 4000000

theorem phiA_upper_closed (w x : ℝ) (hx : w ≤ x) : phiA w x = phiA1 w x := by
  by_cases h : x ≤ w
  · have he : x = w := le_antisymm h hx
    subst x
    simp [phiA, phiA0, phiA1]
  · simp only [phiA, ite_eq_right h]

theorem psiA_upper_closed (w z : ℝ) (hz : 1 - w ≤ z) : psiA w z = psiA1 w z := by
  by_cases h : z ≤ 1 - w
  · have he : z = 1 - w := le_antisymm h hz
    subst z
    simp [psiA, psiA1]
  · simp only [psiA, ite_eq_right h]

def contactA (w x z : ℝ) : Prop :=
  (x ≤ w ∧ z = 1 - x) ∨ (w ≤ x ∧ z = x - w) ∨ (w = 1 / 2 ∧ w ≤ x ∧ z = 1 / 2)

theorem graph_contact_complete (w x z : ℝ) (hw0 : 0 < w) (hw1 : w ≤ 1 / 2)
    (hx : x ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    phiA w x + psiA w z - cost (kA w) x z = 0 ↔ contactA w x z := by
  have hw : w ≠ 1 := by linarith
  have hden : 0 < 1 - w := by linarith
  have hw5 : 0 < 5 - 2 * w := by linarith
  constructor
  · intro heq
    by_cases hxc : x = w
    · subst x
      by_cases hzz : z ≤ 1 - w
      · simp only [phiA, psiA, ite_eq_left le_rfl, ite_eq_left hzz] at heq
        rw [slackA00 w w z hw] at heq
        have hh : w * z ^ 2 * (1 - w - z) = 0 := by
          have he : w * z ^ 2 * (1 - w - z) / (1 - w) = 0 := by simpa using heq
          exact (div_eq_zero_iff.mp he).resolve_right hden.ne'
        rcases mul_eq_zero.mp hh with h | h
        · have hz0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_left hw0.ne')
          exact Or.inr (Or.inl ⟨le_rfl, by linarith⟩)
        · exact Or.inl ⟨le_rfl, by linarith⟩
      · simp only [phiA, psiA, ite_eq_left le_rfl, ite_eq_right hzz] at heq
        rw [slackA01 w w z hw] at heq
        have ht : 0 < z - (1 - w) := by linarith
        have hp : 0 < 3 * (1 - w) + (5 - 2 * w) * (w - w) + (2 * w + 4) * (z - (1 - w)) := by
          simpa using (show 0 < 3 * (1 - w) + (2 * w + 4) * (z - (1 - w)) by positivity)
        have hh := sq_eq_zero_iff.mp
          ((mul_eq_zero.mp ((div_eq_zero_iff.mp heq).resolve_right (by positivity))).resolve_right hp.ne')
        exact Or.inl ⟨le_rfl, by linarith⟩
    · by_cases hzc : z = 1 - w
      · subst z
        by_cases hxx : x ≤ w
        · rw [psiA_upper_closed w (1 - w) le_rfl] at heq
          simp only [phiA, ite_eq_left hxx] at heq
          rw [slackA01 w x (1 - w) hw] at heq
          have hy : 0 ≤ w - x := sub_nonneg.mpr hxx
          have hp : 0 < 3 * (1 - w) + (5 - 2 * w) * (w - x) + (2 * w + 4) * ((1 - w) - (1 - w)) := by
            simpa using (show 0 < 3 * (1 - w) + (5 - 2 * w) * (w - x) by positivity)
          have hh := sq_eq_zero_iff.mp
            ((mul_eq_zero.mp ((div_eq_zero_iff.mp heq).resolve_right (by positivity))).resolve_right hp.ne')
          exact Or.inl ⟨hxx, by linarith⟩
        · simp only [phiA, psiA, ite_eq_right hxx, ite_eq_left le_rfl] at heq
          rw [slackA10 w x (1 - w) hw] at heq
          have hnum := (div_eq_zero_iff.mp heq).resolve_right (by positivity)
          have hh : (x - w) * (1 - 2 * w) * (1 - x) ^ 2 = 0 := by nlinarith
          rcases mul_eq_zero.mp hh with h | h
          · have hxw : x - w ≠ 0 := by linarith
            have hh := (mul_eq_zero.mp h).resolve_left hxw
            exact Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩)
          · have hh := sq_eq_zero_iff.mp h
            exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
      · have h := graph_contact w x z hw0.le hw1 hx hz hxc hzc heq
        by_cases hxx : x ≤ w
        · rw [ite_eq_left hxx] at h
          exact Or.inl ⟨hxx, h⟩
        · rw [ite_eq_right hxx] at h
          exact Or.inr (Or.inl ⟨by linarith, h⟩)
  · rintro (⟨hxx, rfl⟩ | ⟨hxx, rfl⟩ | ⟨rfl, hxx, rfl⟩)
    · rw [psiA_upper_closed w (1 - x) (by linarith)]
      simp only [phiA, ite_eq_left hxx]
      rw [slackA01 w x (1 - x) hw]
      ring
    · rw [phiA_upper_closed w x hxx]
      have hzz : x - w ≤ 1 - w := by linarith [hx.2]
      simp only [psiA, ite_eq_left hzz]
      rw [slackA10 w x (x - w) hw]
      ring
    · rw [phiA_upper_closed (1 / 2) x hxx]
      have hzz : (1 / 2 : ℝ) ≤ 1 - 1 / 2 := by norm_num
      simp only [psiA, ite_eq_left hzz]
      rw [slackA10 (1 / 2) x (1 / 2) (by norm_num)]
      norm_num

theorem phiB_upper_closed (a x : ℝ) (hx : a ≤ x) : phiB a x = phiB1 a x := by
  by_cases h : x ≤ a
  · have he : x = a := le_antisymm h hx
    subst x
    simp [phiB, phiB0, phiB1]
  · simp only [phiB, ite_eq_right h]

theorem randomized_contact_complete (a x z : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    phiB a x + psiB a z - cost (kB a) x z = 0 ↔ x = randomRankReal a z := by
  have ha0 : 0 < a := by linarith
  have hn0 := ha0.ne'
  have hn1 := ha1.ne
  have ha2 : 0 < 2 * a - 1 := by linarith
  have hn2 := ha2.ne'
  have ha3 : 0 < 3 * a - 1 := by linarith
  have hden : 0 < 1 - a := by linarith
  have hc0 : 0 < cutB a := by unfold cutB; positivity
  have hcv : 2 * a * cutB a = 1 - a := by unfold cutB; field_simp
  have hcut : cutB a ≤ 1 - a := by
    unfold cutB
    apply (div_le_iff₀ (by positivity : 0 < 2 * a)).mpr
    nlinarith [mul_nonneg hden.le ha2.le]
  have hz0 := hz.1
  constructor
  · intro heq
    by_cases hxa : x = a
    · subst x
      by_cases hc : z ≤ cutB a
      · simp only [phiB, psiB, ite_eq_left le_rfl, ite_eq_left hc] at heq
        rw [slackB00 a a z hn1] at heq
        have hr : 0 ≤ 1 - a - 2 * a * z := by
          have := (le_div_iff₀ (by positivity : 0 < 2 * a)).mp hc
          nlinarith
        have hp : 0 < (1 - a) * (2 * a - 1) + (1 + a) * (1 - a - 2 * a * z) := by positivity
        have hh : 2 * a * z ^ 2 * ((1 - a) * (2 * a - 1) + (1 + a) * (1 - a - 2 * a * z)) = 0 := by
          have he : 2 * a * z ^ 2 * ((1 - a) * (2 * a - 1) + (1 + a) * (1 - a - 2 * a * z)) / (3 * (1 - a)) = 0 := by simpa using heq
          exact (div_eq_zero_iff.mp he).resolve_right (by positivity)
        have hh' := (mul_eq_zero.mp hh).resolve_right hp.ne'
        have hzv := sq_eq_zero_iff.mp ((mul_eq_zero.mp hh').resolve_left (by positivity))
        rw [randomRankReal, ite_eq_left hc, hzv]
        ring
      · by_cases hm : z ≤ 1 - a
        · simp only [phiB, psiB, ite_eq_left le_rfl, ite_eq_right hc, ite_eq_left hm] at heq
          rw [slackB01 a a z hn0 hn1 hn2] at heq
          have hr : 0 ≤ 2 * a * z - (1 - a) := by
            have := (div_lt_iff₀ (by positivity : 0 < 2 * a)).mp (lt_of_not_ge hc)
            nlinarith
          have hp : 0 < (1 - a) * (2 * a - 1) + (3 * a - 1) * (2 * a * z - (1 - a)) := by positivity
          have hh : 2 * a * (1 - a - z) ^ 2 * ((1 - a) * (2 * a - 1) + (3 * a - 1) * (2 * a * z - (1 - a))) = 0 := by
            have he : 2 * a * (1 - a - z) ^ 2 * ((1 - a) * (2 * a - 1) + (3 * a - 1) * (2 * a * z - (1 - a))) /
                (3 * (1 - a) * (2 * a - 1) ^ 2) = 0 := by simpa using heq
            exact (div_eq_zero_iff.mp he).resolve_right (by positivity)
          have hh' := (mul_eq_zero.mp hh).resolve_right hp.ne'
          have hzv := sq_eq_zero_iff.mp ((mul_eq_zero.mp hh').resolve_left (by positivity))
          rw [randomRankReal, ite_eq_right hc, ite_eq_left hm]
          apply (eq_div_iff hn2).mpr
          nlinarith
        · simp only [phiB, psiB, ite_eq_left le_rfl, ite_eq_right hc, ite_eq_right hm] at heq
          rw [slackB02 a a z hn0 hn1 hn2] at heq
          have ht : 0 < z - (1 - a) := by linarith
          have hp : 0 < 3 * a * (1 - a) + 2 * (a - a) + (3 * a + 1) * (z - (1 - a)) := by
            simpa using (show 0 < 3 * a * (1 - a) + (3 * a + 1) * (z - (1 - a)) by positivity)
          have hh := sq_eq_zero_iff.mp
            ((mul_eq_zero.mp ((div_eq_zero_iff.mp heq).resolve_right (by positivity))).resolve_right hp.ne')
          rw [randomRankReal, ite_eq_right hc, ite_eq_right hm]
          linarith
    · by_cases hzc : z = cutB a
      · subst z
        by_cases hxx : x ≤ a
        · simp only [phiB, psiB, ite_eq_left hxx, ite_eq_left le_rfl] at heq
          rw [slackB00 a x (cutB a) hn1] at heq
          have hy : 0 ≤ a - x := by linarith
          have ht : 0 ≤ 1 - a - cutB a := by linarith
          have hr : 0 ≤ 1 - a - 2 * a * cutB a := by linarith
          have hp : 0 < 2 * a * (cutB a) ^ 2 * ((1 - a) * (2 * a - 1) + (1 + a) * (1 - a - 2 * a * cutB a)) /
              (3 * (1 - a)) + 2 * ((1 - a - cutB a) * a * cutB a * (a - x) +
                (1 - a - cutB a + a * cutB a) * (a - x) ^ 2 / 2 + (a - x) ^ 3 / 3) / (1 - a) := by positivity
          linarith
        · simp only [phiB, psiB, ite_eq_right hxx, ite_eq_left le_rfl] at heq
          rw [slackB10 a x (cutB a) hn0 hn1, hcv] at heq
          have hnum := (div_eq_zero_iff.mp heq).resolve_right (by positivity)
          have hh : (x - 1) ^ 2 * ((2 * a - 1) * (1 - x)) = 0 := by nlinarith
          have hx1 : x = 1 := by
            rcases mul_eq_zero.mp hh with h | h
            · have := sq_eq_zero_iff.mp h; linarith
            · have := (mul_eq_zero.mp h).resolve_left hn2; linarith
          rw [randomRankReal, ite_eq_left le_rfl, hcv, hx1]
          ring
      · exact randomized_contact a x z ha ha1 hx hz hxa hzc heq
  · intro he
    by_cases hc : z ≤ cutB a
    · rw [randomRankReal, ite_eq_left hc] at he
      have hxa : a ≤ x := by nlinarith
      rw [phiB_upper_closed a x hxa]
      simp only [psiB, ite_eq_left hc]
      rw [slackB10 a x z hn0 hn1, he]
      ring
    · by_cases hm : z ≤ 1 - a
      · rw [randomRankReal, ite_eq_right hc, ite_eq_left hm] at he
        have hxa : a ≤ x := by
          rw [he]
          apply (le_div_iff₀ ha2).mpr
          nlinarith
        rw [phiB_upper_closed a x hxa]
        simp only [psiB, ite_eq_right hc, ite_eq_left hm]
        rw [slackB11 a x z hn0 hn1 hn2]
        have hh : x * (2 * a - 1) + 2 * a * z - a = 0 := by
          have := (eq_div_iff hn2).mp he
          nlinarith
        rw [hh]
        simp
      · rw [randomRankReal, ite_eq_right hc, ite_eq_right hm] at he
        have hxa : x ≤ a := by linarith
        simp only [phiB, psiB, ite_eq_left hxa, ite_eq_right hc, ite_eq_right hm]
        rw [slackB02 a x z hn0 hn1 hn2, he]
        ring

#assert_standard_axioms Papers.Rockel2026ExactBlest.phiB_upper_closed
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomized_contact_complete

#assert_standard_axioms Papers.Rockel2026ExactBlest.phiA_upper_closed
#assert_standard_axioms Papers.Rockel2026ExactBlest.psiA_upper_closed
#assert_standard_axioms Papers.Rockel2026ExactBlest.graph_contact_complete

end
end Papers.Rockel2026ExactBlest
