import Papers.Rockel2026ExactBlest.ExactBlestRho
import Papers.Rockel2026ExactBlest.ExactBlestBetaRegion

/-! Displayed exact-region formulas from exact-blest-regions.tex.
Copula uniqueness and the standalone rearrangement equality case remain separate. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
open Papers.Rockel2026XiBlest

namespace Papers.Rockel2026ExactBlest
noncomputable section
set_option maxHeartbeats 4000000

def graphGap (e : ℝ) : ℝ := (1 + e) - (2 : ℝ) ^ (-1 / 3 : ℝ) * (1 + e) ^ (4 / 3 : ℝ)

theorem graphGap_value (w : I) :
    graphGap (eta (familyA w)) = blestNu (familyA w) - eta (familyA w) := by
  have he : 1 + eta (familyA w) = 2 * (1 - (w : ℝ)) ^ 3 := by rw [eta_familyA]; ring
  have hw : 0 ≤ 1 - (w : ℝ) := sub_nonneg.mpr w.property.2
  have hp : (2 : ℝ) ^ (-1 / 3 : ℝ) * (2 : ℝ) ^ (4 / 3 : ℝ) = 2 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  unfold graphGap
  rw [he, Real.mul_rpow (by norm_num) (pow_nonneg hw 3), rpow_cube_four_thirds _ hw,
    ← mul_assoc, hp, nu_familyA, eta_familyA]
  ring

theorem graph_eta_range (w : I) (hw : (w : ℝ) ≤ 1 / 2) :
    eta (familyA w) ∈ Icc (-3 / 4 : ℝ) 1 := by
  have h := eta_mem_Icc (familyA w)
  refine ⟨?_, h.2⟩
  have hp : (1 / 2 : ℝ) ^ 3 ≤ (1 - (w : ℝ)) ^ 3 := by
    gcongr
    linarith
  rw [eta_familyA]
  norm_num at hp
  linarith

theorem etaB_range (a : I) (ha : (1 / 2 : ℝ) ≤ a) :
    etaB a ∈ Icc (-1 : ℝ) (-3 / 4) := by
  have hl := randomized_parameter_strictAnti.antitoneOn
    ⟨ha, a.property.2⟩ (show (1 : ℝ) ∈ Icc (1 / 2) 1 by norm_num) a.property.2
  have hu := randomized_parameter_strictAnti.antitoneOn
    (show (1 / 2 : ℝ) ∈ Icc (1 / 2) 1 by norm_num) ⟨ha, a.property.2⟩ ha
  norm_num [etaB] at hl hu
  constructor <;> unfold etaB <;> linarith

def randomEtaParameter (e : ℝ) : I :=
  if he : e ∈ Icc (-1 : ℝ) (-3 / 4) then (randomized_parameter_exists_unique e he).choose else 0

theorem randomEtaParameter_value (a : I) (ha : (1 / 2 : ℝ) ≤ a) :
    randomEtaParameter (etaB a) = a := by
  have he := etaB_range a ha
  rw [randomEtaParameter, dite_eq_left he]
  exact ((randomized_parameter_exists_unique (etaB a) he).choose_spec.2 a ⟨ha, rfl⟩).symm

/-- The paper's Upsilon: graph formula above -3/4, inverse-parameter formula below it. -/
def etaGap (e : ℝ) : ℝ :=
  if e < -3 / 4 then nuB (randomEtaParameter e) - etaB (randomEtaParameter e) else graphGap e

theorem etaGap_graph (w : I) (hw : (w : ℝ) ≤ 1 / 2) :
    etaGap (eta (familyA w)) = blestNu (familyA w) - eta (familyA w) := by
  rw [etaGap, ite_eq_right (not_lt.mpr (graph_eta_range w hw).1), graphGap_value]

theorem etaGap_randomized (a : I) (ha : (1 / 2 : ℝ) < a) :
    etaGap (etaB a) = nuB a - etaB a := by
  have h := randomized_parameter_strictAnti (show (1 / 2 : ℝ) ∈ Icc (1 / 2) 1 by norm_num)
    ⟨ha.le, a.property.2⟩ ha
  norm_num [etaB] at h
  have hh : etaB a < -3 / 4 := by unfold etaB; linarith
  rw [etaGap, ite_eq_left hh, randomEtaParameter_value a ha.le]

theorem etaGap_randomized_formula (a : I) (ha : (1 / 2 : ℝ) < a) :
    etaGap (etaB a) = (1 - (a : ℝ)) ^ 3 * (6 * (a : ℝ) ^ 2 + 3 * (a : ℝ) - 1) / (8 * (a : ℝ) ^ 2) := by
  have h0 : (a : ℝ) ≠ 0 := by linarith
  rw [etaGap_randomized a ha]
  unfold nuB etaB
  field_simp
  ring

theorem etaGap_bottom : etaGap (-1) = 0 := by
  have h := etaGap_randomized (1 : I) (by norm_num)
  norm_num [etaB, nuB] at h
  exact h

/-- The full fibre statement with the paper's displayed Upsilon formulas. -/
theorem eta_fibre_displayed (e n : ℝ) :
    (∃ C : Copula 2, eta C = e ∧ blestNu C = n) ↔
      e ∈ Icc (-1 : ℝ) 1 ∧ |n - e| ≤ etaGap e := by
  constructor
  · intro hc
    obtain ⟨C, he, hn⟩ := hc
    refine ⟨he ▸ eta_mem_Icc C, ?_⟩
    have hregion := (eta_fibre_complete e n).mp ⟨C, he, hn⟩
    rcases hregion with ⟨w, hw, rfl, hv⟩ | ⟨a, ha, ha1, rfl, hv⟩ | ⟨rfl, rfl⟩
    · rw [etaGap_graph w hw]
      exact abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩
    · rw [etaGap_randomized a ha]
      exact abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩
    · rw [etaGap_bottom]; norm_num
  · rintro ⟨he, hn⟩
    by_cases hg : -3 / 4 ≤ e
    · obtain ⟨w, hw, _⟩ := graph_parameter_exists_unique e ⟨hg, he.2⟩
      rw [← hw.2, etaGap_graph w hw.1] at hn
      have ha := abs_le.mp hn
      obtain ⟨C, hc, hv⟩ := (graph_fibre w hw.1 n).mpr ⟨by linarith [ha.1], by linarith [ha.2]⟩
      exact ⟨C, hc.trans hw.2, hv⟩
    · by_cases hb : e = -1
      · subst e
        rw [etaGap_bottom] at hn
        have h := abs_le.mp hn
        exact (eta_bottom_fibre n).mpr (by linarith [h.1, h.2])
      · obtain ⟨a, ha, ha1, hav⟩ := randomized_parameter_exists_open e
          ⟨lt_of_le_of_ne he.1 (Ne.symm hb), by linarith⟩
        rw [← hav, etaGap_randomized a ha] at hn
        have h := abs_le.mp hn
        obtain ⟨C, hc, hv⟩ := (randomized_fibre a ha ha1 n).mpr ⟨by linarith [h.1], by linarith [h.2]⟩
        exact ⟨C, hc.trans hav, hv⟩

theorem eta_nu_region :
    Set.range (fun C : Copula 2 => (eta C, blestNu C)) =
      {p : ℝ × ℝ | p.1 ∈ Icc (-1 : ℝ) 1 ∧ |p.2 - p.1| ≤ etaGap p.1} := by
  ext ⟨e, n⟩
  simpa only [Set.mem_range, Set.mem_ofPred_eq, Prod.mk.injEq] using eta_fibre_displayed e n

#assert_standard_axioms Papers.Rockel2026ExactBlest.graphGap_value
#assert_standard_axioms Papers.Rockel2026ExactBlest.graph_eta_range
#assert_standard_axioms Papers.Rockel2026ExactBlest.etaB_range
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomEtaParameter_value
#assert_standard_axioms Papers.Rockel2026ExactBlest.etaGap_graph
#assert_standard_axioms Papers.Rockel2026ExactBlest.etaGap_randomized
#assert_standard_axioms Papers.Rockel2026ExactBlest.etaGap_randomized_formula
#assert_standard_axioms Papers.Rockel2026ExactBlest.etaGap_bottom
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_fibre_displayed
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_nu_region

end
end Papers.Rockel2026ExactBlest
