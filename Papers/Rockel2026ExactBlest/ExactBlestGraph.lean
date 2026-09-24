import Papers.Rockel2026ExactBlest.ExactBlest

/-! The graph-regime fibres of the (eta,nu) region in exact-blest-regions.tex. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
open Papers.Rockel2026XiBlest

namespace Papers.Rockel2026ExactBlest
noncomputable section
set_option maxHeartbeats 1600000

theorem integral_potentialsA (w : I) (hw : (w : ℝ) ≤ 1 / 2) :
    (∫ u : I, phiA w u) + (∫ u : I, psiA w u) =
      ((1 + kA w) * blestNu (familyA w) - 2 * kA w * eta (familyA w) + 2 * (1 - kA w)) / 12 := by
  have hn : (w : ℝ) ≠ 1 := by linarith
  have hp := integral_unit_piecewise (phiA0 w) (phiA1 w)
    (by unfold phiA0 antiPhi; fun_prop) (by unfold phiA1 graphPhi; fun_prop) w w.property
  have hq := integral_unit_piecewise (psiA0 w) (psiA1 w)
    (by unfold psiA0 linearPsi; fun_prop) (by unfold psiA1 linearPsi; fun_prop) (1 - (w : ℝ))
      ⟨by linarith [w.property.2], by linarith [w.property.1]⟩
  change (∫ u : I, phiA w u) = _ at hp
  change (∫ u : I, psiA w u) = _ at hq
  rw [hp, hq, nu_familyA, eta_familyA]
  have hp0 : phiA0 w = fun x : ℝ => (-(2 + kA w) / 3) * x ^ 3 +
      (1 + kA w) * x ^ 2 + (-kA w) * x + (-antiPhi (kA w) w) := by
    funext x; unfold phiA0 antiPhi; ring
  have hp1 : phiA1 w = fun x : ℝ => ((2 - kA w) / 3) * x ^ 3 +
      ((w : ℝ) * (kA w - 1)) * x ^ 2 + (-kA w * (w : ℝ) ^ 2) * x + (-graphPhi w w) := by
    funext x; unfold phiA1 graphPhi; ring
  have hq0 : psiA0 w = fun x : ℝ => ((1 - 2 * kA w) / 3) * x ^ 3 +
      ((w : ℝ) * (1 - kA w)) * x ^ 2 + (w : ℝ) ^ 2 * x + 0 := by
    funext x; unfold psiA0 linearPsi; ring
  have hq1 : psiA1 w = fun x : ℝ => ((1 + 2 * kA w) / 3) * x ^ 3 +
      (-(1 + kA w)) * x ^ 2 + 1 * x +
        (psiA0 w (1 - (w : ℝ)) - linearPsi (kA w) (-1) 1 (1 - (w : ℝ))) := by
    funext x; unfold psiA1 linearPsi; ring
  rw [hp0, hp1, hq0, hq1, integral_poly3, integral_poly3, integral_poly3, integral_poly3]
  unfold antiPhi graphPhi psiA0 linearPsi kA
  field_simp
  ring

theorem graph_support (C : Copula 2) (w : I) (hw : (w : ℝ) ≤ 1 / 2) :
    (1 + kA w) * blestNu C - 2 * kA w * eta C ≤
      (1 + kA w) * blestNu (familyA w) - 2 * kA w * eta (familyA w) := by
  let D := C.survivalCopula
  have hp := integrable_phiA D w 0
  have hq := integrable_psiA D w 1
  have hi : Integrable (fun x : Fin 2 → I => cost (kA w) (x 0) (x 1)) D.toMeasure :=
    Copula.integrable_continuous_cube _ (by unfold cost; fun_prop)
  have h := integral_mono hi (hp.add hq)
    (fun x => dualA w (x 0) (x 1) w.property.1 hw (x 0).property (x 1).property)
  simp only [Pi.add_apply] at h
  rw [integral_add hp hq, D.integral_eval 0 _ (measurable_phiA w),
    D.integral_eval 1 _ (measurable_psiA w), integral_potentialsA w hw] at h
  have hs := support_moment_survival C (kA w)
  change (1 + kA w) * blestNu C - 2 * kA w * eta C =
    12 * (∫ x, cost (kA w) (x 0) (x 1) ∂D.toMeasure) - 2 * (1 - kA w) at hs
  linarith

theorem nu_le_familyA (C : Copula 2) (w : I) (hw : (w : ℝ) ≤ 1 / 2)
    (he : eta C = eta (familyA w)) : blestNu C ≤ blestNu (familyA w) := by
  have h := graph_support C w hw
  rw [he] at h
  have hk : 0 < 1 + kA w := by
    have hd : 0 < 1 - (w : ℝ) := by linarith
    have hw0 := w.property.1
    unfold kA
    positivity
  by_contra hn
  have hd : 0 < blestNu C - blestNu (familyA w) := by linarith
  have hm := mul_pos hk hd
  nlinarith

/-- Exact fibres for the graph regime, in the paper's parameter w; uniqueness is not asserted. -/
theorem graph_fibre (w : I) (hw : (w : ℝ) ≤ 1 / 2) (n : ℝ) :
    (∃ C : Copula 2, eta C = eta (familyA w) ∧ blestNu C = n) ↔
      n ∈ Icc (2 * eta (familyA w) - blestNu (familyA w)) (blestNu (familyA w)) := by
  constructor
  · rintro ⟨C, he, rfl⟩
    have hu := nu_le_familyA C w hw he
    have hl := nu_le_familyA C.transpose w hw ((eta_transpose C).trans he)
    rw [nu_transpose, he] at hl
    exact ⟨by linarith, hu⟩
  · intro hn
    have hc : Continuous (fun t : I => blestNu ((familyA w).mix (familyA w).transpose t)) := by
      simp_rw [blest_mix]
      fun_prop
    obtain ⟨t, ht⟩ := Verification.exists_unitInterval_eq hc
      (z := n) (by simp only [blest_mix]; norm_num; rw [nu_transpose]; exact hn.1)
      (by simp only [blest_mix]; norm_num; exact hn.2)
    refine ⟨(familyA w).mix (familyA w).transpose t, ?_, ht⟩
    rw [eta_mix, eta_transpose]
    ring

theorem graph_parameter_strictAnti : StrictAntiOn (fun w : ℝ => 2 * (1 - w) ^ 3 - 1) (Icc 0 (1 / 2)) := by
  intro x hx y hy hxy
  have hp : (1 - y) ^ 3 < (1 - x) ^ 3 := by
    gcongr
    linarith [hy.2]
  linarith

theorem graph_parameter_exists_unique (e : ℝ) (he : e ∈ Icc (-3 / 4 : ℝ) 1) :
    ∃! w : I, (w : ℝ) ≤ 1 / 2 ∧ eta (familyA w) = e := by
  have hc : Continuous (fun t : I => -(2 * (1 - (t : ℝ) / 2) ^ 3 - 1)) := by fun_prop
  obtain ⟨t, ht⟩ := Verification.exists_unitInterval_eq hc (z := -e)
    (by norm_num; linarith [he.2]) (by norm_num; linarith [he.1])
  let w : I := ⟨(t : ℝ) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩
  have hw : (w : ℝ) ≤ 1 / 2 := by dsimp [w]; linarith [t.property.2]
  have hwv : eta (familyA w) = e := by rw [eta_familyA]; change 2 * (1 - (t : ℝ) / 2) ^ 3 - 1 = e; linarith
  refine ⟨w, ⟨hw, hwv⟩, ?_⟩
  intro v hv
  apply Subtype.ext
  apply graph_parameter_strictAnti.injOn ⟨v.property.1, hv.1⟩ ⟨w.property.1, hw⟩
  dsimp only
  rw [← eta_familyA v, ← eta_familyA w, hv.2, hwv]

theorem rho_eta_lower_attained : ∃ C : Copula 2, C.spearmanRho - eta C = -27 / 128 := by
  obtain ⟨C, h⟩ := rho_eta_attained
  refine ⟨C.survivalCopula, ?_⟩
  rw [Copula.spearmanRho_survivalCopula, eta_survival]
  linarith

#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_potentialsA
#assert_standard_axioms Papers.Rockel2026ExactBlest.graph_support
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_le_familyA
#assert_standard_axioms Papers.Rockel2026ExactBlest.graph_fibre
#assert_standard_axioms Papers.Rockel2026ExactBlest.graph_parameter_strictAnti
#assert_standard_axioms Papers.Rockel2026ExactBlest.graph_parameter_exists_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_eta_lower_attained

end
end Papers.Rockel2026ExactBlest
