import Papers.Rockel2026ExactBlest.ExactBlestQuadratic
import Papers.Rockel2026ExactBlest.ExactBlestPotentials
import Papers.Rockel2026ExactBlest.ExactBlestRegions

/-! Direct proofs of the full rho parameter bijection and the randomized-gap calculus
used in exact-blest-regions.tex. -/
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval Topology
open Papers.Rockel2026XiBlest

namespace Papers.Rockel2026ExactBlest
noncomputable section
set_option maxHeartbeats 4000000

theorem continuous_rhoFullFamily_parameter :
    Continuous (fun c : I => (rhoFullFamily c).spearmanRho) := by
  have hf : (fun c : I => (rhoFullFamily c).spearmanRho) =
      (fun c : I => if (c : ℝ) ≤ 1 / 2 then 1 - 8 * (c : ℝ) ^ 3
        else 8 * (1 - (c : ℝ)) ^ 3 - 1) :=
    funext fun c => (rhoFullFamily_values c).1
  rw [hf]
  apply Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) continuous_const
  intro c hc
  change (c : ℝ) = 1 / 2 at hc
  rw [hc]
  norm_num

theorem rhoFullFamily_parameter_endpoints :
    (rhoFullFamily 0).spearmanRho = 1 ∧ (rhoFullFamily 1).spearmanRho = -1 := by
  rw [(rhoFullFamily_values 0).1, (rhoFullFamily_values 1).1]
  norm_num

theorem rhoFullFamily_parameter_strictAnti :
    StrictAnti (fun c : I => (rhoFullFamily c).spearmanRho) := by
  intro x y hxy
  have hxy' : (x : ℝ) < y := hxy
  have hcub : StrictMono (fun t : ℝ => t ^ 3) := (by decide : Odd 3).strictMono_pow
  change (rhoFullFamily y).spearmanRho < (rhoFullFamily x).spearmanRho
  rw [(rhoFullFamily_values x).1, (rhoFullFamily_values y).1]
  by_cases hx : (x : ℝ) ≤ 1 / 2 <;> by_cases hy : (y : ℝ) ≤ 1 / 2
  · rw [ite_eq_left hx, ite_eq_left hy]
    linarith [hcub hxy']
  · rw [ite_eq_left hx, ite_eq_right hy]
    have h1 := hcub.monotone hx
    have h2 := hcub (show 1 - (y : ℝ) < 1 / 2 by linarith)
    norm_num at h1 h2
    linarith
  · exact (hx (by linarith)).elim
  · rw [ite_eq_right hx, ite_eq_right hy]
    linarith [hcub (show 1 - (y : ℝ) < 1 - (x : ℝ) by linarith)]

theorem rhoFullFamily_parameter_exists_unique (r : ℝ) (hr : r ∈ Icc (-1 : ℝ) 1) :
    ∃! c : I, (rhoFullFamily c).spearmanRho = r := by
  obtain ⟨c, hc⟩ := Verification.exists_unitInterval_eq
    continuous_rhoFullFamily_parameter.neg (z := -r)
    (by change -(rhoFullFamily 0).spearmanRho ≤ -r
        rw [rhoFullFamily_parameter_endpoints.1]; linarith [hr.2])
    (by change -r ≤ -(rhoFullFamily 1).spearmanRho
        rw [rhoFullFamily_parameter_endpoints.2]; linarith [hr.1])
  have hv : (rhoFullFamily c).spearmanRho = r := neg_injective hc
  refine ⟨c, hv, ?_⟩
  intro d hd
  exact rhoFullFamily_parameter_strictAnti.injective (hd.trans hv.symm)

theorem rhoFullFamily_parameter_range :
    Set.range (fun c : I => (rhoFullFamily c).spearmanRho) = Icc (-1 : ℝ) 1 := by
  ext r
  constructor
  · rintro ⟨c, rfl⟩
    exact (rhoFullFamily c).spearmanRho_mem_Icc
  · intro hr
    obtain ⟨c, hc, _⟩ := rhoFullFamily_parameter_exists_unique r hr
    exact ⟨c, hc⟩

theorem rhoFullFamily_on_boundary (c : I) :
    blestNu (rhoFullFamily c) = rhoBoundary (rhoFullFamily c).spearmanRho := by
  unfold rhoFullFamily
  split_ifs
  · rw [(rho_family_values _).1, (rho_family_values _).2, rhoBoundary_positive]
  · rw [Copula.spearmanRho_reflect_first, nu_reflect_first,
      (rho_family_values _).1, (rho_family_values _).2, rhoBoundary_negative]

/-- The manuscript's Upsilon(e_a), extended algebraically to real a. -/
def randomGap (a : ℝ) : ℝ := nuB a - etaB a

theorem hasDerivAt_nuB (a : ℝ) (ha : a ≠ 0) :
    HasDerivAt nuB (-((1 - a) ^ 2 * (3 * a ^ 2 + 2 * a + 1)) / a ^ 2) a := by
  convert (hasDerivAt_const a (-1 : ℝ)).add
    ((((hasDerivAt_id a).const_add 1).mul
      (((hasDerivAt_const a (1 : ℝ)).sub (hasDerivAt_id a)).pow 3)).div
      (hasDerivAt_id a) ha) using 1
  · ext y; rfl
  · dsimp
    field_simp
    ring

theorem hasDerivAt_randomGap (a : ℝ) (ha : a ≠ 0) :
    HasDerivAt randomGap
      (-((1 - a) ^ 2 * (3 * a - 1) * (3 * a ^ 2 + 2 * a + 1)) / (4 * a ^ 3)) a := by
  have h := (hasDerivAt_nuB a ha).sub (hasDerivAt_etaB a ha)
  have he : -((1 - a) ^ 2 * (3 * a ^ 2 + 2 * a + 1)) / a ^ 2 -
      -((1 - a) ^ 2 * (1 + a) * (3 * a ^ 2 + 2 * a + 1)) / (4 * a ^ 3) =
      -((1 - a) ^ 2 * (3 * a - 1) * (3 * a ^ 2 + 2 * a + 1)) / (4 * a ^ 3) := by
    field_simp
    ring
  rw [he] at h
  exact h

theorem deriv_randomGap_neg (a : ℝ) (ha : 1 / 2 ≤ a) (ha1 : a < 1) :
    deriv randomGap a < 0 := by
  have ha0 : 0 < a := by linarith
  rw [(hasDerivAt_randomGap a ha0.ne').deriv]
  have h1 : 0 < 1 - a := by linarith
  have h2 : 0 < 3 * a - 1 := by linarith
  have h3 : 0 < 3 * a ^ 2 + 2 * a + 1 := by positivity
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (by positivity)

theorem randomGap_strictAnti : StrictAntiOn randomGap (Icc (1 / 2 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · intro a ha
    exact (hasDerivAt_randomGap a (by linarith [ha.1])).continuousAt.continuousWithinAt
  · intro a ha
    rw [interior_Icc] at ha
    exact deriv_randomGap_neg a ha.1.le ha.2

theorem randomGap_endpoints : randomGap (1 / 2) = 1 / 8 ∧ randomGap 1 = 0 := by
  norm_num [randomGap, nuB, etaB]

theorem randomGap_bounds (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1) :
    0 < randomGap a ∧ randomGap a < 1 / 8 := by
  have hl := randomGap_strictAnti ⟨ha.1.le, ha.2.le⟩
    (show (1 : ℝ) ∈ Icc (1 / 2) 1 by norm_num) ha.2
  have hu := randomGap_strictAnti (show (1 / 2 : ℝ) ∈ Icc (1 / 2) 1 by norm_num)
    ⟨ha.1.le, ha.2.le⟩ ha.1
  rw [randomGap_endpoints.2] at hl
  rw [randomGap_endpoints.1] at hu
  exact ⟨hl, hu⟩

theorem etaGap_randomized_bounds (a : I) (ha : 1 / 2 < (a : ℝ)) (ha1 : (a : ℝ) < 1) :
    0 < etaGap (etaB a) ∧ etaGap (etaB a) < 1 / 8 := by
  rw [etaGap_randomized a ha]
  exact randomGap_bounds a ⟨ha, ha1⟩

theorem hasDerivAt_etaGap_randomized (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1) :
    HasDerivAt (fun b : ℝ => etaGap (etaB b))
      (-((1 - a) ^ 2 * (3 * a - 1) * (3 * a ^ 2 + 2 * a + 1)) / (4 * a ^ 3)) a := by
  apply (hasDerivAt_randomGap a (by linarith)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ha ha1] with b hb
  exact etaGap_randomized ⟨b, by constructor <;> linarith [hb.1, hb.2]⟩ hb.1

theorem etaGap_join : etaGap (-3 / 4) = 1 / 8 := by
  have h := etaGap_graph Copula.unitHalf (by norm_num [Copula.unitHalf])
  norm_num [eta_familyA, nu_familyA, Copula.unitHalf] at h
  simpa only [neg_div] using h

#assert_standard_axioms Papers.Rockel2026ExactBlest.continuous_rhoFullFamily_parameter
#assert_standard_axioms Papers.Rockel2026ExactBlest.rhoFullFamily_parameter_endpoints
#assert_standard_axioms Papers.Rockel2026ExactBlest.rhoFullFamily_parameter_strictAnti
#assert_standard_axioms Papers.Rockel2026ExactBlest.rhoFullFamily_parameter_exists_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.rhoFullFamily_parameter_range
#assert_standard_axioms Papers.Rockel2026ExactBlest.rhoFullFamily_on_boundary
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_nuB
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_randomGap
#assert_standard_axioms Papers.Rockel2026ExactBlest.deriv_randomGap_neg
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomGap_strictAnti
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomGap_endpoints
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomGap_bounds
#assert_standard_axioms Papers.Rockel2026ExactBlest.etaGap_randomized_bounds
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_etaGap_randomized
#assert_standard_axioms Papers.Rockel2026ExactBlest.etaGap_join

end
end Papers.Rockel2026ExactBlest
