import Papers.AnsariRockelSteinmassl2026RhoGamma.Source.Bridge

/-! # Proofs of the compiled claims

Theorem 1.1 (the region and the endpoints of `ρ̄`), Corollary 2.1 (the elementary
arc), Proposition 2.3 (the largest discrepancy) and Corollary 2.4 (the sign
thresholds), and the well-definedness of every definition, proved through
`Bridge` from the companion development of the paper. The article states these
results without a compiled proof, so the citation audit does not restrict
these proofs. -/

namespace Papers.AnsariRockelSteinmassl2026RhoGamma.Source.Proofs
open Papers.AnsariRockelSteinmassl2026RhoGamma.Source Papers.AnsariRockelSteinmassl2026RhoGamma.Source.Bridge
open Proofread MeasureTheory ProbabilityTheory Set
open scoped unitInterval
open Papers.AnsariRockelSteinmassl2026RhoGamma (region upperRho exact_region upperRho_endpoints
  region_compact region_convex region_centrally_symmetric upperRho_continuous upperRho_concave upperRho_strictMono
  elementary_upper_boundary elementary_endpoint_constants abs_rho_sub_gamma_le maximal_discrepancy_attained
  zero_gamma_slice zero_rho_slice)

/-! ## Definitions -/

theorem defined0 : wellDefined0 := trivial

theorem defined1 : wellDefined1 := by
  intro F hF
  obtain ⟨K, rfl⟩ := exists_of_copulas hF
  exact ⟨Papers.Common.integrable_section (Papers.Common.continuous_cdfOf K),
    Papers.Common.integrable_integral (Papers.Common.continuous_cdfOf K)⟩

theorem defined2 : wellDefined2 := by
  intro F hF
  obtain ⟨K, rfl⟩ := exists_of_copulas hF
  refine ⟨fun x => ⟨by linarith [x.2.2], by linarith [x.2.1]⟩, ?_⟩
  apply Papers.Common.integrable_of_continuous
  have hc := Papers.Common.continuous_cdfOf K
  have h1 : Continuous fun x : I => cdfOf K x x := hc.comp (continuous_id.prodMk continuous_id)
  have hs : Continuous fun x : I => (1 : ℝ) - (x : ℝ) := continuous_const.sub continuous_subtype_val
  have hp : Continuous fun x : I => Set.projIcc (0 : ℝ) 1 zero_le_one (1 - (x : ℝ)) :=
    (continuous_projIcc : Continuous (Set.projIcc (0 : ℝ) 1 zero_le_one)).comp hs
  have h2 : Continuous fun x : I => cdfOf K x (Set.projIcc (0 : ℝ) 1 zero_le_one (1 - (x : ℝ))) :=
    hc.comp (continuous_id.prodMk hp)
  exact h1.add h2

theorem defined3 : wellDefined3 := by unfold wellDefined3; definedness []

theorem defined4 : wellDefined4 := by
  intro g hg
  refine ⟨by definedness [], upperRho g, upperRho_isMax g hg, ?_⟩
  rintro y ⟨hy, hmax⟩
  exact le_antisymm ((upperRho_isMax g hg).2 y hy) (hmax _ (upperRho_isMax g hg).1)

theorem defined5 : wellDefined5 := by unfold wellDefined5; norm_num
theorem defined6 : wellDefined6 := by unfold wellDefined6; norm_num
theorem defined7 : wellDefined7 := by unfold wellDefined7; norm_num
theorem defined8 : wellDefined8 := by unfold wellDefined8; norm_num
theorem defined9 : wellDefined9 := by unfold wellDefined9; norm_num
theorem defined10 : wellDefined10 := by unfold wellDefined10; norm_num

/-! ## Theorem 1.1 -/

theorem proof0 : obligation0 := by
  refine ⟨by unfold meaningful0; definedness [], fun r g => ?_⟩
  rw [Omega_iff, exact_region]
  constructor
  · rintro ⟨hg, h1, h2⟩
    refine ⟨⟨hg.1, hg.2⟩, ?_, ?_⟩
    · rw [rhoBar_eq (-g) ⟨by linarith [hg.2], by linarith [hg.1]⟩]; exact h1
    · rw [rhoBar_eq g ⟨hg.1, hg.2⟩]; exact h2
  · rintro ⟨hg, h1, h2⟩
    rw [rhoBar_eq (-g) ⟨by linarith [hg.2], by linarith [hg.1]⟩] at h1
    rw [rhoBar_eq g hg] at h2
    exact ⟨⟨hg.1, hg.2⟩, h1, h2⟩

theorem proof1 : obligation1 := by
  refine ⟨trivial, ?_, ?_, ?_⟩
  · unfold Prelude.compact2; rw [Omega_set]; exact region_compact
  · unfold Prelude.convex2; rw [Omega_set]; exact region_convex
  · intro r g h
    rw [Omega_iff] at h ⊢
    exact region_centrally_symmetric h

theorem rhoBar_eqOn : EqOn upperRho rhoBar (Icc (-1) 1) := fun g hg => (rhoBar_eq g ⟨hg.1, hg.2⟩).symm

theorem proof2 : obligation2 := by
  refine ⟨trivial, ?_, ?_, ?_⟩
  · exact upperRho_continuous.congr rhoBar_eqOn.symm
  · exact upperRho_concave.congr rhoBar_eqOn
  · intro a ha b hb hab
    rw [← rhoBar_eqOn ha, ← rhoBar_eqOn hb]
    exact upperRho_strictMono ha hb hab

theorem proof3 : obligation3 := by
  refine ⟨by unfold meaningful3; norm_num, ?_⟩
  unfold claim3
  rw [rhoBar_eq (-1) (by norm_num)]
  exact upperRho_endpoints.1

theorem proof4 : obligation4 := by
  refine ⟨by unfold meaningful4; norm_num, ?_⟩
  unfold claim4
  rw [rhoBar_eq 1 (by norm_num)]
  exact upperRho_endpoints.2

/-! ## Corollary 2.1 -/

theorem gStar_lt_one : gStar < 1 := by
  rw [gStar_eq]
  unfold Papers.AnsariRockelSteinmassl2026RhoGamma.elementaryGStar
  have := Real.sqrt_nonneg 3
  rw [div_lt_one (by norm_num)]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

theorem proof5 : obligation5 := by
  refine ⟨?_, fun g hg => ?_⟩
  · unfold meaningful5
    intro g hg
    have := gStar_lt_one
    refine ⟨⟨hg.1, by linarith [hg.2]⟩, ⟨?_, by norm_num⟩, by norm_num⟩
    rw [gStar_eq] at hg
    unfold Papers.AnsariRockelSteinmassl2026RhoGamma.elementaryGStar at hg
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), hg.2]
  · have h1 := gStar_lt_one
    rw [rhoBar_eq g ⟨hg.1, by linarith [hg.2]⟩]
    have hmem : g ∈ Icc (-1) (Copula.RankRegion.RhoGamma.contactGamma 1) := by
      rw [elementary_endpoint_constants.2, ← gStar_eq]; exact ⟨hg.1, hg.2⟩
    rw [elementary_upper_boundary hmem, rpow_half]

/-! ## Proposition 2.3 -/

theorem discrepancy_values_iff (y : ℝ) :
    (∃ F, copulas F ∧ |rho F - gamma F| = y) ↔ ∃ K : Copula 2, |K.spearmanRho - K.giniGamma| = y := by
  constructor
  · rintro ⟨F, hF, hy⟩
    obtain ⟨K, rfl⟩ := exists_of_copulas hF
    exact ⟨K, by rw [← rho_cdfOf, ← gamma_cdfOf]; exact hy⟩
  · rintro ⟨K, hy⟩
    exact ⟨cdfOf K, copulas_cdfOf K, by rw [rho_cdfOf, gamma_cdfOf]; exact hy⟩

theorem discrepancy_isMax :
    (∃ F, copulas F ∧ |rho F - gamma F| = Delta0) ∧
      ∀ y, (∃ F, copulas F ∧ |rho F - gamma F| = y) → y ≤ Delta0 := by
  obtain ⟨C, hC, -⟩ := maximal_discrepancy_attained
  rw [Delta0_eq]
  refine ⟨(discrepancy_values_iff _).2 ⟨C, hC⟩, fun y hy => ?_⟩
  obtain ⟨K, rfl⟩ := (discrepancy_values_iff y).1 hy
  exact abs_rho_sub_gamma_le K

theorem proof6 : obligation6 := by
  refine ⟨?_, ?_⟩
  · unfold meaningful6
    refine ⟨by definedness [], Delta0, discrepancy_isMax, ?_⟩
    rintro y ⟨hy, hmax⟩
    exact le_antisymm (discrepancy_isMax.2 y hy) (hmax _ discrepancy_isMax.1)
  · refine epsilon_eq_of_unique ?_ ?_
    · exact discrepancy_isMax
    rintro y ⟨hy, hmax⟩
    exact le_antisymm (discrepancy_isMax.2 y hy) (hmax _ discrepancy_isMax.1)

/-! ## Corollary 2.4 -/

theorem proof7 : obligation7 := by
  refine ⟨by unfold meaningful7; definedness [], fun r => ?_, fun g => ?_⟩
  · have h := zero_gamma_slice r
    rw [← Omega_iff] at h
    rw [r0_eq, ← abs_le]
    rw [← h]
    constructor
    · rintro ⟨F, ⟨hF, hg⟩, hr⟩
      exact ⟨F, hF, hr.symm, hg⟩
    · rintro ⟨F, hF, hr, hg⟩
      exact ⟨F, ⟨hF, hg⟩, hr.symm⟩
  · have h := zero_rho_slice g
    rw [← Omega_iff] at h
    rw [g0_eq, ← abs_le]
    rw [← h]
    constructor
    · rintro ⟨F, ⟨hF, hr⟩, hg⟩
      exact ⟨F, hF, hr, hg.symm⟩
    · rintro ⟨F, hF, hr, hg⟩
      exact ⟨F, ⟨hF, hr⟩, hg.symm⟩

end Papers.AnsariRockelSteinmassl2026RhoGamma.Source.Proofs
