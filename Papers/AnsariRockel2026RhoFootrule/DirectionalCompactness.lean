import Verification.DirectionalCompactness
import Papers.AnsariRockel2026RhoFootrule.UpperInnerEnvelope
import Papers.AnsariRockel2026RhoFootrule.QuantitativeRatio

/-! # Compactness and attained maxima of the full directional region -/

open MeasureTheory ProbabilityTheory Verification Set

namespace Papers.AnsariRockel2026RhoFootrule

/-- Example 2.9: compactness concerns the full attainable region. -/
theorem directional_region_compact : IsCompact directionalRegion := by
  have he : directionalRegion = Set.range (fun C : Copula 2 =>
      (C.chatterjeeXi, correlationRatio C)) := by
    ext p
    simp only [directionalRegion, mem_ofPred_eq, mem_range, Prod.ext_iff]
  rw [he]
  exact isCompact_xi_eta_region

noncomputable def upperRatio (x : ℝ) : ℝ := sSup {y : ℝ | (x, y) ∈ directionalRegion}

/-- Every vertical slice of the full region has an attained upper endpoint. -/
theorem upperRatio_isGreatest (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    IsGreatest {y : ℝ | (x, y) ∈ directionalRegion} (upperRatio x) := by
  let K := directionalRegion ∩ {p : ℝ × ℝ | p.1 = x}
  have hk : IsCompact K := directional_region_compact.inter_right
    (isClosed_eq continuous_fst continuous_const)
  obtain ⟨C, hCx, hCy⟩ := upper_inner_attained x hx
  have hne : K.Nonempty := ⟨(x, upperInnerRatio x), ⟨C, hCx, hCy⟩, rfl⟩
  obtain ⟨⟨u, y⟩, ⟨hp, he⟩, hm⟩ := hk.exists_isMaxOn hne continuous_snd.continuousOn
  change u = x at he
  subst u
  have hy : IsGreatest {z : ℝ | (x, z) ∈ directionalRegion} y :=
    ⟨hp, fun z hz => hm ⟨hz, rfl⟩⟩
  rwa [upperRatio, hy.csSup_eq]

/-- A genuine copula attains the upper boundary for every xi. -/
theorem upper_ratio_attained (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ C : Copula 2, C.chatterjeeXi = x ∧ copulaCorrelationRatio C = upperRatio x :=
  (upperRatio_isGreatest x hx).1

/-- Example 2.9: the attained quarter-xi maximum is uniformly below one half. -/
theorem quarter_xi_maximum :
    ∃ C : Copula 2, C.chatterjeeXi = 1/4 ∧
      copulaCorrelationRatio C ≤ 256/525 ∧
      ∀ D : Copula 2, D.chatterjeeXi = 1/4 →
        copulaCorrelationRatio D ≤ copulaCorrelationRatio C := by
  obtain ⟨C, hCx, hCy⟩ := upper_ratio_attained (1/4) (by norm_num)
  refine ⟨C, hCx, quarter_xi_uniform_gap C hCx, ?_⟩
  intro D hDx
  rw [hCy]
  exact (upperRatio_isGreatest (1/4) (by norm_num)).2 ⟨D, hDx, rfl⟩

end Papers.AnsariRockel2026RhoFootrule
