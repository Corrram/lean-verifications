import Papers.Rockel2026ExactBlest.ExactBlestCDF

/-! Identification of the local Frechet bounds with the actual beta extremizers. -/
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
open Papers.Rockel2026XiBlest
namespace Papers.Rockel2026ExactBlest
noncomputable section
set_option maxHeartbeats 8000000

theorem beta_cdf_scalar (q u v : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (_hu : u ∈ Icc (0 : ℝ) 1) (_hv : v ∈ Icc (0 : ℝ) 1) :
    min q (min u v) + max 0 (min (1 / 2) (min u (v - 1 / 2 + q)) - q) +
      max 0 (min (1 - q) (min u (v + 1 / 2 - q)) - 1 / 2) +
      max 0 (min u v - (1 - q)) = localUpper q u v := by
  unfold localUpper
  grind (splits := 30)

theorem beta_shuffle_cdf (q : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2)) (u v : I) :
    (volume : Measure I).real {x | x ≤ u ∧ betaRank q hq x ≤ v} = localUpper q u v := by
  let b0 := min q (min (u : ℝ) v)
  let b1 := min (1 / 2 : ℝ) (min (u : ℝ) ((v : ℝ) - 1 / 2 + q))
  let b2 := min (1 - q) (min (u : ℝ) ((v : ℝ) + 1 / 2 - q))
  let b3 := min (u : ℝ) v
  have he : Subtype.val '' {x : I | x ≤ u ∧ betaRank q hq x ≤ v} =
      ((Icc (0 : ℝ) b0 ∪ Ioc q b1) ∪ Ioc (1 / 2) b2) ∪ Ioc (1 - q) b3 := by
    ext x
    simp only [mem_image, mem_ofPred_eq, mem_union, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨y, ⟨hyu, hyv⟩, rfl⟩
      change betaRankReal q y ≤ (v : ℝ) at hyv
      change (y : ℝ) ≤ u at hyu
      have hy0 := y.property.1
      have hy1 := y.property.2
      dsimp [b0, b1, b2, b3]
      unfold betaRankReal paramPieces at hyv
      split_ifs at hyv <;> grind
    · intro hx
      have hx01 : x ∈ Icc (0 : ℝ) 1 := by
        dsimp [b0, b1, b2, b3] at hx
        grind [u.property, v.property]
      refine ⟨⟨x, hx01⟩, ⟨?_, ?_⟩, rfl⟩
      · change x ≤ (u : ℝ)
        dsimp [b0, b1, b2, b3] at hx
        grind
      · change betaRankReal q x ≤ (v : ℝ)
        unfold betaRankReal paramPieces
        dsimp [b0, b1, b2, b3] at hx
        split_ifs <;> grind
  have hd01 : Disjoint (Icc (0 : ℝ) b0) (Ioc q b1) := by
    apply disjoint_left.mpr
    intro x hx hy
    dsimp [b0] at hx
    exact (not_lt_of_ge (hx.2.trans (min_le_left _ _))) hy.1
  have hd2 : Disjoint (Icc (0 : ℝ) b0 ∪ Ioc q b1) (Ioc (1 / 2) b2) := by
    apply disjoint_left.mpr
    intro x hx hy
    rcases hx with hx | hx
    · have h := hx.2.trans (min_le_left q _)
      linarith [hq.2, hy.1]
    · exact (not_lt_of_ge (hx.2.trans (min_le_left _ _))) hy.1
  have hd3 : Disjoint ((Icc (0 : ℝ) b0 ∪ Ioc q b1) ∪ Ioc (1 / 2) b2) (Ioc (1 - q) b3) := by
    apply disjoint_left.mpr
    intro x hx hy
    rcases hx with (hx | hx) | hx
    · have h := hx.2.trans (min_le_left q _)
      linarith [hq.2, hy.1]
    · have h := hx.2.trans (min_le_left (1 / 2) _)
      linarith [hq.2, hy.1]
    · exact (not_lt_of_ge (hx.2.trans (min_le_left _ _))) hy.1
  change ((volume : Measure I) {x | x ≤ u ∧ betaRank q hq x ≤ v}).toReal = _
  rw [unitInterval.volume_apply, he]
  change (volume : Measure ℝ).real (((Icc 0 b0 ∪ Ioc q b1) ∪ Ioc (1 / 2) b2) ∪ Ioc (1 - q) b3) = _
  have hf0 : (volume : Measure ℝ) (Icc 0 b0) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hf1 : (volume : Measure ℝ) (Ioc q b1) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hf2 : (volume : Measure ℝ) (Ioc (1 / 2) b2) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hf3 : (volume : Measure ℝ) (Ioc (1 - q) b3) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hf01 : (volume : Measure ℝ) (Icc 0 b0 ∪ Ioc q b1) ≠ ⊤ := by
    rw [measure_union hd01 measurableSet_Ioc]
    exact ENNReal.add_ne_top.mpr ⟨hf0, hf1⟩
  have hf012 : (volume : Measure ℝ) ((Icc 0 b0 ∪ Ioc q b1) ∪ Ioc (1 / 2) b2) ≠ ⊤ := by
    rw [measure_union hd2 measurableSet_Ioc]
    exact ENNReal.add_ne_top.mpr ⟨hf01, hf2⟩
  rw [measureReal_union hd3 measurableSet_Ioc hf012 hf3,
    measureReal_union hd2 measurableSet_Ioc hf01 hf2,
    measureReal_union hd01 measurableSet_Ioc hf0 hf1]
  simp only [Measure.real, Real.volume_Icc, Real.volume_Ioc, ENNReal.toReal_ofReal', sub_zero]
  have hb0 : 0 ≤ b0 := le_min hq.1 (le_min u.property.1 v.property.1)
  rw [max_eq_left hb0]
  simpa only [max_comm] using beta_cdf_scalar q u v hq u.property v.property

theorem beta_upper_cdf (C : Copula 2) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hb : C.blomqvistBeta = 4 * q - 1) (hn : blestNu C = betaUpper C.blomqvistBeta) (u v : I) :
    C.cdf ![u, v] = localUpper q u v := by
  have hm : Measurable (fun x : I => ![x, betaRank q hq x]) := by
    have := measurable_betaRank q hq
    fun_prop
  rw [Copula.cdf, beta_upper_graph_law C q hq hb hn, map_measureReal_apply hm measurableSet_Iic]
  have he : (fun x : I => ![x, betaRank q hq x]) ⁻¹' Iic ![u, v] =
      {x | x ≤ u ∧ betaRank q hq x ≤ v} := by
    ext x
    simp [Pi.le_def, Fin.forall_fin_two]
  rw [he]
  exact beta_shuffle_cdf q hq u v

theorem local_bounds_reflection (q u v : ℝ) (_hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (_hu : u ∈ Icc (0 : ℝ) 1) (_hv : v ∈ Icc (0 : ℝ) 1) :
    u - localUpper (1 / 2 - q) u (1 - v) = localLower q u v := by
  unfold localUpper localLower
  grind (splits := 30)

theorem beta_lower_cdf (C : Copula 2) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hb : C.blomqvistBeta = 4 * q - 1) (hn : blestNu C = betaLower C.blomqvistBeta) (u v : I) :
    C.cdf ![u, v] = localLower q u v := by
  have hq' : 1 / 2 - q ∈ Icc (0 : ℝ) (1 / 2) := ⟨by linarith [hq.2], by linarith [hq.1]⟩
  have hb' : (C.reflect {1}).blomqvistBeta = 4 * (1 / 2 - q) - 1 := by
    rw [Copula.blomqvistBeta_reflect_second, hb]; ring
  have hn' : blestNu (C.reflect {1}) = betaUpper (C.reflect {1}).blomqvistBeta := by
    rw [blest_reflect_second, Copula.blomqvistBeta_reflect_second, hn]
    unfold betaUpper betaLower
    ring
  have h := beta_upper_cdf (C.reflect {1}) (1 / 2 - q) hq' hb' hn' u (unitInterval.symm v)
  rw [Copula.cdf_reflect_second, unitInterval.symm_symm] at h
  change (u : ℝ) - C.cdf ![u, v] = localUpper (1 / 2 - q) u (1 - (v : ℝ)) at h
  rw [← local_bounds_reflection q u v hq u.property v.property]
  linarith

#assert_standard_axioms Papers.Rockel2026ExactBlest.local_bounds_reflection
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_lower_cdf
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_cdf_scalar
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_shuffle_cdf
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_upper_cdf
end
end Papers.Rockel2026ExactBlest
