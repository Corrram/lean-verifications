import Papers.OrendayLaresRockel2026TauFootruleBeta.JointRegion
import Mathlib.Analysis.Convex.Mul
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Corollary 4.1 and Remark 4.3: geometry of the attained region -/

open ProbabilityTheory Set

namespace Papers.OrendayLaresRockel2026TauFootruleBeta

def jointRegion : Set (ℝ × ℝ × ℝ) :=
  {z | ∃ C : Copula 2, C.kendallTau = z.1 ∧
    C.spearmanFootrule = z.2.1 ∧ C.blomqvistBeta = z.2.2}

theorem mem_jointRegion (t p b : ℝ) : (t, p, b) ∈ jointRegion ↔
    b ∈ Icc (-1) 1 ∧ 3 / 16 * (1 + b) ^ 2 - 1 / 2 ≤ p ∧
    p ≤ 1 - 3 / 8 * (1 - b) ^ 2 ∧
    4 / 3 * p - 1 / 3 ≤ t ∧ t ≤ 2 / 3 * p + 1 / 3 :=
  exact_joint_region t p b

theorem jointRegion_closed : IsClosed jointRegion := by
  have he : jointRegion = {z : ℝ × ℝ × ℝ |
      -1 ≤ z.2.2 ∧ z.2.2 ≤ 1 ∧
      3 / 16 * (1 + z.2.2) ^ 2 - 1 / 2 ≤ z.2.1 ∧
      z.2.1 ≤ 1 - 3 / 8 * (1 - z.2.2) ^ 2 ∧
      4 / 3 * z.2.1 - 1 / 3 ≤ z.1 ∧ z.1 ≤ 2 / 3 * z.2.1 + 1 / 3} := by
    ext ⟨t, p, b⟩
    simp only [mem_jointRegion, mem_ofPred_eq, mem_Icc, and_assoc]
  rw [he]
  simp only [ofPred_and]
  repeat' apply IsClosed.inter
  all_goals exact isClosed_le (by fun_prop) (by fun_prop)

theorem jointRegion_compact : IsCompact jointRegion := by
  apply (isCompact_Icc : IsCompact (Icc ((-1 : ℝ), (-1 / 2 : ℝ), (-1 : ℝ))
    ((1 : ℝ), (1 : ℝ), (1 : ℝ)))).of_isClosed_subset jointRegion_closed
  rintro ⟨t, p, b⟩ ⟨C, rfl, rfl, rfl⟩
  exact ⟨⟨C.kendallTau_mem_Icc.1, C.spearmanFootrule_mem_Icc.1, C.blomqvistBeta_mem_Icc.1⟩,
    C.kendallTau_mem_Icc.2, C.spearmanFootrule_mem_Icc.2, C.blomqvistBeta_mem_Icc.2⟩

theorem jointRegion_convex : Convex ℝ jointRegion := by
  rintro ⟨t, p, b⟩ ht ⟨t', p', b'⟩ ht' a c ha hc hac
  rw [mem_jointRegion] at ht ht'
  change (a * t + c * t', a * p + c * p', a * b + c * b') ∈ jointRegion
  rw [mem_jointRegion]
  have hs (x y : ℝ) : (a * x + c * y) ^ 2 ≤ a * x ^ 2 + c * y ^ 2 :=
    (even_two.convexOn_pow.2 (mem_univ x) (mem_univ y) ha hc hac)
  have hplus : 1 + (a * b + c * b') = a * (1 + b) + c * (1 + b') := by
    nlinarith only [hac]
  have hminus : 1 - (a * b + c * b') = a * (1 - b) + c * (1 - b') := by
    nlinarith only [hac]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left ht.1.1 ha, mul_le_mul_of_nonneg_left ht'.1.1 hc]
  · nlinarith [mul_le_mul_of_nonneg_left ht.1.2 ha, mul_le_mul_of_nonneg_left ht'.1.2 hc]
  · rw [hplus]
    nlinarith [hs (1 + b) (1 + b'), mul_le_mul_of_nonneg_left ht.2.1 ha,
      mul_le_mul_of_nonneg_left ht'.2.1 hc]
  · rw [hminus]
    nlinarith [hs (1 - b) (1 - b'), mul_le_mul_of_nonneg_left ht.2.2.1 ha,
      mul_le_mul_of_nonneg_left ht'.2.2.1 hc]
  · nlinarith [mul_le_mul_of_nonneg_left ht.2.2.2.1 ha,
      mul_le_mul_of_nonneg_left ht'.2.2.2.1 hc]
  · nlinarith [mul_le_mul_of_nonneg_left ht.2.2.2.2 ha,
      mul_le_mul_of_nonneg_left ht'.2.2.2.2 hc]

theorem fibre_reflection (t p b : ℝ) :
    (2 * p - t, p, b) ∈ jointRegion ↔ (t, p, b) ∈ jointRegion := by
  rw [mem_jointRegion, mem_jointRegion]
  constructor <;> rintro ⟨hb, hpL, hpU, htL, htU⟩ <;>
    exact ⟨hb, hpL, hpU, by linarith, by linarith⟩

theorem fibre_midpoint_attained (p b : ℝ) (hb : b ∈ Icc (-1) 1)
    (hpL : 3 / 16 * (1 + b) ^ 2 - 1 / 2 ≤ p)
    (hpU : p ≤ 1 - 3 / 8 * (1 - b) ^ 2) :
    ∃ C : Copula 2, C.kendallTau = p ∧ C.spearmanFootrule = p ∧ C.blomqvistBeta = b := by
  apply (exact_joint_region p p b).mpr
  have hp1 : p ≤ 1 := by nlinarith [sq_nonneg (1 - b)]
  exact ⟨hb, hpL, hpU, by linarith, by linarith⟩

noncomputable def betaSectionLower (p : ℝ) : ℝ := 1 - Real.sqrt (8 / 3 * (1 - p))
noncomputable def betaSectionUpper (p : ℝ) : ℝ := min 1 (-1 + 4 / Real.sqrt 3 * Real.sqrt (p + 1 / 2))

theorem footrule_beta_section (p b : ℝ) (hp : p ∈ Icc (-1 / 2) 1) :
    (b ∈ Icc (-1) 1 ∧ 3 / 16 * (1 + b) ^ 2 - 1 / 2 ≤ p ∧
      p ≤ 1 - 3 / 8 * (1 - b) ^ 2) ↔
    b ∈ Icc (betaSectionLower p) (betaSectionUpper p) := by
  have hA : 0 ≤ 8 / 3 * (1 - p) := by linarith [hp.2]
  have hB : 0 ≤ p + 1 / 2 := by linarith [hp.1]
  have hs3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hs3p : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsp := Real.sqrt_nonneg (p + 1 / 2)
  have hsp2 := Real.sq_sqrt hB
  have hsa := Real.sqrt_nonneg (8 / 3 * (1 - p))
  have hsa2 := Real.sq_sqrt hA
  have hquot0 : 0 ≤ 4 / Real.sqrt 3 * Real.sqrt (p + 1 / 2) :=
    mul_nonneg (div_nonneg (by norm_num) hs3p.le) hsp
  have hquot2 : (4 / Real.sqrt 3 * Real.sqrt (p + 1 / 2)) ^ 2 = 16 / 3 * (p + 1 / 2) := by
    rw [mul_pow, div_pow, hs3, hsp2]
    ring
  unfold betaSectionLower betaSectionUpper
  simp only [mem_Icc, le_min_iff]
  constructor
  · rintro ⟨⟨hb0, hb1⟩, hpL, hpU⟩
    refine ⟨?_, hb1, ?_⟩
    · nlinarith
    · nlinarith
  · rintro ⟨hbL, hb1, hbU⟩
    have hb0 : -1 ≤ b := by nlinarith [hp.1]
    refine ⟨⟨hb0, hb1⟩, ?_, ?_⟩ <;> nlinarith

theorem fixed_footrule_rectangle (p : ℝ) (hp : p ∈ Icc (-1 / 2) 1) :
    {z : ℝ × ℝ | (z.1, p, z.2) ∈ jointRegion} =
      Icc (4 / 3 * p - 1 / 3) (2 / 3 * p + 1 / 3) ×ˢ
      Icc (betaSectionLower p) (betaSectionUpper p) := by
  ext ⟨t, b⟩
  simp only [mem_ofPred_eq, mem_jointRegion, mem_prod, mem_Icc]
  have h := footrule_beta_section p b hp
  simp only [mem_Icc] at h
  tauto

end Papers.OrendayLaresRockel2026TauFootruleBeta
