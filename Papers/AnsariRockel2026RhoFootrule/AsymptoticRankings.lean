import Papers.AnsariRockel2026RhoFootrule.FiniteRankings
import Verification.CDFRankStability

/-! # Remark 2.2: asymptotic sharpness for actual finite permutations -/

open MeasureTheory ProbabilityTheory Filter
open scoped unitInterval Topology

namespace Papers.AnsariRockel2026RhoFootrule

/-- Both normalized ranking moments approach those of any prescribed copula. -/
theorem ranking_moment_limits (C : Copula 2) :
    ∃ π : (n : ℕ) → Equiv.Perm (Fin (n+1)),
      Tendsto (fun n => rankingDistance n (π n)/((n : ℝ)+1)^2) atTop (𝓝 (meanDistance C)) ∧
      Tendsto (fun n => rankingSquare n (π n)/((n : ℝ)+1)^3) atTop (𝓝 ((1-C.spearmanRho)/6)) := by
  obtain ⟨π,hr,hf⟩ := Verification.exists_permutationShuffle_rank_limits C
  have hm (n : ℕ) : rankingDistance n (π n)/((n : ℝ)+1)^2=
      (1-(Verification.PermutationShuffle.copula n (π n)).spearmanFootrule)/3 := by
    have h := Verification.footrule_eq_abs_moment (Verification.PermutationShuffle.copula n (π n))
    change _=1-3*meanDistance _ at h
    rw [ranking_mean] at h
    linarith
  have hmC : meanDistance C=(1-C.spearmanFootrule)/3 := by
    have h := Verification.footrule_eq_abs_moment C
    change _=1-3*meanDistance C at h
    linarith
  have hq (n : ℕ) : rankingSquare n (π n)/((n : ℝ)+1)^3=
      (1-(Verification.PermutationShuffle.copula n (π n)).spearmanRho)/6 := by
    have h := Verification.PermutationShuffle.rho n (π n)
    change _=1-6*rankingSquare n (π n)/((n : ℝ)+1)^3 at h
    rw [mul_div_assoc] at h
    linarith
  refine ⟨π,?_,?_⟩
  · simpa only [hm,hmC] using (tendsto_const_nhds.sub hf).div_const 3
  · simpa only [hq] using (tendsto_const_nhds.sub hr).div_const 6

/-- At every admissible mean, finite rankings approach the sharp lower moment boundary. -/
theorem ranking_lower_asymptotic_sharp {m : ℝ} (hm : m ∈ Set.Icc 0 (1/2)) :
    ∃ π : (n : ℕ) → Equiv.Perm (Fin (n+1)),
      Tendsto (fun n => rankingDistance n (π n)/((n : ℝ)+1)^2) atTop (𝓝 m) ∧
      Tendsto (fun n => rankingSquare n (π n)/((n : ℝ)+1)^3) atTop (𝓝 (m^2+minimumVariance m)) := by
  obtain ⟨C,hmean,hvar⟩ := minimum_variance_attained hm
  have hmean' : meanDistance C=m := hmean
  have hvar' : distanceVariance C=minimumVariance m := by
    unfold distanceVariance
    rw [hmean']
    exact hvar
  have he := distanceVariance_eq C
  rw [hmean',hvar'] at he
  have hq : (1-C.spearmanRho)/6=m^2+minimumVariance m := by linarith
  obtain ⟨π,hp,hs⟩ := ranking_moment_limits C
  exact ⟨π,by simpa only [hmean'] using hp,by simpa only [hq] using hs⟩

/-- At every admissible mean, finite rankings approach the sharp upper moment boundary. -/
theorem ranking_upper_asymptotic_sharp {m : ℝ} (hm : m ∈ Set.Icc 0 (1/2)) :
    ∃ π : (n : ℕ) → Equiv.Perm (Fin (n+1)),
      Tendsto (fun n => rankingDistance n (π n)/((n : ℝ)+1)^2) atTop (𝓝 m) ∧
      Tendsto (fun n => rankingSquare n (π n)/((n : ℝ)+1)^3) atTop (𝓝 ((1-(Real.sqrt (1-2*m))^3)/3)) := by
  obtain ⟨C,hmean,hvar⟩ := maximum_variance_attained hm
  have he := distanceVariance_eq C
  rw [hmean,hvar] at he
  unfold maximumVariance at he
  have hq : (1-C.spearmanRho)/6=(1-(Real.sqrt (1-2*m))^3)/3 := by linarith
  obtain ⟨π,hp,hs⟩ := ranking_moment_limits C
  exact ⟨π,by simpa only [hmean] using hp,by simpa only [hq] using hs⟩

end Papers.AnsariRockel2026RhoFootrule
