import Papers.AnsariRockel2024.FrankContinuity
import Verification.FrankTau
import Copula.Rank.Symmetry

/-! # Table 6: Frank Kendall tau and the first Debye function -/

open ProbabilityTheory MeasureTheory Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem frank_conditionalCDF {θ : ℝ} (hθ : θ≠0) (v : I) :
    (fun u => (frankSigned θ).conditionalCDF u v) =ᵐ[volume]
      fun u => Verification.frankPartial θ u v := by
  apply Verification.frank_conditionalCDF_of_cdf _ hθ
  intro u v
  rw [frankSigned_cdf_regular,Verification.frankRegularCDF_eq_real hθ]

theorem frank_kendallTau {θ : ℝ} (hθ : θ≠0) :
    (frankSigned θ).kendallTau=1-4/θ*(1-Verification.debyeOne θ) := by
  apply Verification.frank_kendallTau_of_cdf _ hθ
  intro u v
  rw [frankSigned_cdf_regular,Verification.frankRegularCDF_eq_real hθ]

theorem frank_kendallTau_zero : (frankSigned 0).kendallTau=0 := by
  simp [frankSigned]

theorem frank_debyeTwo_kernel_integral {θ : ℝ} (hθ : θ≠0) :
    Verification.debyeTwo θ=∫ v : I, 2*(v:ℝ)*Verification.debyeKernel (θ*(v:ℝ)) :=
  Verification.debyeTwo_kernel_integral hθ

theorem frank_debyeOne_neg {θ : ℝ} (hθ : θ≠0) :
    Verification.debyeOne (-θ)=Verification.debyeOne θ+θ/2 := Verification.debyeOne_neg hθ

theorem frank_debyeTwo_neg {θ : ℝ} (hθ : θ≠0) :
    Verification.debyeTwo (-θ)=Verification.debyeTwo θ+2*θ/3 := Verification.debyeTwo_neg hθ

theorem frank_kendallTau_neg (θ : ℝ) : (frankSigned (-θ)).kendallTau= -(frankSigned θ).kendallTau := by
  by_cases hθ : θ=0
  · subst θ; simp [frank_kendallTau_zero]
  rw [frank_kendallTau (neg_ne_zero.mpr hθ),frank_kendallTau hθ,Verification.debyeOne_neg hθ]
  field_simp
  ring

theorem frank_spearmanRho_zero : (frankSigned 0).spearmanRho=0 := by
  simp [frankSigned]

theorem frank_spearmanRho_neg (θ : ℝ) : (frankSigned (-θ)).spearmanRho= -(frankSigned θ).spearmanRho := by
  rcases lt_trichotomy θ 0 with hn | hz | hp
  · simp [frankSigned,frankNegative,hn,not_lt.mpr hn.le,neg_pos.mpr hn,
      Copula.spearmanRho_reflect_second]
  · subst θ; simp [frank_spearmanRho_zero]
  · simp [frankSigned,frankNegative,hp,show ¬0< -θ by linarith,show -θ<0 by linarith,
      Copula.spearmanRho_reflect_second]

end Papers.AnsariRockel2024
