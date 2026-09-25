import Papers.AnsariRockel2024.Laplace
import Verification.GammaMixtureDependence
import Verification.MTP2ConditionalIncreasing
import Copula.Order.StrictSpearman
import Verification.ScaleMixtureTP2Transfer
import Verification.LaplaceJointNonTP2

open ProbabilityTheory Set Copula

namespace Papers.AnsariRockel2024

theorem laplace_not_independent_zero :
    Verification.laplaceBivariate 0 (by norm_num) ≠ independence 2 :=
  Verification.gammaVariance_zero_ne_independence 1 1 zero_lt_one zero_lt_one

theorem laplace_not_isPQD_nonpositive (r : ℝ) (hr : r∈Icc (-1) 1) (hn : r≤0) :
    ¬(Verification.laplaceBivariate r hr).IsPQD := by
  intro h
  by_cases hz : r=0
  · subst r
    apply laplace_not_independent_zero
    apply h.kendallTau_eq_zero_iff.mp
    rw [laplace_kendallTau]
    norm_num
  have ht := h.kendallTau_nonneg
  rw [laplace_kendallTau] at ht
  have ha : Real.arcsin r<0 := by
    simpa using Real.strictMonoOn_arcsin hr (show (0:ℝ)∈Icc (-1) 1 by norm_num) (lt_of_le_of_ne hn hz)
  have hneg := mul_neg_of_pos_of_neg (div_pos (by norm_num : (0:ℝ)<2) Real.pi_pos) ha
  linarith

theorem laplace_not_isNQD_nonnegative (r : ℝ) (hr : r∈Icc (-1) 1) (hn : 0≤r) :
    ¬(Verification.laplaceBivariate r hr).IsNQD := by
  intro h
  by_cases hz : r=0
  · subst r
    apply laplace_not_independent_zero
    apply h.kendallTau_eq_zero_iff.mp
    rw [laplace_kendallTau]
    norm_num
  have ht := h.kendallTau_nonpos
  rw [laplace_kendallTau] at ht
  have ha : 0<Real.arcsin r := by
    simpa using Real.strictMonoOn_arcsin (show (0:ℝ)∈Icc (-1) 1 by norm_num) hr
      (lt_of_le_of_ne hn (Ne.symm hz))
  have hpos := mul_pos (div_pos (by norm_num : (0:ℝ)<2) Real.pi_pos) ha
  linarith

theorem laplace_not_isCI_nonpositive (r : ℝ) (hr : r∈Icc (-1) 1) (hn : r≤0) :
    ¬(Verification.laplaceBivariate r hr).IsCI :=
  fun h => laplace_not_isPQD_nonpositive r hr hn h.isPQD

theorem laplace_not_isCD_nonnegative (r : ℝ) (hr : r∈Icc (-1) 1) (hn : 0≤r) :
    ¬(Verification.laplaceBivariate r hr).IsCD :=
  fun h => laplace_not_isNQD_nonnegative r hr hn h.isNQD

theorem laplace_not_hasMTP2Density_nonpositive (r : ℝ) (hr : r∈Icc (-1) 1) (hn : r≤0) :
    ¬(Verification.laplaceBivariate r hr).HasMTP2Density :=
  fun h => laplace_not_isCI_nonpositive r hr hn (Verification.mtp2_isCI h)

theorem laplace_not_hasMTP2Density (r : ℝ) (hr : r∈Icc (-1) 1) :
    ¬(Verification.laplaceBivariate r hr).HasMTP2Density := by
  intro h
  have hi := (Verification.gaussianScaleMixture_absolutelyContinuous_iff hr
    (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt (by fun_prop)
    Verification.laplace_scale_pos).mp h.absolutelyContinuous
  exact Verification.laplace_joint_no_tp2_density hi
    (Verification.gaussianScaleMixture_joint_tp2_density hi
      (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt (by fun_prop)
      Verification.laplace_scale_pos h)

end Papers.AnsariRockel2024
