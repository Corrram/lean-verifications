import Verification.Nelsen18Tails

/-! # Nelsen 18: constructor, CDF, tails and conditional classifications -/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem nelsen18_cdf_full (θ : ℝ) (hθ : 2 ≤ θ) (u v : I) :
    (Verification.nelsen18 θ hθ).cdf ![u,v] =
      max 0 (1+θ/Real.log (Verification.n18Inv θ u+Verification.n18Inv θ v)) :=
  Verification.nelsen18_cdf_full θ hθ u v

theorem nelsen18_cdf_of_lt_one (θ : ℝ) (hθ : 2 ≤ θ) (u v : I) (hu : u < 1) (hv : v < 1) :
    (Verification.nelsen18 θ hθ).cdf ![u,v] =
      max 0 (1+θ/Real.log (Real.exp (θ/((u:ℝ)-1))+Real.exp (θ/((v:ℝ)-1)))) :=
  Verification.nelsen18_cdf_of_lt_one θ hθ u v hu hv

theorem nelsen18_lowerTail (θ : ℝ) (hθ : 2 ≤ θ) :
    (Verification.nelsen18 θ hθ).HasLowerTailDependence 0 :=
  Verification.nelsen18_lowerTail θ hθ

theorem nelsen18_upperTail (θ : ℝ) (hθ : 2 ≤ θ) :
    (Verification.nelsen18 θ hθ).HasUpperTailDependence 1 :=
  Verification.nelsen18_upperTail θ hθ

theorem nelsen18_not_pqd (θ : ℝ) (hθ : 2 ≤ θ) : ¬ (Verification.nelsen18 θ hθ).IsPQD :=
  Verification.nelsen18_not_pqd θ hθ

theorem nelsen18_not_ci (θ : ℝ) (hθ : 2 ≤ θ) : ¬ (Verification.nelsen18 θ hθ).IsCI :=
  Verification.nelsen18_not_ci θ hθ

theorem nelsen18_not_density_tp2 (θ : ℝ) (hθ : 2 ≤ θ) :
    ¬ (Verification.nelsen18 θ hθ).HasMTP2Density :=
  Verification.nelsen18_not_density_tp2 θ hθ

theorem nelsen18_not_nqd (θ : ℝ) (hθ : 2 ≤ θ) : ¬ (Verification.nelsen18 θ hθ).IsNQD :=
  Verification.nelsen18_not_nqd θ hθ

theorem nelsen18_not_cd (θ : ℝ) (hθ : 2 ≤ θ) : ¬ (Verification.nelsen18 θ hθ).IsCD :=
  Verification.nelsen18_not_cd θ hθ

end Papers.AnsariRockel2024
