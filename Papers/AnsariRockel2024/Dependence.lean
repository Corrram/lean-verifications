import Papers.AnsariRockel2024.Definitions
import Copula.Dependence.ConditionalMonotonicity
import Copula.Dependence.AMH
import Copula.Order.FGM
import Copula.TailDependence.Examples
import Copula.TailDependence.AMH

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

/-- Table 3: AMH is positively quadrant dependent exactly for nonnegative θ. -/
theorem amh_pqd_iff (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) :
    (Copula.amh θ hmin hmax).IsPQD ↔ 0 ≤ θ :=
  Copula.isPQD_amh_iff θ hmin hmax

/-- Table 3: AMH is negatively quadrant dependent exactly for nonpositive θ. -/
theorem amh_nqd_iff (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) :
    (Copula.amh θ hmin hmax).IsNQD ↔ θ ≤ 0 :=
  Copula.isNQD_amh_iff θ hmin hmax

/-- Corrected Table 3 AMH tail pair for every parameter below one. -/
theorem amh_tails_lt_one (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1)
    (hθ : θ < 1) :
    (Copula.amh θ hmin hmax).HasLowerTailDependence 0 ∧
    (Copula.amh θ hmin hmax).HasUpperTailDependence 0 :=
  ⟨Copula.hasLowerTailDependence_amh_lt_one θ hmin hmax hθ,
    Copula.hasUpperTailDependence_amh θ hmin hmax⟩

/-- Corrected Table 3 AMH endpoint: Clayton(1) has lower-tail coefficient 1/2. -/
theorem amh_tails_one :
    (Copula.amh 1 (by norm_num) le_rfl).HasLowerTailDependence (1 / 2) ∧
    (Copula.amh 1 (by norm_num) le_rfl).HasUpperTailDependence 0 :=
  ⟨Copula.hasLowerTailDependence_amh_one,
    Copula.hasUpperTailDependence_amh 1 (by norm_num) le_rfl⟩

/-- arXiv:2310.17307v3, Table 5 / Appendix A.4.1: FGM CI. See COVERAGE.md for conventions. -/
theorem fgm_ci (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.fgm θ hθ).IsCI ↔ 0 ≤ θ :=
  Copula.isCI_fgm_iff θ hθ

/-- arXiv:2310.17307v3, Table 5 / Appendix A.4.1: FGM CD. See COVERAGE.md for conventions. -/
theorem fgm_cd (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.fgm θ hθ).IsCD ↔ θ ≤ 0 :=
  Copula.isCD_fgm_iff θ hθ

/-- arXiv:2310.17307v3, Table 5 / Appendix A.4.2: FGM lower orthant order. See COVERAGE.md for conventions. -/
theorem fgm_lowerOrthant {θ η : ℝ} (hθ : |θ| ≤ 1) (hη : |η| ≤ 1) :
    (Copula.fgm θ hθ).LowerOrthantLE (Copula.fgm η hη) ↔ θ ≤ η :=
  Copula.lowerOrthantLE_fgm_iff hθ hη

/-- arXiv:2310.17307v3, Table 5 / Appendix A.4.3: FGM lower and upper tails. See COVERAGE.md for conventions. -/
theorem fgm_tails (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.fgm θ hθ).HasLowerTailDependence 0 ∧
    (Copula.fgm θ hθ).HasUpperTailDependence 0 :=
  ⟨Copula.hasLowerTailDependence_fgm θ hθ, Copula.hasUpperTailDependence_fgm θ hθ⟩

/-- arXiv:2310.17307v3, Table 5 / Appendix A.4.3: Frechet tails. See COVERAGE.md for conventions. -/
theorem frechet_tails (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (Copula.frechet a b ha hb hab).HasLowerTailDependence a ∧
    (Copula.frechet a b ha hb hab).HasUpperTailDependence a :=
  ⟨Copula.hasLowerTailDependence_frechet a b ha hb hab,
      Copula.hasUpperTailDependence_frechet a b ha hb hab⟩

/-- arXiv:2310.17307v3, Table 5 / Appendix A.4.3: Mardia tails. See COVERAGE.md for conventions. -/
theorem mardia_tails (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.mardia θ hθ).HasLowerTailDependence (θ ^ 2 * (1 + θ) / 2) ∧
    (Copula.mardia θ hθ).HasUpperTailDependence (θ ^ 2 * (1 + θ) / 2) :=
  ⟨Copula.hasLowerTailDependence_mardia θ hθ, Copula.hasUpperTailDependence_mardia θ hθ⟩

end Papers.AnsariRockel2024

