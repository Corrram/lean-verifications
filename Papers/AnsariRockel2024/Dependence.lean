import Papers.AnsariRockel2024.Definitions
import Copula.Dependence.ConditionalMonotonicity
import Copula.Order.FGM
import Copula.TailDependence.Examples

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

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

