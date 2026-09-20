import Papers.AnsariRockel2024.Definitions
import Copula.Rank.FGMChatterjee
import Copula.Rank.FGMKendall
import Copula.Rank.FrechetChatterjee
import Copula.Rank.FrechetKendall

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

/-- arXiv:2310.17307v3, Table 6, FGM, Spearman rho. See COVERAGE.md for conventions. -/
theorem fgm_rho (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.fgm θ hθ).spearmanRho = θ / 3 :=
  Copula.spearmanRho_fgm θ hθ

/-- arXiv:2310.17307v3, Table 6, FGM, Kendall tau. See COVERAGE.md for conventions. -/
theorem fgm_tau (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.fgm θ hθ).kendallTau = 2 * θ / 9 :=
  Copula.kendallTau_fgm θ hθ

/-- arXiv:2310.17307v3, Table 6, FGM, Chatterjee xi. See COVERAGE.md for conventions. -/
theorem fgm_xi (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.fgm θ hθ).chatterjeeXi = θ ^ 2 / 15 :=
  Copula.chatterjeeXi_fgm θ hθ

/-- arXiv:2310.17307v3, Table 6, Frechet, Spearman rho. See COVERAGE.md for conventions. -/
theorem frechet_rho (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (Copula.frechet a b ha hb hab).spearmanRho = a - b :=
  Copula.spearmanRho_frechet a b ha hb hab

/-- arXiv:2310.17307v3, Table 6, Frechet, Kendall tau. See COVERAGE.md for conventions. -/
theorem frechet_tau (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (Copula.frechet a b ha hb hab).kendallTau = (a - b) * (a + b + 2) / 3 :=
  Copula.kendallTau_frechet a b ha hb hab

/-- arXiv:2310.17307v3, Table 6, Frechet, Chatterjee xi. See COVERAGE.md for conventions. -/
theorem frechet_xi (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (Copula.frechet a b ha hb hab).chatterjeeXi = (a - b) ^ 2 + a * b :=
  Copula.chatterjeeXi_frechet a b ha hb hab

/-- arXiv:2310.17307v3, Table 6, Mardia, Spearman rho. See COVERAGE.md for conventions. -/
theorem mardia_rho (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.mardia θ hθ).spearmanRho = θ ^ 3 :=
  Copula.spearmanRho_mardia θ hθ

/-- arXiv:2310.17307v3, Table 6, Mardia, Kendall tau. See COVERAGE.md for conventions. -/
theorem mardia_tau (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.mardia θ hθ).kendallTau = θ ^ 3 * (θ ^ 2 + 2) / 3 :=
  Copula.kendallTau_mardia θ hθ

/-- arXiv:2310.17307v3, Table 6, Mardia, Chatterjee xi. See COVERAGE.md for conventions. -/
theorem mardia_xi (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.mardia θ hθ).chatterjeeXi = θ ^ 4 * (1 + 3 * θ ^ 2) / 4 :=
  Copula.chatterjeeXi_mardia θ hθ

end Papers.AnsariRockel2024

