import Papers.AnsariRockel2024.Nelsen7Tau

/-! # A false intermediate xi integrand in the arXiv v3 appendix

Appendix A.5.1 of arXiv:2310.17307v3 prints the integrand
`(θv+1-θ)^2 * (θuv+(1-θ)(u+v-1))₊` for Nelsen 7's xi.
The positive part is the CDF, whereas the squared conditional CDF is a
step profile. The printed integral fails even for interior parameters. The final
Table 6 value `xi = 1-θ` is proved separately and is correct.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

/-- The xi expression obtained from the intermediate integrand printed in
arXiv:2310.17307v3, Appendix A.5.1. The CDF factor is exactly the printed
positive-part expression by `Copula.cdf_nelsen7`. -/
noncomputable def nelsen7PrintedXiCandidate (θ : I) : ℝ :=
  6 * (∫ v : I, ∫ u : I,
    (((θ : ℝ) * v + 1 - θ) ^ 2) * (Copula.nelsen7 θ).cdf ![u, v]) - 2

/-- The candidate is literally the positive-part integrand printed in
Appendix A.5.1 of arXiv v3, under the paper's Nelsen 7 CDF convention. -/
theorem nelsen7_printed_xi_candidate_expanded (θ : I) :
    nelsen7PrintedXiCandidate θ =
      6 * (∫ v : I, ∫ u : I,
        (((θ : ℝ) * v + 1 - θ) ^ 2) *
          max 0 ((θ : ℝ) * u * v + (1 - (θ : ℝ)) * ((u : ℝ) + v - 1))) - 2 := by
  unfold nelsen7PrintedXiCandidate
  simp_rw [Copula.cdf_nelsen7]

/-- The printed intermediate expression evaluates to a different affine
function on the entire parameter interval. -/
theorem nelsen7_printed_xi_candidate_formula (θ : I) :
    nelsen7PrintedXiCandidate θ = -1 - (θ : ℝ) / 4 := by
  have hinner (v : I) :
      (∫ u : I, (((θ : ℝ) * v + 1 - θ) ^ 2) *
        (Copula.nelsen7 θ).cdf ![u, v]) =
      ((θ : ℝ) * v + 1 - θ) * (v : ℝ) ^ 2 / 2 := by
    rw [integral_const_mul, nelsen7_integral_cdf_first]
    let h : ℝ := (θ : ℝ) * v + 1 - θ
    change h ^ 2 * ((v : ℝ) ^ 2 / (2 * h)) = h * (v : ℝ) ^ 2 / 2
    by_cases hz : h = 0
    · simp [hz]
    · field_simp
  unfold nelsen7PrintedXiCandidate
  simp_rw [hinner]
  have hp : (fun v : I => ((θ : ℝ) * v + 1 - θ) * (v : ℝ) ^ 2 / 2) =
      fun v : I => ((θ : ℝ) / 2) * (v : ℝ) ^ 3 +
        ((1 - (θ : ℝ)) / 2) * (v : ℝ) ^ 2 := by
    funext v
    ring
  rw [hp, integral_add, integral_const_mul, integral_const_mul,
    Copula.integral_unit_pow, Copula.integral_unit_pow]
  · ring
  all_goals exact Copula.integrable_continuous_unit volume (by fun_prop)

/-- The printed expression gives -1 at the countermonotonic endpoint. -/
theorem nelsen7_printed_xi_candidate_zero :
    nelsen7PrintedXiCandidate 0 = -1 := by
  simpa using nelsen7_printed_xi_candidate_formula (0 : I)

private noncomputable def n7Half : I := ⟨1 / 2, by constructor <;> norm_num⟩

/-- An interior counterexample, within the parameter range of the appendix's
calculation: printed xi is -9/8, whereas actual xi is 1/2. -/
theorem nelsen7_printed_xi_identity_false_half :
    (Copula.nelsen7 n7Half).chatterjeeXi ≠
      nelsen7PrintedXiCandidate n7Half := by
  rw [nelsen7_xi, nelsen7_printed_xi_candidate_formula]
  norm_num [n7Half]

/-- The false intermediate xi equality fails at every allowed parameter,
including the source's entire open interval, while Table 6's final xi formula
is correct. -/
theorem nelsen7_printed_xi_identity_false (θ : I) :
    (Copula.nelsen7 θ).chatterjeeXi ≠ nelsen7PrintedXiCandidate θ := by
  rw [nelsen7_xi, nelsen7_printed_xi_candidate_formula]
  intro he
  nlinarith [θ.property.2]

end Papers.AnsariRockel2024
