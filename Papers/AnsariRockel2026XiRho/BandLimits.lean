import Papers.AnsariRockel2026XiRho.BandSymmetry
import Verification.BandUniformBounds
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! # Proposition 3: all three uniform limiting cases -/

open ProbabilityTheory Verification Filter
open scoped unitInterval Topology

namespace Papers.AnsariRockel2026XiRho

theorem sourceBand_independence_error (b : ℝ) (hb : 0 < b) (u v : I) :
    |(sourceBand b hb).cdf ![u,v] - (u : ℝ)*(v : ℝ)| ≤ b := by
  rw [sourceBand_eq_normalizedBand]
  exact diagonalBand_independence_error b hb.le u v

theorem sourceBand_comonotonic_error (b : ℝ) (hb : 0 < b) (u v : I) :
    |(sourceBand b hb).cdf ![u,v] - min (u : ℝ) (v : ℝ)| ≤ 1/b := by
  rw [sourceBand_eq_normalizedBand]
  exact diagonalBand_comonotonic_error b hb u v

theorem negativeSourceBand_independence_error (b : ℝ) (hb : 0 < b) (u v : I) :
    |(negativeSourceBand b hb).cdf ![u,v] - (u : ℝ)*(v : ℝ)| ≤ b := by
  rw [negativeSourceBand_cdf]
  have h := sourceBand_independence_error b hb (unitInterval.symm u) v
  change |(sourceBand b hb).cdf ![unitInterval.symm u,v] - (1-(u : ℝ))*(v : ℝ)| ≤ b at h
  convert h using 1
  rw [show (v : ℝ) - (sourceBand b hb).cdf ![unitInterval.symm u,v] - (u : ℝ)*v =
    -((sourceBand b hb).cdf ![unitInterval.symm u,v] - (1-(u : ℝ))*v) by ring, abs_neg]

theorem negativeSourceBand_countermonotonic_error (b : ℝ) (hb : 0 < b) (u v : I) :
    |(negativeSourceBand b hb).cdf ![u,v] - max ((u : ℝ)+(v : ℝ)-1) 0| ≤ 1/b := by
  rw [negativeSourceBand_cdf]
  have h := sourceBand_comonotonic_error b hb (unitInterval.symm u) v
  change |(sourceBand b hb).cdf ![unitInterval.symm u,v] - min (1-(u : ℝ)) (v : ℝ)| ≤ 1/b at h
  have he : max ((u : ℝ)+(v : ℝ)-1) 0 = v-min (1-(u : ℝ)) (v : ℝ) := by
    rcases le_total (1-(u : ℝ)) (v : ℝ) with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]; ring
    · rw [min_eq_right h, max_eq_right (by linarith)]; ring
  rw [he]
  convert h using 1
  rw [show (v : ℝ) - (sourceBand b hb).cdf ![unitInterval.symm u,v] -
    ((v : ℝ)-min (1-(u : ℝ)) (v : ℝ)) =
    -((sourceBand b hb).cdf ![unitInterval.symm u,v] - min (1-(u : ℝ)) (v : ℝ)) by ring, abs_neg]

/-- Any positive parameter net approaching zero converges uniformly to independence. -/
theorem sourceBand_tendstoUniformly_zero {α : Type*} {l : Filter α}
    (b : α → ℝ) (hb : ∀ a, 0 < b a) (hlim : Tendsto b l (𝓝 0)) :
    TendstoUniformly (fun a => (sourceBand (b a) (hb a)).cdf) (Copula.independence 2).cdf l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with a ha u
  have he : ![u 0,u 1] = u := by ext i; fin_cases i <;> rfl
  have h := sourceBand_independence_error (b a) (hb a) (u 0) (u 1)
  rw [he] at h
  simpa only [Real.dist_eq, abs_sub_comm, Copula.cdf_independence, Fin.prod_univ_two] using h.trans_lt ha

/-- The negative branch also converges uniformly to independence as its magnitude vanishes. -/
theorem negativeSourceBand_tendstoUniformly_zero {α : Type*} {l : Filter α}
    (b : α → ℝ) (hb : ∀ a, 0 < b a) (hlim : Tendsto b l (𝓝 0)) :
    TendstoUniformly (fun a => (negativeSourceBand (b a) (hb a)).cdf) (Copula.independence 2).cdf l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with a ha u
  have he : ![u 0,u 1] = u := by ext i; fin_cases i <;> rfl
  have h := negativeSourceBand_independence_error (b a) (hb a) (u 0) (u 1)
  rw [he] at h
  simpa only [Real.dist_eq, abs_sub_comm, Copula.cdf_independence, Fin.prod_univ_two] using h.trans_lt ha

/-- Parameters tending to positive infinity converge uniformly to M. -/
theorem sourceBand_tendstoUniformly_atTop {α : Type*} {l : Filter α}
    (b : α → ℝ) (hb : ∀ a, 0 < b a) (hlim : Tendsto b l atTop) :
    TendstoUniformly (fun a => (sourceBand (b a) (hb a)).cdf) (Copula.comonotonic 2).cdf l := by
  have hi : Tendsto (fun a => 1/b a) l (𝓝 0) := by simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hlim
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hi).2 ε hε] with a ha u
  have he : ![u 0,u 1] = u := by ext i; fin_cases i <;> rfl
  have h := sourceBand_comonotonic_error (b a) (hb a) (u 0) (u 1)
  rw [he] at h
  have hm : (⨅ i, u i : I) = min (u 0) (u 1) := by
    apply le_antisymm (le_min (iInf_le _ 0) (iInf_le _ 1))
    apply le_iInf
    intro i
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  rw [Real.dist_eq, Copula.cdf_comonotonic, hm, abs_sub_comm]
  exact h.trans_lt ha

/-- Negative parameters with magnitude tending to infinity converge uniformly to W. -/
theorem negativeSourceBand_tendstoUniformly_atTop {α : Type*} {l : Filter α}
    (b : α → ℝ) (hb : ∀ a, 0 < b a) (hlim : Tendsto b l atTop) :
    TendstoUniformly (fun a => (negativeSourceBand (b a) (hb a)).cdf) Copula.countermonotonic.cdf l := by
  have hi : Tendsto (fun a => 1/b a) l (𝓝 0) := by simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hlim
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hi).2 ε hε] with a ha u
  have he : ![u 0,u 1] = u := by ext i; fin_cases i <;> rfl
  have h := negativeSourceBand_countermonotonic_error (b a) (hb a) (u 0) (u 1)
  rw [he] at h
  simpa only [Real.dist_eq, abs_sub_comm, Copula.cdf_countermonotonic, max_comm] using h.trans_lt ha

end Papers.AnsariRockel2026XiRho
