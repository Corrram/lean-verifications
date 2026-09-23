import Copula.Families.Clayton.CDF
import Copula.Families.Clayton.Negative
import Copula.Families.Clayton.Limits
import Copula.Dependence.Clayton

/-! # Clayton family: full bivariate CDF branches and limiting cases -/

open ProbabilityTheory Filter
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

/-- Tables 1–2: the Clayton CDF for positive parameters at positive coordinates. -/
theorem clayton_positive_cdf (θ : ℝ) (hθ : 0 < θ) (u v : I)
    (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) :
    (Copula.clayton 2 θ hθ).cdf ![u, v] =
      ((u : ℝ) ^ (-θ) + (v : ℝ) ^ (-θ) - 1) ^ (-1 / θ) := by
  exact Copula.cdf_clayton_two_pos θ hθ u v hu hv

/-- Tables 1–2: the negative Clayton branch, with truncation before the power. -/
theorem clayton_negative_cdf (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0) (u v : I)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    (Copula.claytonNegative θ hθ hn).cdf ![u, v] =
      (max 0 ((u : ℝ) ^ (-θ) + (v : ℝ) ^ (-θ) - 1)) ^ (-θ)⁻¹ := by
  exact Copula.cdf_claytonNegative θ hθ hn ![u, v] (by
    intro i
    fin_cases i
    · simpa using hu
    · simpa using hv)

/-- Table 1: the positive Clayton CDF vanishes on the coordinate axes. -/
theorem clayton_positive_zero_axes (θ : ℝ) (hθ : 0 < θ) (u v : I) :
    (Copula.clayton 2 θ hθ).cdf ![0, v] = 0 ∧
      (Copula.clayton 2 θ hθ).cdf ![u, 0] = 0 := by
  constructor
  · exact (Copula.clayton 2 θ hθ).cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl
  · exact (Copula.clayton 2 θ hθ).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl

/-- Table 1: the negative Clayton CDF also vanishes on the coordinate axes. -/
theorem clayton_negative_zero_axes (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0) (u v : I) :
    (Copula.claytonNegative θ hθ hn).cdf ![0, v] = 0 ∧
      (Copula.claytonNegative θ hθ hn).cdf ![u, 0] = 0 := by
  constructor
  · exact (Copula.claytonNegative θ hθ hn).cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl
  · exact (Copula.claytonNegative θ hθ hn).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl

/-- Table 2: the positive-parameter θ = 1 special case on the open square. -/
theorem clayton_one_cdf (u v : I) (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) :
    (Copula.clayton 2 1 (by norm_num)).cdf ![u, v] =
      (u : ℝ) * (v : ℝ) / ((u : ℝ) + (v : ℝ) - (u : ℝ) * (v : ℝ)) := by
  rw [clayton_positive_cdf 1 (by norm_num) u v hu hv]
  norm_num
  rw [Real.rpow_neg_one, Real.rpow_neg_one, Real.rpow_neg_one]
  have hden : 0 < (u : ℝ) + (v : ℝ) - (u : ℝ) * (v : ℝ) := by
    have h := mul_nonneg hu.le (sub_nonneg.mpr v.property.2)
    nlinarith
  field_simp [ne_of_gt hu, ne_of_gt hv, ne_of_gt hden]
  have hq : ((u : ℝ) + (v : ℝ) - (u : ℝ) * (v : ℝ)) *
      ((u : ℝ) + (v : ℝ) - (u : ℝ) * (v : ℝ))⁻¹ = 1 := by
    exact mul_inv_cancel₀ (ne_of_gt hden)
  convert hq using 1; ring

/-- Table 2: the θ = −1 copula is the lower Fréchet bound. -/
theorem clayton_negative_one :
    Copula.claytonNegative (-1) le_rfl (by norm_num) = Copula.countermonotonic :=
  Copula.claytonNegative_neg_one

/-- Table 3: a proved necessary consequence of positive Clayton's CI entry. -/
theorem clayton_positive_pqd (θ : ℝ) (hθ : 0 < θ) :
    (Copula.clayton 2 θ hθ).IsPQD :=
  Copula.isPQD_clayton_positive θ hθ

/-- Table 2: positive Clayton parameters tending to zero give independence. -/
theorem clayton_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 0 < θ a) (hlim : Tendsto θ l (𝓝 0)) (u : Fin 2 → I) :
    Tendsto (fun a => (Copula.clayton 2 (θ a) (hθ a)).cdf u) l
      (𝓝 ((Copula.independence 2).cdf u)) :=
  Copula.tendsto_clayton_zero θ hθ hlim u

/-- Table 2: positive Clayton parameters tending to infinity give the upper bound. -/
theorem clayton_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 0 < θ a) (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun a => (Copula.clayton 2 (θ a) (hθ a)).cdf u) l
      (𝓝 ((Copula.comonotonic 2).cdf u)) :=
  Copula.tendsto_clayton_atTop θ hθ hlim u

end Papers.AnsariRockel2024