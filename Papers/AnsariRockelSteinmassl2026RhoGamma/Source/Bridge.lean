import Papers.AnsariRockelSteinmassl2026RhoGamma.Source.Article
import Papers.Common.UnitSquareCopula
import Papers.AnsariRockelSteinmassl2026RhoGamma.ElementaryArc
import Papers.AnsariRockelSteinmassl2026RhoGamma.ElementaryEndpoints
import Papers.AnsariRockelSteinmassl2026RhoGamma.SharpDiscrepancy
import Papers.AnsariRockelSteinmassl2026RhoGamma.SignThresholds
import Papers.AnsariRockelSteinmassl2026RhoGamma.BoundaryGeometry

/-! # The article's definitions are the library's notions

The copulas of the compiled article are the distribution functions `cdfOf K` of
library copulas `K : Copula 2`; its `ρ` and `γ` are `K.spearmanRho` and
`K.giniGamma`; its region `Ω_{ρ,γ}` is the companion's `region`; its maximum
`ρ̄(g)` is `upperRho g`; and its constants are the companion's radical
constants. Each identification is proved. -/

namespace Papers.AnsariRockelSteinmassl2026RhoGamma.Source.Bridge
open Papers.AnsariRockelSteinmassl2026RhoGamma.Source Proofread MeasureTheory ProbabilityTheory
open scoped unitInterval
open Papers.AnsariRockelSteinmassl2026RhoGamma (region upperRho sharp_upper_bound upper_boundary_attained)

export Papers.Common (cdfOf)

theorem copulas_cdfOf (K : Copula 2) : copulas (cdfOf K) := Papers.Common.isCopula_cdfOf K

theorem exists_of_copulas {F : I → I → ℝ} (hF : copulas F) : ∃ K : Copula 2, F = cdfOf K :=
  Papers.Common.exists_cdfOf hF

theorem rho_cdfOf (K : Copula 2) : rho (cdfOf K) = K.spearmanRho := Papers.Common.spearmanRho_cdfOf K

theorem gamma_cdfOf (K : Copula 2) : gamma (cdfOf K) = K.giniGamma := Papers.Common.giniGamma_cdfOf K

/-- `Ω_{ρ,γ}` is the companion's region. -/
theorem Omega_iff (r g : ℝ) : Omegarhogamma r g ↔ (r, g) ∈ region := by
  constructor
  · rintro ⟨F, hF, hr, hg⟩
    obtain ⟨K, rfl⟩ := exists_of_copulas hF
    rw [rho_cdfOf] at hr
    rw [gamma_cdfOf] at hg
    exact ⟨K, by simp only [hr, hg]⟩
  · rintro ⟨K, hK⟩
    simp only [Prod.mk.injEq] at hK
    exact ⟨cdfOf K, copulas_cdfOf K, by rw [rho_cdfOf, hK.1], by rw [gamma_cdfOf, hK.2]⟩

/-- A definite description with exactly one solution denotes it. -/
theorem epsilon_eq_of_unique {α : Type} [Nonempty α] {P : α → Prop} {a : α} (ha : P a)
    (hu : ∀ b, P b → b = a) : Classical.epsilon P = a :=
  hu _ (Classical.epsilon_spec ⟨a, ha⟩)

/-- The values of `ρ` at the copulas with `γ = g`. -/
theorem rho_values_iff (g y : ℝ) :
    (∃ F, (copulas F ∧ gamma F = g) ∧ y = rho F) ↔ ∃ K : Copula 2, K.giniGamma = g ∧ y = K.spearmanRho := by
  constructor
  · rintro ⟨F, ⟨hF, hg⟩, hy⟩
    obtain ⟨K, rfl⟩ := exists_of_copulas hF
    exact ⟨K, by rw [← gamma_cdfOf, hg], by rw [hy, rho_cdfOf]⟩
  · rintro ⟨K, hg, hy⟩
    exact ⟨cdfOf K, ⟨copulas_cdfOf K, by rw [gamma_cdfOf, hg]⟩, by rw [hy, rho_cdfOf]⟩

/-- `upperRho g` is the greatest value of `ρ` at `γ = g`. -/
theorem upperRho_isMax (g : ℝ) (hg : -1 ≤ g ∧ g ≤ 1) :
    (∃ F, (copulas F ∧ gamma F = g) ∧ upperRho g = rho F) ∧
      ∀ y, (∃ F, (copulas F ∧ gamma F = g) ∧ y = rho F) → y ≤ upperRho g := by
  obtain ⟨C, hC, hr⟩ := upper_boundary_attained (g := g) ⟨hg.1, hg.2⟩
  refine ⟨(rho_values_iff g _).2 ⟨C, hC, hr.symm⟩, fun y hy => ?_⟩
  obtain ⟨K, hK, rfl⟩ := (rho_values_iff g y).1 hy
  have := sharp_upper_bound K
  rw [hK] at this
  exact this

theorem rhoBar_eq (g : ℝ) (hg : -1 ≤ g ∧ g ≤ 1) : rhoBar g = upperRho g := by
  unfold rhoBar
  refine epsilon_eq_of_unique ?_ ?_
  · exact upperRho_isMax g hg
  rintro y ⟨hy, hmax⟩
  exact le_antisymm (( upperRho_isMax g hg).2 y hy) (hmax _ (upperRho_isMax g hg).1)

/-- `Ω_{ρ,γ}` as a set of points of the plane is the companion's `region`. -/
theorem Omega_set : {p : ℝ × ℝ | Omegarhogamma p.1 p.2} = region := by
  ext ⟨r, g⟩
  exact Omega_iff r g

/-! ## Radical constants -/

theorem rpow_half (x : ℝ) : x ^ (1 / 2 : ℝ) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm

theorem gStar_eq : gStar = Papers.AnsariRockelSteinmassl2026RhoGamma.elementaryGStar := by
  unfold gStar Papers.AnsariRockelSteinmassl2026RhoGamma.elementaryGStar
  rw [rpow_half 3]

theorem Delta0_eq : Delta0 = Papers.AnsariRockelSteinmassl2026RhoGamma.maximalDiscrepancy := by
  unfold Delta0 Papers.AnsariRockelSteinmassl2026RhoGamma.maximalDiscrepancy
  rw [rpow_half 10]

theorem r0_eq : r0 = Papers.AnsariRockelSteinmassl2026RhoGamma.rhoThreshold := by
  unfold r0 Papers.AnsariRockelSteinmassl2026RhoGamma.rhoThreshold
  rw [rpow_half 6]

theorem g0_eq : g0 = Papers.AnsariRockelSteinmassl2026RhoGamma.gammaThreshold := by
  unfold g0 Papers.AnsariRockelSteinmassl2026RhoGamma.gammaThreshold
  rw [rpow_half 69]

end Papers.AnsariRockelSteinmassl2026RhoGamma.Source.Bridge
