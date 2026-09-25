import Verification.ArchimedeanOrder
import Verification.ArchimedeanCD
import Papers.AnsariRockel2024.GeneralOrders

/-! # Proposition 3.3: ordering Archimedean copulas

Generators are inverse generators `ψ` in the library convention (`C=ψ(ψ⁻¹u+ψ⁻¹v)`).
Part (i) is proved for strict generators, where `ψ₁⁻¹ ∘ ψ₂` is defined on all of `[0,∞)`,
and in generator coordinates for arbitrary bivariate generators. Parts (ii) and (iii)
use the smooth log-convexity/log-concavity hypotheses of the paper to obtain CI/CD, and
then Lemmas 2.6 and 2.8.
-/

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

/-- Smooth strict inverse generator with log-convex `-ψ'` (hypothesis of Prop. 3.3(ii)). -/
def LogConvexNegDeriv (g : BivariateGenerator) : Prop :=
  ∃ φ φ' ψ' : ℝ → ℝ,
    (∀ u : I, 0<(u:ℝ) → (u:ℝ)<1 → φ u=g.invFun u) ∧
    (∀ u ∈ Ioo (0:ℝ) 1, 0<φ u) ∧
    (∀ u ∈ Ioo (0:ℝ) 1, HasDerivAt φ (φ' u) u) ∧
    (∀ t, 0<t → HasDerivAt g.toFun (ψ' t) t) ∧
    (∀ t, 0<t → ψ' t<0) ∧
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (-ψ' t))

/-- Smooth strict inverse generator with log-concave `-ψ'` (hypothesis of Prop. 3.3(iii)). -/
def LogConcaveNegDeriv (g : BivariateGenerator) : Prop :=
  ∃ φ φ' ψ' : ℝ → ℝ,
    (∀ u : I, 0<(u:ℝ) → (u:ℝ)<1 → φ u=g.invFun u) ∧
    (∀ u ∈ Ioo (0:ℝ) 1, 0<φ u) ∧
    (∀ u ∈ Ioo (0:ℝ) 1, HasDerivAt φ (φ' u) u) ∧
    (∀ t, 0<t → HasDerivAt g.toFun (ψ' t) t) ∧
    (∀ t, 0<t → ψ' t<0) ∧
    ConcaveOn ℝ (Ioi 0) (fun t => Real.log (-ψ' t))

theorem LogConvexNegDeriv.isCI {g : BivariateGenerator} (h : LogConvexNegDeriv g) : g.copula.IsCI := by
  obtain ⟨φ,φ',ψ',h1,h2,h3,h4,h5,h6⟩ := h
  exact Verification.generator_isCI_of_logconvex_neg_deriv g φ φ' ψ' h1 h2 h3 h4 h5 h6

theorem LogConcaveNegDeriv.isCD {g : BivariateGenerator} (h : LogConcaveNegDeriv g) : g.copula.IsCD := by
  obtain ⟨φ,φ',ψ',h1,h2,h3,h4,h5,h6⟩ := h
  exact Verification.generator_isCD_of_logconcave_neg_deriv g φ φ' ψ' h1 h2 h3 h4 h5 h6

/-- Proposition 3.3(i), generator coordinates, for arbitrary bivariate generators. -/
theorem archimedean_lowerOrthant_iff_generator (g₁ g₂ : BivariateGenerator) :
    g₁.copula.LowerOrthantLE g₂.copula ↔
      ∀ u v : I, u≠0 → v≠0 →
        g₁.toFun (g₁.invFun u+g₁.invFun v)≤g₂.toFun (g₂.invFun u+g₂.invFun v) :=
  BivariateGenerator.lowerOrthantLE_iff_generator g₁ g₂

/-- Proposition 3.3(i): for strict generators, `C₁ ≤_lo C₂` iff `ψ₁⁻¹∘ψ₂` is subadditive. -/
theorem archimedean_lowerOrthant_iff_subadditive (g₁ g₂ : BivariateGenerator)
    (h₁ : ∀ x, 0≤x → 0<g₁.toFun x) (h₂ : ∀ x, 0≤x → 0<g₂.toFun x) :
    g₁.copula.LowerOrthantLE g₂.copula ↔
      ∀ x y, 0≤x → 0≤y →
        BivariateGenerator.compose g₁ g₂ (x+y)≤
          BivariateGenerator.compose g₁ g₂ x+BivariateGenerator.compose g₁ g₂ y :=
  BivariateGenerator.lowerOrthantLE_iff_subadditive g₁ g₂ h₁ h₂

/-- Proposition 3.3(ii): with log-convex `-ψᵢ'`, subadditivity characterizes the
two-direction Schur order `C₁ ≤_∂S C₂`. -/
theorem archimedean_schur_iff_subadditive_of_logconvex (g₁ g₂ : BivariateGenerator)
    (h₁ : ∀ x, 0≤x → 0<g₁.toFun x) (h₂ : ∀ x, 0≤x → 0<g₂.toFun x)
    (hc₁ : LogConvexNegDeriv g₁) (hc₂ : LogConvexNegDeriv g₂) :
    g₁.copula.SchurBothLE g₂.copula ↔
      ∀ x y, 0≤x → 0≤y →
        BivariateGenerator.compose g₁ g₂ (x+y)≤
          BivariateGenerator.compose g₁ g₂ x+BivariateGenerator.compose g₁ g₂ y := by
  rw [schurBothLE_iff_of_archimedean g₁.isArchimedean g₂.isArchimedean,
    cis_schur_iff_orthant _ _ hc₁.isCI.1 hc₂.isCI.1]
  exact archimedean_lowerOrthant_iff_subadditive g₁ g₂ h₁ h₂

/-- Proposition 3.3(iii): with log-concave `-ψᵢ'`, subadditivity characterizes the
reversed two-direction Schur order `C₂ ≤_∂S C₁`. -/
theorem archimedean_schur_iff_subadditive_of_logconcave (g₁ g₂ : BivariateGenerator)
    (h₁ : ∀ x, 0≤x → 0<g₁.toFun x) (h₂ : ∀ x, 0≤x → 0<g₂.toFun x)
    (hc₁ : LogConcaveNegDeriv g₁) (hc₂ : LogConcaveNegDeriv g₂) :
    g₂.copula.SchurBothLE g₁.copula ↔
      ∀ x y, 0≤x → 0≤y →
        BivariateGenerator.compose g₁ g₂ (x+y)≤
          BivariateGenerator.compose g₁ g₂ x+BivariateGenerator.compose g₁ g₂ y := by
  rw [schurBothLE_iff_of_archimedean g₂.isArchimedean g₁.isArchimedean,
    cds_schur_iff_reverse_orthant _ _ hc₂.isCD.1 hc₁.isCD.1]
  exact archimedean_lowerOrthant_iff_subadditive g₁ g₂ h₁ h₂

end Papers.AnsariRockel2024
