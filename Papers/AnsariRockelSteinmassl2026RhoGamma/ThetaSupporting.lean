import Papers.AnsariRockelSteinmassl2026RhoGamma.StrongDuality
import Papers.AnsariRockelSteinmassl2026RhoGamma.ThetaBoundary

/-! # Theorem 4.2 in the original theta coordinates -/

open MeasureTheory ProbabilityTheory Copula.RankRegion
open scoped unitInterval

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

/-- Equation (46), including the attained primal, dual and supporting values. -/
theorem theta_transport_value (theta : ℝ) (ht : 0 < theta) :
    let A := thetaCertificate theta ht
    transportValue (thetaT theta) = 2 * ∫ u : I, A.dual u ∧
      (2 * ∫ u : I, A.dual u) = (thetaP theta - 3 / 2 * thetaT theta * thetaG theta) / 3 := by
  dsimp only
  let A := thetaCertificate theta ht
  have hf : Continuous (fun u : I => A.dual u) := A.continuous_dual.comp continuous_subtype_val
  have hv := transport_contact_value A.magnitudes A.t hf A.magnitude_contact
  have hopt := (transport_contact_optimal A.magnitudes A.t hf
    (fun x => A.dual_feasible (x 0) (x 1)) A.magnitude_contact).1
  obtain ⟨D, hD, hmax⟩ := transportValue_attained A.t
  have he : transportValue A.t = 2 * ∫ u : I, A.dual u := by
    have h1 := hopt D
    have h2 := hmax A.magnitudes
    rw [hD, hv] at h1
    rw [hv] at h2
    exact le_antisymm h1 h2
  have hs := theta_splitting theta ht
  dsimp only at hs
  have ht' : A.t = thetaT theta := hs.2.1
  refine ⟨ht' ▸ he, ?_⟩
  have hv' := RhoGamma.signOptimizer_value A.magnitudes A.t
  change A.copula.spearmanRho - 3 / 2 * A.t * A.copula.giniGamma =
    3 * ∫ x, magnitudeCost A.t x ∂A.magnitudes.toMeasure at hv'
  rw [hv, ht', (theta_boundary_coefficients theta ht).1,
    (theta_boundary_coefficients theta ht).2] at hv'
  linarith

/-- Equation (47), with the exact source multiplier and coordinates. -/
theorem theta_supporting_inequality (theta : ℝ) (ht : 0 < theta) (C : Copula 2) :
    C.spearmanRho - 3 / 2 * thetaT theta * C.giniGamma ≤
      thetaP theta - 3 / 2 * thetaT theta * thetaG theta := by
  have h := (thetaCertificate theta ht).supporting_bound C
  rw [(theta_splitting theta ht).2.1, (theta_boundary_coefficients theta ht).1,
    (theta_boundary_coefficients theta ht).2] at h
  exact h

end Papers.AnsariRockelSteinmassl2026RhoGamma
