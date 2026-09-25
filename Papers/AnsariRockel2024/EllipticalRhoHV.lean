import Papers.AnsariRockel2024.EllipticalRho

/-! # Table 6: Student-t and Laplace Spearman rho in Heinen–Valdesogo form

Heinen and Valdesogo (2020, Proposition 1) write Spearman's rho of a normal variance
mixture as `(6/π) E[arcsin(r V)]` with `V = W₃/√((W₁+W₃)(W₂+W₃))` for three independent
copies `Wᵢ` of the mixing variance. For Student-t the variance is the reciprocal of a
`Gamma(ν/2,ν/2)` precision (inverse gamma); for Laplace it is `Gamma(1,1)`. The verified
scale expectations are rewritten in exactly this variable.
-/

open MeasureTheory ProbabilityTheory

namespace Papers.AnsariRockel2024

/-- The Heinen–Valdesogo mixing variable. -/
noncomputable def hvV (w₁ w₂ w₃ : ℝ) : ℝ := w₃ / Real.sqrt ((w₁ + w₃) * (w₂ + w₃))

theorem hv_integrand (r x y z : ℝ) :
    r * z ^ 2 / (Real.sqrt (z ^ 2 + x ^ 2) * Real.sqrt (z ^ 2 + y ^ 2)) =
      r * hvV (x ^ 2) (y ^ 2) (z ^ 2) := by
  unfold hvV
  rw [← Real.sqrt_mul (by positivity), show (x ^ 2 + z ^ 2) * (y ^ 2 + z ^ 2) =
    (z ^ 2 + x ^ 2) * (z ^ 2 + y ^ 2) by ring]
  ring

/-- Table 6: Student-t rho as `(6/π)E[arcsin(rṼ₁)]`, `Wᵢ` inverse-gamma(ν/2,ν/2). -/
theorem student_spearmanRho_hv (r : ℝ) (hr : r ∈ Set.Icc (-1) 1) (ν : ℝ) (hν : 0 < ν) :
    let μ := gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)
    let W := fun t : ℝ => ((Real.sqrt t)⁻¹) ^ 2
    (Verification.studentBivariate r hr ν hν).spearmanRho =
      6 / Real.pi * (∫ a, ∫ t : ℝ × ℝ, Real.arcsin (r * hvV (W t.1) (W t.2) (W a))
        ∂μ.toMeasure.prod μ.toMeasure ∂μ.toMeasure) := by
  intro μ W
  rw [student_spearmanRho r hr ν hν]
  simp only [W, hv_integrand]
  rfl

/-- Table 6: Laplace rho as `(6/π)E[arcsin(rṼ₂)]`, `Wᵢ` exponential(1). -/
theorem laplace_spearmanRho_hv (r : ℝ) (hr : r ∈ Set.Icc (-1) 1) :
    let μ := gammaProbability 1 1 zero_lt_one zero_lt_one
    let W := fun t : ℝ => (Real.sqrt t) ^ 2
    (Verification.laplaceBivariate r hr).spearmanRho =
      6 / Real.pi * (∫ a, ∫ t : ℝ × ℝ, Real.arcsin (r * hvV (W t.1) (W t.2) (W a))
        ∂μ.toMeasure.prod μ.toMeasure ∂μ.toMeasure) := by
  intro μ W
  rw [laplace_spearmanRho r hr]
  simp only [W, hv_integrand]
  rfl

end Papers.AnsariRockel2024
