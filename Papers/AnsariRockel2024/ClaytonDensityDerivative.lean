import Papers.AnsariRockel2024.ClaytonResults
import Copula.Dependence.ClaytonDensityFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open ProbabilityTheory Real
open scoped unitInterval

namespace Papers.AnsariRockel2024

private noncomputable def claytonBaseReal (θ u v : ℝ) : ℝ :=
  u ^ (-θ) + v ^ (-θ) - 1

private theorem claytonBaseReal_pos (θ u v : ℝ) (hθ : 0 < θ)
    (hu : 0 < u) (hv : 0 < v) (hu1 : u ≤ 1) (hv1 : v ≤ 1) :
    0 < claytonBaseReal θ u v := by
  have hx : 1 ≤ u ^ (-θ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu hu1 (by linarith)
  have hy : 1 ≤ v ^ (-θ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv hv1 (by linarith)
  dsimp [claytonBaseReal]
  linarith

/-- The analytic expression below is the CDF of the actual positive-Clayton
copula on strictly positive unit coordinates. -/
theorem clayton_cdf_positive_eq_analytic
    (θ : ℝ) (hθ : 0 < θ) (u v : I)
    (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) :
    (Copula.clayton 2 θ hθ).cdf ![u, v] =
      (claytonBaseReal θ (u : ℝ) (v : ℝ)) ^ (-1 / θ) := by
  simpa only [claytonBaseReal] using clayton_positive_cdf θ hθ u v hu hv

/-- The actual positive-Clayton CDF formula has the expected first partial
derivative on the positive unit square. -/
theorem clayton_cdf_formula_hasDerivAt_first
    (θ u v : ℝ) (hθ : 0 < θ)
    (hu : 0 < u) (hv : 0 < v) (hu1 : u ≤ 1) (hv1 : v ≤ 1) :
    HasDerivAt (fun x : ℝ => (claytonBaseReal θ x v) ^ (-1 / θ))
      (u ^ (-θ - 1) * (claytonBaseReal θ u v) ^ (-1 / θ - 1)) u := by
  have hb := claytonBaseReal_pos θ u v hθ hu hv hu1 hv1
  have huPow : HasDerivAt (fun x : ℝ => x ^ (-θ))
      ((-θ) * u ^ (-θ - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu.ne')
  have hbase : HasDerivAt (fun x : ℝ => claytonBaseReal θ x v)
      ((-θ) * u ^ (-θ - 1)) u := by
    convert (huPow.add_const ((v ^ (-θ)) - 1)) using 1
    funext x
    simp only [claytonBaseReal]
    ring
  have hp := hbase.rpow_const (Or.inl hb.ne') (p := -1 / θ)
  convert hp using 1
  field_simp [hθ.ne']

/-- The mixed derivative of the positive-Clayton CDF formula is its standard
density formula on the positive unit square. -/
theorem clayton_cdf_formula_hasDerivAt_second
    (θ u v : ℝ) (hθ : 0 < θ)
    (hu : 0 < u) (hv : 0 < v) (hu1 : u ≤ 1) (hv1 : v ≤ 1) :
    HasDerivAt (fun y : ℝ =>
      u ^ (-θ - 1) * (claytonBaseReal θ u y) ^ (-1 / θ - 1))
      ((1 + θ) * u ^ (-θ - 1) * v ^ (-θ - 1) *
        (claytonBaseReal θ u v) ^ (-2 - 1 / θ)) v := by
  have hb := claytonBaseReal_pos θ u v hθ hu hv hu1 hv1
  have hvPow : HasDerivAt (fun y : ℝ => y ^ (-θ))
      ((-θ) * v ^ (-θ - 1)) v :=
    Real.hasDerivAt_rpow_const (Or.inl hv.ne')
  have hbase : HasDerivAt (fun y : ℝ => claytonBaseReal θ u y)
      ((-θ) * v ^ (-θ - 1)) v := by
    convert (hvPow.const_add (u ^ (-θ) - 1)) using 1
    funext y
    simp only [claytonBaseReal]
    ring
  have hp := hbase.rpow_const (Or.inl hb.ne') (p := -1 / θ - 1)
  have hd := hp.const_mul (u ^ (-θ - 1))
  convert hd using 1
  field_simp [hθ.ne']
  ring_nf

/-- The analytic mixed derivative is exactly the pinned copula package's
candidate density at every strictly positive coordinate. -/
theorem clayton_mixed_derivative_eq_densityFormula
    (θ : ℝ) (hθ : 0 < θ) (u v : I)
    (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) :
    deriv (fun y : ℝ =>
      (u : ℝ) ^ (-θ - 1) *
        (claytonBaseReal θ (u : ℝ) y) ^ (-1 / θ - 1)) (v : ℝ) =
      Copula.claytonDensityFormula θ ![u, v] := by
  have hd := (clayton_cdf_formula_hasDerivAt_second θ u v hθ hu hv
    u.property.2 v.property.2).deriv
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    norm_num at hu
  have hv0 : v ≠ 0 := by
    intro h
    subst v
    norm_num at hv
  calc
    _ = (1 + θ) * (u : ℝ) ^ (-θ - 1) * (v : ℝ) ^ (-θ - 1) *
      (claytonBaseReal θ (u : ℝ) (v : ℝ)) ^ (-2 - 1 / θ) := hd
    _ = Copula.claytonDensityFormula θ ![u, v] := by
      change (1 + θ) * (u : ℝ) ^ (-θ - 1) * (v : ℝ) ^ (-θ - 1) *
        (claytonBaseReal θ (u : ℝ) (v : ℝ)) ^ (-2 - 1 / θ) =
        (1 + θ) * (u : ℝ) ^ (-θ - 1) * (v : ℝ) ^ (-θ - 1) *
          (if u = 0 ∨ v = 0 then 0 else
            ((u : ℝ) ^ (-θ) + (v : ℝ) ^ (-θ) - 1) ^ (-2 - 1 / θ))
      simp [claytonBaseReal, hu0, hv0]

end Papers.AnsariRockel2024
