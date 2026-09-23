import Papers.AnsariRockel2024.ClaytonResults
import Copula.Dependence.ClaytonDensityFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open ProbabilityTheory Real MeasureTheory
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

/-- On a positive rectangle, integrating the mixed derivative in the second
coordinate recovers the first-derivative increment. -/
theorem clayton_density_formula_integral_second
    (θ u a b : ℝ) (hθ : 0 < θ)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    (∫ y in a..b,
      (1 + θ) * u ^ (-θ - 1) * y ^ (-θ - 1) *
        (claytonBaseReal θ u y) ^ (-2 - 1 / θ)) =
      u ^ (-θ - 1) * (claytonBaseReal θ u b) ^ (-1 / θ - 1) -
        u ^ (-θ - 1) * (claytonBaseReal θ u a) ^ (-1 / θ - 1) := by
  let f : ℝ → ℝ := fun y =>
    u ^ (-θ - 1) * (claytonBaseReal θ u y) ^ (-1 / θ - 1)
  let g : ℝ → ℝ := fun y =>
    (1 + θ) * u ^ (-θ - 1) * y ^ (-θ - 1) *
      (claytonBaseReal θ u y) ^ (-2 - 1 / θ)
  have hderiv (y : ℝ) (hy : y ∈ Set.uIcc a b) : HasDerivAt f (g y) y := by
    have hy' : y ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hy
    exact clayton_cdf_formula_hasDerivAt_second θ u y hθ hu
      (ha.trans_le hy'.1) hu1 (hy'.2.trans hb1)
  have hpow : ContinuousOn (fun y : ℝ => y ^ (-θ)) (Set.Icc a b) :=
    continuousOn_id.rpow_const (fun y hy => Or.inl
      (ne_of_gt (ha.trans_le hy.1)))
  have hbase : ContinuousOn (fun y : ℝ => claytonBaseReal θ u y)
      (Set.Icc a b) := by
    have hc : ContinuousOn (fun _ : ℝ => u ^ (-θ)) (Set.Icc a b) := continuousOn_const
    have h1 : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) := continuousOn_const
    convert (hc.add hpow).sub h1 using 1
    funext y
    simp [claytonBaseReal]
  have hpow2 : ContinuousOn (fun y : ℝ => y ^ (-θ - 1)) (Set.Icc a b) :=
    continuousOn_id.rpow_const (fun y hy => Or.inl
      (ne_of_gt (ha.trans_le hy.1)))
  have hpow3 : ContinuousOn (fun y : ℝ =>
      (claytonBaseReal θ u y) ^ (-2 - 1 / θ)) (Set.Icc a b) :=
    hbase.rpow_const (fun y hy => Or.inl
      ((claytonBaseReal_pos θ u y hθ hu (ha.trans_le hy.1)
        hu1 (hy.2.trans hb1)).ne'))
  have hg : ContinuousOn g (Set.Icc a b) := by
    dsimp [g]
    exact (continuousOn_const.mul hpow2).mul hpow3
  have hg' : ContinuousOn g (Set.uIcc a b) := by
    simpa [Set.uIcc_of_le hab] using hg
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hg'.intervalIntegrable

/-- Integrating the first partial derivative over a positive interval
recovers the Clayton CDF formula increment. -/
theorem clayton_cdf_formula_integral_first
    (θ v a b : ℝ) (hθ : 0 < θ)
    (hv : 0 < v) (hv1 : v ≤ 1)
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    (∫ x in a..b,
      x ^ (-θ - 1) * (claytonBaseReal θ x v) ^ (-1 / θ - 1)) =
      (claytonBaseReal θ b v) ^ (-1 / θ) -
        (claytonBaseReal θ a v) ^ (-1 / θ) := by
  let f : ℝ → ℝ := fun x =>
    (claytonBaseReal θ x v) ^ (-1 / θ)
  let g : ℝ → ℝ := fun x =>
    x ^ (-θ - 1) * (claytonBaseReal θ x v) ^ (-1 / θ - 1)
  have hderiv (x : ℝ) (hx : x ∈ Set.uIcc a b) : HasDerivAt f (g x) x := by
    have hx' : x ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hx
    exact clayton_cdf_formula_hasDerivAt_first θ x v hθ
      (ha.trans_le hx'.1) hv (hx'.2.trans hb1) hv1
  have hpow : ContinuousOn (fun x : ℝ => x ^ (-θ)) (Set.Icc a b) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl
      (ne_of_gt (ha.trans_le hx.1)))
  have hbase : ContinuousOn (fun x : ℝ => claytonBaseReal θ x v)
      (Set.Icc a b) := by
    have hc : ContinuousOn (fun _ : ℝ => v ^ (-θ)) (Set.Icc a b) := continuousOn_const
    have h1 : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) := continuousOn_const
    convert (hpow.add hc).sub h1 using 1
    funext x
    simp [claytonBaseReal]
  have hpow2 : ContinuousOn (fun x : ℝ => x ^ (-θ - 1)) (Set.Icc a b) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl
      (ne_of_gt (ha.trans_le hx.1)))
  have hpow3 : ContinuousOn (fun x : ℝ =>
      (claytonBaseReal θ x v) ^ (-1 / θ - 1)) (Set.Icc a b) :=
    hbase.rpow_const (fun x hx => Or.inl
      ((claytonBaseReal_pos θ x v hθ (ha.trans_le hx.1) hv
        (hx.2.trans hb1) hv1).ne'))
  have hg : ContinuousOn g (Set.Icc a b) := by
    dsimp [g]
    exact hpow2.mul hpow3
  have hg' : ContinuousOn g (Set.uIcc a b) := by
    simpa [Set.uIcc_of_le hab] using hg
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hg'.intervalIntegrable

private theorem clayton_first_derivative_intervalIntegrable
    (θ v a b : ℝ) (hθ : 0 < θ)
    (hv : 0 < v) (hv1 : v ≤ 1)
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    IntervalIntegrable (fun x : ℝ =>
      x ^ (-θ - 1) * (claytonBaseReal θ x v) ^ (-1 / θ - 1))
      volume a b := by
  have hpow : ContinuousOn (fun x : ℝ => x ^ (-θ)) (Set.Icc a b) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl
      (ne_of_gt (ha.trans_le hx.1)))
  have hbase : ContinuousOn (fun x : ℝ => claytonBaseReal θ x v)
      (Set.Icc a b) := by
    have hc : ContinuousOn (fun _ : ℝ => v ^ (-θ)) (Set.Icc a b) := continuousOn_const
    have h1 : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) := continuousOn_const
    convert (hpow.add hc).sub h1 using 1
    funext x
    simp [claytonBaseReal]
  have hpow2 : ContinuousOn (fun x : ℝ => x ^ (-θ - 1)) (Set.Icc a b) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl
      (ne_of_gt (ha.trans_le hx.1)))
  have hpow3 : ContinuousOn (fun x : ℝ =>
      (claytonBaseReal θ x v) ^ (-1 / θ - 1)) (Set.Icc a b) :=
    hbase.rpow_const (fun x hx => Or.inl
      ((claytonBaseReal_pos θ x v hθ (ha.trans_le hx.1) hv
        (hx.2.trans hb1) hv1).ne'))
  have hg : ContinuousOn (fun x : ℝ =>
      x ^ (-θ - 1) * (claytonBaseReal θ x v) ^ (-1 / θ - 1))
      (Set.Icc a b) := hpow2.mul hpow3
  have hg' : ContinuousOn (fun x : ℝ =>
      x ^ (-θ - 1) * (claytonBaseReal θ x v) ^ (-1 / θ - 1))
      (Set.uIcc a b) := by
    simpa [Set.uIcc_of_le hab] using hg
  exact hg'.intervalIntegrable (μ := (volume : MeasureTheory.Measure ℝ))

/-- The analytic Clayton density integrates to the exact CDF rectangle
increment on every rectangle bounded away from both axes. -/
theorem clayton_density_formula_positive_rectangle
    (θ a b c d : ℝ) (hθ : 0 < θ)
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hc : 0 < c) (hcd : c ≤ d) (hd1 : d ≤ 1) :
    (∫ x in a..b, ∫ y in c..d,
      (1 + θ) * x ^ (-θ - 1) * y ^ (-θ - 1) *
        (claytonBaseReal θ x y) ^ (-2 - 1 / θ)) =
      (claytonBaseReal θ b d) ^ (-1 / θ) -
        (claytonBaseReal θ a d) ^ (-1 / θ) -
        (claytonBaseReal θ b c) ^ (-1 / θ) +
        (claytonBaseReal θ a c) ^ (-1 / θ) := by
  have hinner :
      (∫ x in a..b, ∫ y in c..d,
        (1 + θ) * x ^ (-θ - 1) * y ^ (-θ - 1) *
          (claytonBaseReal θ x y) ^ (-2 - 1 / θ)) =
      ∫ x in a..b,
        x ^ (-θ - 1) * (claytonBaseReal θ x d) ^ (-1 / θ - 1) -
          x ^ (-θ - 1) * (claytonBaseReal θ x c) ^ (-1 / θ - 1) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hx
    exact clayton_density_formula_integral_second θ x c d hθ
      (ha.trans_le hx'.1) (hx'.2.trans hb1) hc hcd hd1
  rw [hinner, intervalIntegral.integral_sub
    (clayton_first_derivative_intervalIntegrable θ d a b hθ
      (hc.trans_le hcd) hd1 ha hab hb1)
    (clayton_first_derivative_intervalIntegrable θ c a b hθ
      hc (hcd.trans hd1) ha hab hb1),
    clayton_cdf_formula_integral_first θ d a b hθ
      (hc.trans_le hcd) hd1 ha hab hb1,
    clayton_cdf_formula_integral_first θ c a b hθ
      hc (hcd.trans hd1) ha hab hb1]
  ring

/-- On positive rectangles, the analytic density integrates to the mass of
that rectangle under the actual Clayton copula measure. -/
theorem clayton_density_formula_positive_rectangle_eq_measure
    (θ : ℝ) (hθ : 0 < θ) (a b c d : I)
    (ha : 0 < (a : ℝ)) (hab : a ≤ b)
    (hc : 0 < (c : ℝ)) (hcd : c ≤ d) :
    (∫ x in (a : ℝ)..(b : ℝ), ∫ y in (c : ℝ)..(d : ℝ),
      (1 + θ) * x ^ (-θ - 1) * y ^ (-θ - 1) *
        (claytonBaseReal θ x y) ^ (-2 - 1 / θ)) =
      (Copula.clayton 2 θ hθ).toMeasure.real
        (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i))) := by
  have hrect := clayton_density_formula_positive_rectangle θ
    (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) hθ ha hab b.property.2 hc hcd d.property.2
  rw [hrect, (Copula.clayton 2 θ hθ).measureReal_rectangle_two
    ![a, c] ![b, d] (by simpa [Pi.le_def, Fin.forall_fin_two] using And.intro hab hcd)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [clayton_cdf_positive_eq_analytic θ hθ b d (ha.trans_le hab) (hc.trans_le hcd),
    clayton_cdf_positive_eq_analytic θ hθ a d ha (hc.trans_le hcd),
    clayton_cdf_positive_eq_analytic θ hθ b c (ha.trans_le hab) hc,
    clayton_cdf_positive_eq_analytic θ hθ a c ha hc]

/-- The candidate's mass on the positive square with lower cutoff `r`
reaches the Clayton copula's corresponding square mass. -/
theorem clayton_density_formula_cutoff_square
    (θ : ℝ) (hθ : 0 < θ) (r : I) (hr : 0 < (r : ℝ)) :
    (∫ x in (r : ℝ)..1, ∫ y in (r : ℝ)..1,
      (1 + θ) * x ^ (-θ - 1) * y ^ (-θ - 1) *
        (claytonBaseReal θ x y) ^ (-2 - 1 / θ)) =
      1 - 2 * (r : ℝ) + (Copula.clayton 2 θ hθ).cdf ![r, r] := by
  have h := clayton_density_formula_positive_rectangle_eq_measure θ hθ
    r 1 r 1 hr (unitInterval.le_one _) hr (unitInterval.le_one _)
  rw [(Copula.clayton 2 θ hθ).measureReal_rectangle_two
    ![r, r] ![1, 1] (by simp [Pi.le_def, Fin.forall_fin_two, unitInterval.le_one'])] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Copula.cdf_two_one_left, Copula.cdf_two_one_right] at h
  norm_num at h
  convert h using 1 <;> ring_nf

/-- The positive cutoff-square mass lies between `1 - 2r` and `1 - r`.
This quantitative estimate is a boundary-control step for the density. -/
theorem clayton_density_formula_cutoff_square_bounds
    (θ : ℝ) (hθ : 0 < θ) (r : I) (hr : 0 < (r : ℝ)) :
    1 - 2 * (r : ℝ) ≤
      (∫ x in (r : ℝ)..1, ∫ y in (r : ℝ)..1,
        (1 + θ) * x ^ (-θ - 1) * y ^ (-θ - 1) *
          (claytonBaseReal θ x y) ^ (-2 - 1 / θ)) ∧
      (∫ x in (r : ℝ)..1, ∫ y in (r : ℝ)..1,
        (1 + θ) * x ^ (-θ - 1) * y ^ (-θ - 1) *
          (claytonBaseReal θ x y) ^ (-2 - 1 / θ)) ≤ 1 - (r : ℝ) := by
  rw [clayton_density_formula_cutoff_square θ hθ r hr]
  constructor
  · exact le_add_of_nonneg_right ((Copula.clayton 2 θ hθ).cdf_nonneg ![r, r])
  · have h := (Copula.clayton 2 θ hθ).cdf_le_coord ![r, r] 0
    simp only [Matrix.cons_val_zero] at h
    linarith

end Papers.AnsariRockel2024
