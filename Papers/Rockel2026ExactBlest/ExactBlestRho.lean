import Papers.Rockel2026ExactBlest.ExactBlestRandomized

/-! The complete rho/Blest region of exact-blest-regions.tex in natural parameters.
Supporting inequalities use explicit potentials, independently of the general
rearrangement lemma. Boundary-copula uniqueness is not asserted. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
open Papers.Rockel2026XiBlest

namespace Papers.Rockel2026ExactBlest
noncomputable section
set_option maxHeartbeats 4000000

def rhoParamPhi (t x : ℝ) : ℝ :=
  if x ≤ t then (4 / 3) * |x - t / 2| ^ 3 else 2 * x ^ 3 / 3 - t * x ^ 2 / 2
def rhoParamPsi (t z : ℝ) : ℝ :=
  if z ≤ t then z ^ 3 / 12 - t ^ 2 * z / 4 else z ^ 3 / 3 - t * z ^ 2 / 2

theorem rho_param_cell00 (t x z : ℝ) (hz : 0 ≤ z) :
    0 ≤ (4 / 3) * |x - t / 2| ^ 3 + (z ^ 3 / 12 - t ^ 2 * z / 4) - (x ^ 2 - t * x) * z := by
  have he : (4 / 3) * |x - t / 2| ^ 3 + (z ^ 3 / 12 - t ^ 2 * z / 4) - (x ^ 2 - t * x) * z =
      (z - 2 * |x - t / 2|) ^ 2 * (z + 4 * |x - t / 2|) / 12 := by
    have hs : x ^ 2 - t * x = |x - t / 2| ^ 2 - t ^ 2 / 4 := by rw [sq_abs]; ring
    rw [hs]
    ring
  rw [he]
  positivity

theorem rho_param_cell01 (t x z : ℝ) (ht : 0 ≤ t) (hx : x ∈ Icc 0 t) (hz : t ≤ z) :
    0 ≤ (4 / 3) * |x - t / 2| ^ 3 + (z ^ 3 / 3 - t * z ^ 2 / 2) - (x ^ 2 - t * x) * z := by
  have hq : 0 ≤ t ^ 2 / 4 - |x - t / 2| ^ 2 := by
    rw [sq_abs]
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have he : (4 / 3) * |x - t / 2| ^ 3 + (z ^ 3 / 3 - t * z ^ 2 / 2) - (x ^ 2 - t * x) * z =
      (t - 2 * |x - t / 2|) ^ 2 * (t + 4 * |x - t / 2|) / 12 +
      (t ^ 2 / 4 - |x - t / 2| ^ 2) * (z - t) + t / 2 * (z - t) ^ 2 + (z - t) ^ 3 / 3 := by
    have hs : x ^ 2 - t * x = |x - t / 2| ^ 2 - t ^ 2 / 4 := by rw [sq_abs]; ring
    rw [hs]
    ring
  rw [he]
  have hzt : 0 ≤ z - t := sub_nonneg.mpr hz
  positivity

theorem rho_param_cell10 (t x z : ℝ) (ht : 0 ≤ t) (hx : t ≤ x) (hz : z ∈ Icc 0 t) :
    0 ≤ (2 * x ^ 3 / 3 - t * x ^ 2 / 2) + (z ^ 3 / 12 - t ^ 2 * z / 4) - (x ^ 2 - t * x) * z := by
  have he : (2 * x ^ 3 / 3 - t * x ^ 2 / 2) + (z ^ 3 / 12 - t ^ 2 * z / 4) - (x ^ 2 - t * x) * z =
      (z - t) ^ 2 * (z + 2 * t) / 12 + t * (t - z) * (x - t) +
        (3 * t / 2 - z) * (x - t) ^ 2 + 2 * (x - t) ^ 3 / 3 := by ring
  rw [he]
  have hz0 := hz.1
  have htz : 0 ≤ t - z := sub_nonneg.mpr hz.2
  have hxt : 0 ≤ x - t := sub_nonneg.mpr hx
  have hc : 0 ≤ 3 * t / 2 - z := by linarith [hz.2]
  positivity

theorem rho_param_cell11 (t x z : ℝ) (ht : 0 ≤ t) (hx : t ≤ x) (hz : t ≤ z) :
    0 ≤ (2 * x ^ 3 / 3 - t * x ^ 2 / 2) + (z ^ 3 / 3 - t * z ^ 2 / 2) - (x ^ 2 - t * x) * z := by
  have he : (2 * x ^ 3 / 3 - t * x ^ 2 / 2) + (z ^ 3 / 3 - t * z ^ 2 / 2) - (x ^ 2 - t * x) * z =
      (x - z) ^ 2 * ((2 * x + z) / 3 - t / 2) := by ring
  rw [he]
  have hp : 0 ≤ (2 * x + z) / 3 - t / 2 := by linarith
  positivity

theorem rho_param_dual (t x z : ℝ) (ht : 0 ≤ t) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    (x ^ 2 - t * x) * z ≤ rhoParamPhi t x + rhoParamPsi t z := by
  by_cases hxt : x ≤ t <;> by_cases hzt : z ≤ t
  · simpa only [rhoParamPhi, rhoParamPsi, ite_eq_left hxt, ite_eq_left hzt, sub_nonneg] using
      rho_param_cell00 t x z hz
  · simpa only [rhoParamPhi, rhoParamPsi, ite_eq_left hxt, ite_eq_right hzt, sub_nonneg] using
      rho_param_cell01 t x z ht ⟨hx, hxt⟩ (by linarith)
  · simpa only [rhoParamPhi, rhoParamPsi, ite_eq_right hxt, ite_eq_left hzt, sub_nonneg] using
      rho_param_cell10 t x z ht (by linarith) ⟨hz, hzt⟩
  · simpa only [rhoParamPhi, rhoParamPsi, ite_eq_right hxt, ite_eq_right hzt, sub_nonneg] using
      rho_param_cell11 t x z ht (by linarith) (by linarith)

#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_param_cell00
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_param_cell01
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_param_cell10
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_param_cell11
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_param_dual

def rhoPhiLo (t x : ℝ) : ℝ := (4 / 3) * (t / 2 - x) ^ 3
def rhoPhiMid (t x : ℝ) : ℝ := (4 / 3) * (x - t / 2) ^ 3
def rhoPhiHi (t x : ℝ) : ℝ := 2 * x ^ 3 / 3 - t * x ^ 2 / 2

theorem rhoPhi_threePieces (t : I) :
    rhoParamPhi t = threePieces ((t : ℝ) / 2) t (rhoPhiLo t) (rhoPhiMid t) (rhoPhiHi t) := by
  funext x
  unfold rhoParamPhi threePieces rhoPhiLo rhoPhiMid rhoPhiHi
  by_cases hx : x ≤ (t : ℝ) / 2
  · have ht : x ≤ (t : ℝ) := by linarith [t.property.1]
    simp only [ite_eq_left hx, ite_eq_left ht]
    rw [abs_of_nonpos (by linarith : x - (t : ℝ) / 2 ≤ 0)]
    ring
  · by_cases ht : x ≤ (t : ℝ)
    · simp only [ite_eq_right hx, ite_eq_left ht]
      rw [abs_of_nonneg (by linarith : 0 ≤ x - (t : ℝ) / 2)]
    · simp only [ite_eq_right hx, ite_eq_right ht]

theorem integral_rhoParamPhi (t : I) :
    (∫ u : I, rhoParamPhi t u) = (t : ℝ) ^ 4 / 24 - (t : ℝ) / 6 + 1 / 6 := by
  rw [rhoPhi_threePieces, integral_threePieces _ _
    ⟨by linarith [t.property.1], by linarith [t.property.2]⟩ t.property
    (by linarith [t.property.1]) _ _ _
    (by unfold rhoPhiLo; fun_prop) (by unfold rhoPhiMid; fun_prop) (by unfold rhoPhiHi; fun_prop)]
  have he0 : rhoPhiHi t = fun x : ℝ => (2/3) * x ^ 3 + (-(t : ℝ)/2) * x ^ 2 + (0) * x + (0) := by
    funext x; unfold rhoPhiHi; ring
  have he1 : (fun x : ℝ => rhoPhiMid t x - rhoPhiHi t x) = fun x : ℝ => (2/3) * x ^ 3 + (-3 * (t : ℝ)/2) * x ^ 2 + ((t : ℝ) ^ 2) * x + (-(t : ℝ) ^ 3/6) := by
    funext x; unfold rhoPhiMid rhoPhiHi; ring
  have he2 : (fun x : ℝ => rhoPhiLo t x - rhoPhiMid t x) = fun x : ℝ => (-8/3) * x ^ 3 + (4 * (t : ℝ)) * x ^ 2 + (-2 * (t : ℝ) ^ 2) * x + ((t : ℝ) ^ 3/3) := by
    funext x; unfold rhoPhiLo rhoPhiMid; ring
  rw [he1, he2, he0, Copula.integral_unitInterval (fun x : ℝ => (2/3) * x ^ 3 + (-(t : ℝ)/2) * x ^ 2 + (0) * x + (0)),
    integral_poly3, integral_poly3, integral_poly3]
  ring

theorem integral_rhoParamPsi (t : I) :
    (∫ u : I, rhoParamPsi t u) = -(t : ℝ) ^ 4 / 48 - (t : ℝ) / 6 + 1 / 12 := by
  change (∫ u : I, if (u : ℝ) ≤ t then (u : ℝ) ^ 3 / 12 - (t : ℝ) ^ 2 * (u : ℝ) / 4
    else (u : ℝ) ^ 3 / 3 - (t : ℝ) * (u : ℝ) ^ 2 / 2) = _
  rw [integral_unit_piecewise
    (fun x : ℝ => x ^ 3 / 12 - (t : ℝ) ^ 2 * x / 4)
    (fun x : ℝ => x ^ 3 / 3 - (t : ℝ) * x ^ 2 / 2)
    (by fun_prop) (by fun_prop) t t.property]
  have he0 : (fun x : ℝ => x ^ 3 / 12 - (t : ℝ) ^ 2 * x / 4) = fun x : ℝ => (1/12) * x ^ 3 + (0) * x ^ 2 + (-(t : ℝ) ^ 2/4) * x + (0) := by funext x; ring
  have he1 : (fun x : ℝ => x ^ 3 / 3 - (t : ℝ) * x ^ 2 / 2) = fun x : ℝ => (1/3) * x ^ 3 + (-(t : ℝ)/2) * x ^ 2 + (0) * x + (0) := by funext x; ring
  rw [he0, he1, integral_poly3, integral_poly3]
  ring

#assert_standard_axioms Papers.Rockel2026ExactBlest.rhoPhi_threePieces
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_rhoParamPhi
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_rhoParamPsi

theorem integrable_rhoParamPhi (C : Copula 2) (t : ℝ) (i : Fin 2) :
    Integrable (fun x => rhoParamPhi t (x i)) C.toMeasure := by
  classical
  exact Integrable.piecewise
    (measurableSet_le (show Measurable (fun x : Fin 2 → I => (x i : ℝ)) by fun_prop) measurable_const)
    (Copula.integrable_continuous_cube _ (show Continuous (fun x : Fin 2 → I =>
      (4 / 3 : ℝ) * |(x i : ℝ) - t / 2| ^ 3) by fun_prop)).integrableOn
    (Copula.integrable_continuous_cube _ (show Continuous (fun x : Fin 2 → I =>
      2 * (x i : ℝ) ^ 3 / 3 - t * (x i : ℝ) ^ 2 / 2) by fun_prop)).integrableOn

theorem integrable_rhoParamPsi (C : Copula 2) (t : ℝ) (i : Fin 2) :
    Integrable (fun x => rhoParamPsi t (x i)) C.toMeasure := by
  classical
  exact Integrable.piecewise
    (measurableSet_le (show Measurable (fun x : Fin 2 → I => (x i : ℝ)) by fun_prop) measurable_const)
    (Copula.integrable_continuous_cube _ (show Continuous (fun x : Fin 2 → I =>
      (x i : ℝ) ^ 3 / 12 - t ^ 2 * (x i : ℝ) / 4) by fun_prop)).integrableOn
    (Copula.integrable_continuous_cube _ (show Continuous (fun x : Fin 2 → I =>
      (x i : ℝ) ^ 3 / 3 - t * (x i : ℝ) ^ 2 / 2) by fun_prop)).integrableOn

theorem measurable_rhoParamPhi (t : ℝ) : Measurable (fun u : I => rhoParamPhi t u) := by
  exact (show Measurable (fun u : I => (4 / 3 : ℝ) * |(u : ℝ) - t / 2| ^ 3) by fun_prop).ite
    (measurableSet_le measurable_subtype_coe measurable_const)
    (show Measurable (fun u : I => 2 * (u : ℝ) ^ 3 / 3 - t * (u : ℝ) ^ 2 / 2) by fun_prop)

theorem measurable_rhoParamPsi (t : ℝ) : Measurable (fun u : I => rhoParamPsi t u) := by
  exact (show Measurable (fun u : I => (u : ℝ) ^ 3 / 12 - t ^ 2 * (u : ℝ) / 4) by fun_prop).ite
    (measurableSet_le measurable_subtype_coe measurable_const)
    (show Measurable (fun u : I => (u : ℝ) ^ 3 / 3 - t * (u : ℝ) ^ 2 / 2) by fun_prop)

theorem transport_rho_param_upper (C : Copula 2) (t : I) :
    (∫ x, ((x 0 : ℝ) ^ 2 - (t : ℝ) * (x 0 : ℝ)) * (x 1 : ℝ) ∂C.toMeasure) ≤
      (t : ℝ) ^ 4 / 48 - (t : ℝ) / 3 + 1 / 4 := by
  have hp := integrable_rhoParamPhi C t 0
  have hq := integrable_rhoParamPsi C t 1
  have hi : Integrable (fun x : Fin 2 → I =>
      ((x 0 : ℝ) ^ 2 - (t : ℝ) * (x 0 : ℝ)) * (x 1 : ℝ)) C.toMeasure :=
    Copula.integrable_continuous_cube _ (by fun_prop)
  have h := integral_mono hi (hp.add hq)
    (fun x => rho_param_dual t (x 0) (x 1) t.property.1 (x 0).property.1 (x 1).property.1)
  simp only [Pi.add_apply] at h
  rw [integral_add hp hq, C.integral_eval 0 _ (measurable_rhoParamPhi t),
    C.integral_eval 1 _ (measurable_rhoParamPsi t), integral_rhoParamPhi, integral_rhoParamPsi] at h
  linarith

theorem rho_support_moment (C : Copula 2) (t : ℝ) :
    blestNu C - t * C.spearmanRho =
      12 * (∫ x, ((x 0 : ℝ) ^ 2 - t * (x 0 : ℝ)) * (x 1 : ℝ) ∂C.survivalCopula.toMeasure) - 2 + 3 * t := by
  have hn := support_moment_survival C 0
  norm_num [cost] at hn
  have hr : C.spearmanRho =
      12 * (∫ x, (x 0 : ℝ) * (x 1 : ℝ) ∂C.survivalCopula.toMeasure) - 3 := by
    rw [← Copula.spearmanRho_survivalCopula C]
    rfl
  have he : (fun x : Fin 2 → I => ((x 0 : ℝ) ^ 2 - t * (x 0 : ℝ)) * (x 1 : ℝ)) =
      fun x => (x 0 : ℝ) ^ 2 * (x 1 : ℝ) - t * ((x 0 : ℝ) * (x 1 : ℝ)) := by funext x; ring
  rw [he, integral_sub (Copula.integrable_continuous_cube _ (by fun_prop))
    (Copula.integrable_continuous_cube _ (by fun_prop)), integral_const_mul, hn, hr]
  ring

theorem rho_support (C : Copula 2) (t : I) :
    blestNu C - (t : ℝ) * C.spearmanRho ≤ 1 - (t : ℝ) + (t : ℝ) ^ 4 / 4 := by
  rw [rho_support_moment]
  linarith [transport_rho_param_upper C.survivalCopula t]

def rhoPosR (t : ℝ) : ℝ := 1 - t ^ 3
def rhoPosN (t : ℝ) : ℝ := 1 - (3 / 4) * t ^ 4
def rhoFamily (t : I) : Copula 2 :=
  (Copula.comonotonic 2).ordinalSum (skewTent Copula.unitHalf).transpose (unitInterval.symm t)

theorem rho_family_values (t : I) :
    (rhoFamily t).spearmanRho = rhoPosR t ∧ blestNu (rhoFamily t) = rhoPosN t := by
  constructor
  · rw [rhoFamily, Copula.spearmanRho_ordinalSum, Copula.spearmanRho_transpose,
      Copula.spearmanRho_comonotonic, rho_skewTent]
    norm_num [Copula.unitHalf, unitInterval.coe_symm_eq, rhoPosR]
  · rw [rhoFamily, blest_ordinalSum, blest_comonotonic, nu_transpose_skewTent,
      Copula.spearmanRho_comonotonic]
    norm_num [Copula.unitHalf, unitInterval.coe_symm_eq, rhoPosN]
    ring

theorem rho_positive_upper (C : Copula 2) (t : I) (hr : C.spearmanRho = rhoPosR t) :
    blestNu C ≤ rhoPosN t := by
  have h := rho_support C t
  rw [hr] at h
  dsimp [rhoPosR, rhoPosN] at *
  nlinarith

theorem rho_positive_fibre (t : I) (n : ℝ) :
    (∃ C : Copula 2, C.spearmanRho = rhoPosR t ∧ blestNu C = n) ↔
      n ∈ Icc (2 * rhoPosR t - rhoPosN t) (rhoPosN t) := by
  constructor
  · rintro ⟨C, hr, rfl⟩
    have hu := rho_positive_upper C t hr
    have hl := rho_positive_upper C.survivalCopula t ((Copula.spearmanRho_survivalCopula C).trans hr)
    rw [nu_survival, hr] at hl
    exact ⟨by linarith, hu⟩
  · intro hn
    let B := rhoFamily t
    have hr : B.spearmanRho = rhoPosR t := (rho_family_values t).1
    have hb : blestNu B = rhoPosN t := (rho_family_values t).2
    have hc : Continuous (fun s : I => blestNu (B.mix B.survivalCopula s)) := by
      simp_rw [blest_mix]
      fun_prop
    obtain ⟨s, hs⟩ := Verification.exists_unitInterval_eq hc (z := n)
      (by simp only [blest_mix]; norm_num; rw [nu_survival, hr, hb]; exact hn.1)
      (by simp only [blest_mix]; norm_num; rw [hb]; exact hn.2)
    refine ⟨B.mix B.survivalCopula s, ?_, hs⟩
    rw [Copula.spearmanRho_mix, Copula.spearmanRho_survivalCopula, hr]
    ring

theorem rho_negative_fibre (t : I) (n : ℝ) :
    (∃ C : Copula 2, C.spearmanRho = -rhoPosR t ∧ blestNu C = n) ↔
      n ∈ Icc (-rhoPosN t) (rhoPosN t - 2 * rhoPosR t) := by
  constructor
  · rintro ⟨C, hr, rfl⟩
    have h := (rho_positive_fibre t (blestNu C + 2 * rhoPosR t)).mp
      ⟨C.reflect {0},
        by rw [Copula.spearmanRho_reflect_first, hr]; ring,
        by rw [nu_reflect_first, hr]; ring⟩
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro hn
    obtain ⟨C, hr, hc⟩ := (rho_positive_fibre t (n + 2 * rhoPosR t)).mpr
      ⟨by linarith [hn.1], by linarith [hn.2]⟩
    refine ⟨C.reflect {0}, ?_, ?_⟩
    · rw [Copula.spearmanRho_reflect_first, hr]
    · rw [nu_reflect_first, hr, hc]; ring

#assert_standard_axioms Papers.Rockel2026ExactBlest.integrable_rhoParamPhi
#assert_standard_axioms Papers.Rockel2026ExactBlest.integrable_rhoParamPsi
#assert_standard_axioms Papers.Rockel2026ExactBlest.measurable_rhoParamPhi
#assert_standard_axioms Papers.Rockel2026ExactBlest.measurable_rhoParamPsi
#assert_standard_axioms Papers.Rockel2026ExactBlest.transport_rho_param_upper
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_support_moment
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_support
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_family_values
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_positive_upper
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_positive_fibre
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_negative_fibre

theorem rhoPosR_mem_Icc (t : I) : rhoPosR t ∈ Icc (0 : ℝ) 1 := by
  have h0 := pow_nonneg t.property.1 3
  have h1 := pow_le_one₀ t.property.1 t.property.2 (n := 3)
  constructor <;> unfold rhoPosR <;> linarith

theorem rho_parameter_strictAnti : StrictAntiOn rhoPosR (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hp : x ^ 3 < y ^ 3 := by
    gcongr
    exact hx.1
  unfold rhoPosR
  linarith

theorem rho_parameter_exists_unique (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    ∃! t : I, rhoPosR t = r := by
  obtain ⟨t, ht⟩ := Verification.exists_unitInterval_eq
    (show Continuous (fun t : I => (t : ℝ) ^ 3) by fun_prop) (z := 1 - r)
    (by norm_num; linarith [hr.2]) (by norm_num; linarith [hr.1])
  have hv : rhoPosR t = r := by unfold rhoPosR; linarith
  refine ⟨t, hv, ?_⟩
  intro s hs
  apply Subtype.ext
  exact rho_parameter_strictAnti.injOn s.property t.property (hs.trans hv.symm)

theorem rpow_cube_four_thirds (x : ℝ) (hx : 0 ≤ x) :
    (x ^ 3) ^ (4 / 3 : ℝ) = x ^ 4 := by
  rw [← Real.rpow_natCast x 3, ← Real.rpow_mul hx]
  norm_num

/-- The manuscript's Phi, with the agreeing branches joined at rho=0. -/
def rhoBoundary (r : ℝ) : ℝ :=
  if 0 ≤ r then 1 - (3 / 4) * (1 - r) ^ (4 / 3 : ℝ)
  else 2 * r + 1 - (3 / 4) * (1 + r) ^ (4 / 3 : ℝ)

theorem rhoBoundary_positive (t : I) : rhoBoundary (rhoPosR t) = rhoPosN t := by
  rw [rhoBoundary, ite_eq_left (rhoPosR_mem_Icc t).1]
  have he : 1 - rhoPosR t = (t : ℝ) ^ 3 := by unfold rhoPosR; ring
  rw [he, rpow_cube_four_thirds _ t.property.1]
  rfl

theorem rhoBoundary_neg (r : ℝ) (hr : 0 ≤ r) : rhoBoundary (-r) = rhoBoundary r - 2 * r := by
  by_cases hz : r = 0
  · subst r; simp
  · have hn : ¬0 ≤ -r := by
      have hp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
      linarith
    rw [rhoBoundary, ite_eq_right hn, rhoBoundary, ite_eq_left hr]
    have he : 1 + -r = 1 - r := by ring
    rw [he]
    ring

theorem rhoBoundary_negative (t : I) :
    rhoBoundary (-rhoPosR t) = rhoPosN t - 2 * rhoPosR t := by
  rw [rhoBoundary_neg _ (rhoPosR_mem_Icc t).1, rhoBoundary_positive]

theorem rho_fibre_complete (r n : ℝ) :
    (∃ C : Copula 2, C.spearmanRho = r ∧ blestNu C = n) ↔
      r ∈ Icc (-1 : ℝ) 1 ∧ n ∈ Icc (2 * r - rhoBoundary r) (rhoBoundary r) := by
  constructor
  · rintro ⟨C, hr, hn⟩
    have hrc : r ∈ Icc (-1 : ℝ) 1 := hr ▸ C.spearmanRho_mem_Icc
    refine ⟨hrc, ?_⟩
    by_cases hp : 0 ≤ r
    · obtain ⟨t, ht, _⟩ := rho_parameter_exists_unique r ⟨hp, hrc.2⟩
      have h := (rho_positive_fibre t n).mp ⟨C, hr.trans ht.symm, hn⟩
      rw [← ht, rhoBoundary_positive]
      exact h
    · obtain ⟨t, ht, _⟩ := rho_parameter_exists_unique (-r) ⟨by linarith, by linarith [hrc.1]⟩
      have he : r = -rhoPosR t := by linarith
      have h := (rho_negative_fibre t n).mp ⟨C, hr.trans he, hn⟩
      rw [he, rhoBoundary_negative]
      exact ⟨by linarith [h.1], h.2⟩
  · rintro ⟨hr, hn⟩
    by_cases hp : 0 ≤ r
    · obtain ⟨t, ht, _⟩ := rho_parameter_exists_unique r ⟨hp, hr.2⟩
      rw [← ht, rhoBoundary_positive] at hn
      obtain ⟨C, hc, hv⟩ := (rho_positive_fibre t n).mpr hn
      exact ⟨C, hc.trans ht, hv⟩
    · obtain ⟨t, ht, _⟩ := rho_parameter_exists_unique (-r) ⟨by linarith, by linarith [hr.1]⟩
      have he : r = -rhoPosR t := by linarith
      rw [he, rhoBoundary_negative] at hn
      obtain ⟨C, hc, hv⟩ := (rho_negative_fibre t n).mpr ⟨by linarith [hn.1], hn.2⟩
      exact ⟨C, hc.trans he.symm, hv⟩

/-- The exact rho/nu set equality with the displayed 4/3-power boundary. -/
theorem rho_nu_region :
    Set.range (fun C : Copula 2 => (C.spearmanRho, blestNu C)) =
      {p : ℝ × ℝ | p.1 ∈ Icc (-1 : ℝ) 1 ∧
        p.2 ∈ Icc (2 * p.1 - rhoBoundary p.1) (rhoBoundary p.1)} := by
  ext ⟨r, n⟩
  simpa only [Set.mem_range, Set.mem_ofPred_eq, Prod.mk.injEq] using rho_fibre_complete r n

#assert_standard_axioms Papers.Rockel2026ExactBlest.rhoPosR_mem_Icc
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_parameter_strictAnti
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_parameter_exists_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.rpow_cube_four_thirds
#assert_standard_axioms Papers.Rockel2026ExactBlest.rhoBoundary_positive
#assert_standard_axioms Papers.Rockel2026ExactBlest.rhoBoundary_neg
#assert_standard_axioms Papers.Rockel2026ExactBlest.rhoBoundary_negative
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_fibre_complete
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_nu_region

end
end Papers.Rockel2026ExactBlest
