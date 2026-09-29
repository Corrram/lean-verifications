import Papers.OrendayLaresRockel2026XiBeta.GapConvexEq
import Papers.OrendayLaresRockel2026XiBeta.MaximalCompletion

/-! # Equation (5.3): `1 - ξ(Q_A) = (3/2) J(w)`

The conditional distribution of `V` given `U = u` under `Q_A` puts mass `p(u)` at `A(u)` and
`1 - p(u)` at `B(u)`; by (2.2) `1 - ξ = 6 ∬ h (1 - h)`, and integrating out the response first
gives `p (1 - p) (B - A) = p (1 - p) w`.  With `w' = 1 - 2p` this is `(3/2) J(w)`.
-/

open MeasureTheory ProbabilityTheory Set intervalIntegral
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

namespace MedianSection

variable (s : MedianSection)

/-- The slope data `d = 1 - 2p = w'` of the gap function of a median section. -/
noncomputable def slopeData : SlopeData where
  d u := 1 - 2 * s.p u
  mono a b h := by have := s.antitone h; simp only; linarith
  bdd u hu := by
    have h0 := s.p_nonneg hu.2
    have h1 := s.p_le_one hu.1
    rw [abs_le]; constructor <;> linarith
  integral_zero := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((s.intervalIntegrable_p _ _).const_mul 2), intervalIntegral.integral_const_mul,
      s.integral_eq]
    simp

theorem slopeData_d (u : ℝ) : s.slopeData.d u = 1 - 2 * s.p u := rfl

theorem slopeData_w (u : ℝ) : s.slopeData.w u = s.gap u := by
  rw [gap_eq_integral]; rfl

theorem slopeData_q : s.slopeData.q = s.gap (1 / 2) := s.slopeData_w _

theorem slopeData_abs_le : ∀ u ∈ Icc (0 : ℝ) 1, |u - 1 / 2| ≤ s.slopeData.w u := by
  intro u hu
  rw [slopeData_w]; exact s.abs_le_gap hu.1 hu.2

/-- `J(w) = ∫₀¹ w (1 - w'²)` for the gap function of a median section. -/
theorem slopeData_J : s.slopeData.J = 4 * ∫ u in (0 : ℝ)..1, s.p u * (1 - s.p u) * s.gap u := by
  unfold SlopeData.J
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  simp only [slopeData_w, slopeData_d]
  ring

theorem measurable_kerR_uncurry : Measurable (fun z : I × I => s.kerR z.1 z.2) := by
  have hA : Measurable (fun z : I × I => s.A z.2) :=
    s.continuous_A.measurable.comp (measurable_subtype_coe.comp measurable_snd)
  have hB : Measurable (fun z : I × I => s.B z.2) :=
    s.continuous_B.measurable.comp (measurable_subtype_coe.comp measurable_snd)
  have hv : Measurable (fun z : I × I => (z.1 : ℝ)) := measurable_subtype_coe.comp measurable_fst
  have hp : Measurable (fun z : I × I => s.p z.2) :=
    s.antitone.measurable.comp (measurable_subtype_coe.comp measurable_snd)
  unfold kerR
  exact (hp.mul (Measurable.ite (measurableSet_le hA hv) measurable_const measurable_const)).add
    ((measurable_const.sub hp).mul
      (Measurable.ite (measurableSet_le hB hv) measurable_const measurable_const))

/-- The product form of the kernel: `k (1 - k) = p (1 - p) 1{A ≤ v < B}`. -/
theorem kerR_mul_one_sub {v t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    s.kerR v t * (1 - s.kerR v t) =
      s.p t * (1 - s.p t) * (if s.A t ≤ v ∧ v < s.B t then 1 else 0) := by
  have hAB := s.A_le_B ht0 ht1
  unfold kerR
  by_cases h1 : s.A t ≤ v <;> by_cases h2 : s.B t ≤ v
  · simp [h1, h2]
  · have h2' : v < s.B t := not_le.mp h2
    simp [h1, h2, h2']
  · exfalso; exact h1 (hAB.trans h2)
  · have h1' : v < s.A t := not_le.mp h1
    simp [h1, h2]

theorem integral_indicator_AB {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∫ v : I, (if s.A u ≤ (v : ℝ) ∧ (v : ℝ) < s.B u then (1 : ℝ) else 0) = s.B u - s.A u := by
  classical
  rw [Copula.integral_unitInterval
    (fun v => if s.A u ≤ v ∧ v < s.B u then (1 : ℝ) else 0)]
  have hA0 := s.A_nonneg hu0 hu1
  have hAB := s.A_le_B hu0 hu1
  have hB1 := s.B_le_one hu0 hu1
  have hm : ∀ a b : ℝ, IntervalIntegrable
      (fun v : ℝ => if s.A u ≤ v ∧ v < s.B u then (1 : ℝ) else 0) volume a b := by
    intro a b
    have : Measurable (fun v : ℝ => if s.A u ≤ v ∧ v < s.B u then (1 : ℝ) else 0) :=
      Measurable.ite ((measurableSet_le measurable_const measurable_id).inter
        (measurableSet_lt measurable_id measurable_const)) measurable_const measurable_const
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' this.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun x => by
      by_cases h : s.A u ≤ x ∧ x < s.B u <;> simp [h])
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := s.A u) (hm _ _) (hm _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := s.A u) (b := s.B u) (hm _ _) (hm _ _),
    integral_eq_of_eq_on_Ioo hA0 (k := 0) (fun t ht => by
      have : ¬ s.A u ≤ t := not_le.mpr ht.2
      simp [this]),
    integral_eq_of_eq_on_Ioo hAB (k := 1) (fun t ht => by simp [ht.1.le, ht.2]),
    integral_eq_of_eq_on_Ioo hB1 (k := 0) (fun t ht => by
      have : ¬ t < s.B u := not_lt.mpr ht.1.le
      simp [this])]
  ring

theorem integral_condCDF_sq_completion (t : I) :
    (∫ u : I, s.completion.conditionalCDF u t ^ 2) = ∫ u : I, s.kernelCDF t u ^ 2 :=
  integral_congr_ae ((s.conditionalCDF_completion t).fun_comp (fun x : ℝ => x ^ 2))

theorem integrable_integral_kernelCDF_sq :
    Integrable (fun t : I => ∫ u : I, s.kernelCDF t u ^ 2) := by
  have := s.completion.integrable_integral_conditionalCDF_sq
  simp only [integral_condCDF_sq_completion] at this
  exact this

theorem xi_completion_eq :
    s.completion.chatterjeeXi = 6 * (∫ t : I, ∫ u : I, s.kernelCDF t u ^ 2) - 2 := by
  unfold Copula.chatterjeeXi
  simp_rw [integral_condCDF_sq_completion]

/-- Equation (5.3), first form: `1 - ξ(Q_A) = 6 ∫₀¹ p (1 - p) w`. -/
theorem xi_completion :
    s.completion.chatterjeeXi = 1 - 6 * ∫ u in (0 : ℝ)..1, s.p u * (1 - s.p u) * s.gap u := by
  have hΦint := s.integrable_integral_kernelCDF_sq
  have hsq : ∀ t : I, Integrable (fun u : I => s.kernelCDF t u ^ 2) := fun t =>
    Verification.integrable_unit_bounded ((s.measurable_kernelCDF t).pow_const 2)
      (fun u => ⟨sq_nonneg _, by
        have := s.kernelCDF_mem t u
        nlinarith [this.1, this.2]⟩)
  have hstep : ∫ t : I, ∫ u : I, (s.kernelCDF t u - s.kernelCDF t u ^ 2) =
      1 / 2 - ∫ t : I, ∫ u : I, s.kernelCDF t u ^ 2 := by
    have : ∀ t : I, (∫ u : I, (s.kernelCDF t u - s.kernelCDF t u ^ 2)) =
        (t : ℝ) - ∫ u : I, s.kernelCDF t u ^ 2 := fun t => by
      rw [integral_sub (s.integrable_kernelCDF t) (hsq t), s.integral_kernelCDF]
    simp_rw [this]
    rw [integral_sub (Copula.integrable_continuous_unit volume continuous_subtype_val) hΦint,
      Copula.integral_unit_id]
  have hint : Integrable (Function.uncurry fun (t u : I) => s.kernelCDF t u - s.kernelCDF t u ^ 2)
      (volume.prod volume) := by
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · have := s.measurable_kerR_uncurry
      exact ((this.sub (this.pow_const 2))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun z => ?_)
      have h := s.kernelCDF_mem z.1 z.2
      simp only [Function.uncurry, Real.norm_eq_abs]
      rw [abs_le]; constructor <;> nlinarith [h.1, h.2]
  have hswap := integral_integral_swap (μ := (volume : Measure I)) (ν := (volume : Measure I))
    hint
  have hinner : ∀ u : I, (∫ t : I, (s.kernelCDF t u - s.kernelCDF t u ^ 2)) =
      s.p u * (1 - s.p u) * s.gap u := by
    intro u
    have h : ∀ t : I, s.kernelCDF t u - s.kernelCDF t u ^ 2 =
        s.p u * (1 - s.p u) *
          (if s.A u ≤ (t : ℝ) ∧ (t : ℝ) < s.B u then (1 : ℝ) else 0) := by
      intro t
      rw [← s.kerR_mul_one_sub u.2.1 u.2.2]
      unfold kernelCDF; ring
    simp_rw [h]
    rw [MeasureTheory.integral_const_mul, s.integral_indicator_AB u.2.1 u.2.2]
    rfl
  simp_rw [hinner] at hswap
  have hW : (∫ u : I, s.p u * (1 - s.p u) * s.gap u) =
      ∫ u in (0 : ℝ)..1, s.p u * (1 - s.p u) * s.gap u :=
    Copula.integral_unitInterval (fun u => s.p u * (1 - s.p u) * s.gap u)
  rw [s.xi_completion_eq]
  rw [hW] at hswap
  linarith

/-- Equation (5.3): `1 - ξ(Q_A) = (3/2) J(w)`. -/
theorem one_sub_xi_completion : 1 - s.completion.chatterjeeXi = 3 / 2 * s.slopeData.J := by
  rw [s.xi_completion, s.slopeData_J]; ring

end MedianSection

end Papers.OrendayLaresRockel2026XiBeta
