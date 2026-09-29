import Papers.OrendayLaresRockel2026XiBeta.MedianSection

/-! # Elementary integral lemmas for Lemma 5.2

Areas under the maximum of two lines (the triangles of the source's inequality (5.4)), and
vanishing of continuous nonnegative functions with zero integral.
-/

open MeasureTheory Set intervalIntegral

namespace Papers.OrendayLaresRockel2026XiBeta

theorem int_lin (α β a b : ℝ) :
    ∫ u in a..b, (α + β * u) = α * (b - a) + β * (b ^ 2 - a ^ 2) / 2 := by
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]; ring

/-- A continuous nonnegative function with vanishing integral vanishes. -/
theorem eq_zero_of_integral_eq_zero {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (h0 : ∀ x ∈ Icc a b, 0 ≤ f x) (hint : ∫ x in a..b, f x = 0) : ∀ x ∈ Icc a b, f x = 0 := by
  have hae : f =ᵐ[volume.restrict (Ioc a b)] 0 := by
    refine (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab.le ?_
      (hf.intervalIntegrable _ _)).1 hint
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun x hx => h0 x (Ioc_subset_Icc_self hx))
  have hEq : EqOn f 0 (Ioc a b) :=
    Measure.eqOn_of_ae_eq hae hf.continuousOn continuousOn_const
      (Ioc_subset_closure_interior a b)
  have hEq' : EqOn f 0 (Icc a b) :=
    hEq.of_subset_closure hf.continuousOn continuousOn_const Ioc_subset_Icc_self
      (by rw [closure_Ioc hab.ne])
  exact fun x hx => hEq' hx

/-- The area under `max (1/2 - u) (q + m (u - 1/2))` on `[0, 1/2]`. -/
theorem integral_max_lines {q m : ℝ} (hq : 0 ≤ q) (hm : 0 < 1 + m) (hqm : 2 * q ≤ 1 + m) :
    ∫ u in (0 : ℝ)..(1 / 2), max (1 / 2 - u) (q + m * (u - 1 / 2)) =
      1 / 8 + q ^ 2 / (2 * (1 + m)) := by
  set δ := q / (1 + m) with hδ
  have hδ0 : 0 ≤ δ := div_nonneg hq hm.le
  have hδ1 : δ ≤ 1 / 2 := by rw [hδ, div_le_iff₀ hm]; linarith
  have hq' : q = δ * (1 + m) := by rw [hδ]; field_simp
  have e1 : ∫ u in (0 : ℝ)..(1 / 2 - δ), max (1 / 2 - u) (q + m * (u - 1 / 2)) =
      ∫ u in (0 : ℝ)..(1 / 2 - δ), (1 / 2 + (-1) * u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by linarith)] at hu
    have : q + m * (u - 1 / 2) ≤ 1 / 2 - u := by nlinarith [hu.2]
    show max _ _ = _
    rw [max_eq_left this]; ring
  have e2 : ∫ u in (1 / 2 - δ)..(1 / 2), max (1 / 2 - u) (q + m * (u - 1 / 2)) =
      ∫ u in (1 / 2 - δ)..(1 / 2), ((q - m / 2) + m * u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by linarith)] at hu
    have : 1 / 2 - u ≤ q + m * (u - 1 / 2) := by nlinarith [hu.1]
    show max _ _ = _
    rw [max_eq_right this]; ring
  rw [← integral_add_adjacent_intervals (b := 1 / 2 - δ)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), e1, e2, int_lin, int_lin]
  have : q ^ 2 / (2 * (1 + m)) = δ * q / 2 := by rw [hδ]; field_simp
  rw [this, hq']
  ring

/-- The lower area bound of (5.4) on the left half, with its equality case. -/
theorem area_left {f : ℝ → ℝ} (hf : Continuous f) {q m : ℝ} (hq : 0 ≤ q) (hm : 0 < 1 + m)
    (hqm : 2 * q ≤ 1 + m) (h1 : ∀ u ∈ Icc (0 : ℝ) (1 / 2), 1 / 2 - u ≤ f u)
    (h2 : ∀ u ∈ Icc (0 : ℝ) (1 / 2), q + m * (u - 1 / 2) ≤ f u) :
    1 / 8 + q ^ 2 / (2 * (1 + m)) ≤ ∫ u in (0 : ℝ)..(1 / 2), f u ∧
      (∫ u in (0 : ℝ)..(1 / 2), f u = 1 / 8 + q ^ 2 / (2 * (1 + m)) →
        ∀ u ∈ Icc (0 : ℝ) (1 / 2), f u = max (1 / 2 - u) (q + m * (u - 1 / 2))) := by
  have hg : Continuous (fun u : ℝ => max (1 / 2 - u) (q + m * (u - 1 / 2))) := by fun_prop
  have hle : ∀ u ∈ Icc (0 : ℝ) (1 / 2), max (1 / 2 - u) (q + m * (u - 1 / 2)) ≤ f u :=
    fun u hu => max_le (h1 u hu) (h2 u hu)
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (hg.intervalIntegrable (μ := volume) _ _) (hf.intervalIntegrable (μ := volume) _ _) hle
  rw [integral_max_lines hq hm hqm] at hmono
  refine ⟨hmono, fun heq u hu => ?_⟩
  have hsub : ∫ x in (0 : ℝ)..(1 / 2), (f x - max (1 / 2 - x) (q + m * (x - 1 / 2))) = 0 := by
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _),
      integral_max_lines hq hm hqm, heq]; ring
  have := eq_zero_of_integral_eq_zero (hf.sub hg) (by norm_num : (0 : ℝ) < 1 / 2)
    (fun x hx => sub_nonneg.2 (hle x hx)) hsub u hu
  simp only [Pi.sub_apply] at this
  linarith

/-- The mirror image of `area_left` on the right half. -/
theorem area_right {f : ℝ → ℝ} (hf : Continuous f) {q m : ℝ} (hq : 0 ≤ q) (hm : 0 < 1 - m)
    (hqm : 2 * q ≤ 1 - m) (h1 : ∀ u ∈ Icc (1 / 2 : ℝ) 1, u - 1 / 2 ≤ f u)
    (h2 : ∀ u ∈ Icc (1 / 2 : ℝ) 1, q + m * (u - 1 / 2) ≤ f u) :
    1 / 8 + q ^ 2 / (2 * (1 - m)) ≤ ∫ u in (1 / 2 : ℝ)..1, f u ∧
      (∫ u in (1 / 2 : ℝ)..1, f u = 1 / 8 + q ^ 2 / (2 * (1 - m)) →
        ∀ u ∈ Icc (1 / 2 : ℝ) 1, f u = max (u - 1 / 2) (q + m * (u - 1 / 2))) := by
  have key := area_left (f := fun u => f (1 - u)) (hf.comp (by fun_prop)) (m := -m) hq
    (by linarith) (by linarith)
    (fun u hu => by have := h1 (1 - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩; linarith)
    (fun u hu => by have := h2 (1 - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩; linarith)
  have hint : ∫ u in (0 : ℝ)..(1 / 2), f (1 - u) = ∫ u in (1 / 2 : ℝ)..1, f u := by
    rw [intervalIntegral.integral_comp_sub_left (fun u => f u) (1 : ℝ)]
    norm_num
  rw [hint] at key
  refine ⟨key.1, fun heq u hu => ?_⟩
  have := key.2 heq (1 - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
  simp only [sub_sub_cancel] at this
  rw [this]
  congr 1 <;> ring_nf

end Papers.OrendayLaresRockel2026XiBeta
