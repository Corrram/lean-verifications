import Papers.OrendayLaresRockel2026XiBeta.MedianSection
import Verification.ConditionalCopulaAE

/-! # Lemma 5.1 (i), (ii): the maximal completion `Q_A` of a median section

For `s : MedianSection` (with section `A` and companion `B`) the kernel of
`Q_A` puts mass `p(u)` at `A(u)` and mass `1 - p(u)` at `B(u)`; its
distribution function in the response threshold `v` is `kerR`.  The copula
`s.completion` is built from this kernel (`copulaOfConditionalAE`), its
distribution function is the closed form (5.1) of the source, and it is
stochastically increasing with median section `A`.  Part (ii) says that it is the
largest copula with median section `A`.
-/

open MeasureTheory ProbabilityTheory Set intervalIntegral
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

/-- A density times the indicator of a measurable set stays interval integrable. -/
theorem intervalIntegrable_mul_ite {x : ℝ → ℝ} {a b : ℝ} (hx : IntervalIntegrable x volume a b)
    (P : ℝ → Prop) [DecidablePred P] (hP : MeasurableSet {t | P t}) :
    IntervalIntegrable (fun t => x t * if P t then (1 : ℝ) else 0) volume a b := by
  refine hx.mono_fun ?_ ?_
  · exact (intervalIntegrable_iff.1 hx).aestronglyMeasurable.mul
      (Measurable.ite hP measurable_const measurable_const).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      by_cases h : P t <;> simp [h])

/-- The integral of a nonnegative density against the indicator of a sublevel set of its own
primitive is `min (X u) v - a`. -/
theorem integral_mul_indicator_primitive {x : ℝ → ℝ} (hxi : ∀ a b, IntervalIntegrable x volume a b)
    {u a v : ℝ} (hu : 0 ≤ u) (hx : ∀ t ∈ Icc 0 u, 0 ≤ x t) (hav : a ≤ v) :
    ∫ t in (0 : ℝ)..u, x t * (if a + ∫ r in (0 : ℝ)..t, x r ≤ v then 1 else 0) =
      min (a + ∫ r in (0 : ℝ)..u, x r) v - a := by
  set Y : ℝ → ℝ := fun t => a + ∫ r in (0 : ℝ)..t, x r with hY
  have hYc : Continuous Y := continuous_const.add (intervalIntegral.continuous_primitive hxi 0)
  have hYm : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → t ≤ u → Y s ≤ Y t := by
    intro s t hs hst htu
    have : 0 ≤ ∫ r in s..t, x r := integral_nonneg hst (fun r hr => hx r ⟨hs.trans hr.1, hr.2.trans htu⟩)
    have h2 := integral_interval_sub_left (hxi 0 t) (hxi 0 s)
    simp only [hY]; linarith
  have hY0 : Y 0 = a := by simp [hY]
  by_cases hcase : Y u ≤ v
  · have h1 : ∫ t in (0 : ℝ)..u, x t * (if Y t ≤ v then 1 else 0) = ∫ t in (0 : ℝ)..u, x t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hu] at ht
      have := (hYm ht.1 ht.2 le_rfl).trans hcase
      simp [this]
    rw [h1, min_eq_left hcase]
    have h3 := integral_interval_sub_left (hxi 0 u) (hxi 0 0)
    simp only [intervalIntegral.integral_same, sub_zero] at h3
    simp only [hY]; linarith
  · replace hcase := not_le.mp hcase
    obtain ⟨c, hc, hcY⟩ := intermediate_value_Icc hu hYc.continuousOn
      (show v ∈ Icc (Y 0) (Y u) from ⟨by rw [hY0]; exact hav, hcase.le⟩)
    have hS : IsCompact (Icc 0 u ∩ {t | Y t ≤ v}) :=
      isCompact_Icc.inter_right (isClosed_le hYc continuous_const)
    obtain ⟨t0, ⟨ht0, ht0v⟩, hgr⟩ := hS.exists_isGreatest ⟨c, hc, hcY.le⟩
    have hct0 : c ≤ t0 := hgr ⟨hc, hcY.le⟩
    have hYt0 : Y t0 = v := le_antisymm ht0v (hcY ▸ hYm hc.1 hct0 ht0.2)
    have hind : ∀ t ∈ Icc 0 u, (if Y t ≤ v then (1 : ℝ) else 0) = if t ≤ t0 then 1 else 0 := by
      intro t ht
      by_cases h : t ≤ t0
      · have := (hYm ht.1 h ht0.2).trans ht0v
        simp [h, this]
      · have : ¬ Y t ≤ v := fun hle => h (hgr ⟨ht, hle⟩)
        simp [h, this]
    have hsplit := integral_add_adjacent_intervals
      (f := fun t => x t * (if Y t ≤ v then (1 : ℝ) else 0)) (a := 0) (b := t0) (c := u)
      (intervalIntegrable_mul_ite (hxi 0 t0) _ (measurableSet_le hYc.measurable measurable_const))
      (intervalIntegrable_mul_ite (hxi t0 u) _ (measurableSet_le hYc.measurable measurable_const))
    · rw [← hsplit]
      have e1 : ∫ t in (0 : ℝ)..t0, x t * (if Y t ≤ v then 1 else 0) = ∫ t in (0 : ℝ)..t0, x t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le ht0.1] at ht
        simp [hind t ⟨ht.1, ht.2.trans ht0.2⟩, ht.2]
      have e2 : ∫ t in t0..u, x t * (if Y t ≤ v then 1 else 0) = 0 := by
        rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))]
        · simp
        · refine Filter.Eventually.of_forall (fun t ht => ?_)
          rw [uIoc_of_le ht0.2] at ht
          simp [hind t ⟨ht0.1.trans ht.1.le, ht.2⟩, not_le.mpr ht.1]
      rw [e1, e2, min_eq_right hcase.le]
      have h3 := integral_interval_sub_left (hxi 0 t0) (hxi 0 0)
      have : Y t0 = a + ∫ r in (0 : ℝ)..t0, x r := rfl
      simp at h3
      linarith

namespace MedianSection

variable (s : MedianSection)

theorem half_mul_le_A {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) : u / 2 ≤ s.A u := by
  have h := s.concaveOn_A.2 (x := 0) (y := 1) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
    (show 0 ≤ 1 - u by linarith) hu (by ring)
  simp only [smul_eq_mul, A_zero, A_one, mul_zero, mul_one, zero_add] at h
  linarith

theorem B_eq_integral (t : ℝ) : s.B t = 1 / 2 + ∫ r in (0 : ℝ)..t, (1 - s.p r) := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const (s.intervalIntegrable_p _ _)]
  simp [B, A]
  ring

/-- The distribution function in the response threshold `v` of the kernel of `Q_A` at the
conditioning point `t`: mass `p(t)` at `A(t)` and mass `1 - p(t)` at `B(t)`. -/
noncomputable def kerR (v t : ℝ) : ℝ :=
  s.p t * (if s.A t ≤ v then 1 else 0) + (1 - s.p t) * (if s.B t ≤ v then 1 else 0)

theorem kerR_of_lt {v t : ℝ} (hv : v < 1 / 2) (ht : 0 ≤ t) :
    s.kerR v t = s.p t * (if s.A t ≤ v then 1 else 0) := by
  have : ¬ s.B t ≤ v := not_le.mpr (lt_of_lt_of_le hv (s.half_le_B ht))
  simp [kerR, this]

theorem kerR_of_ge {v t : ℝ} (hv : 1 / 2 ≤ v) (ht : t ≤ 1) :
    s.kerR v t = s.p t + (1 - s.p t) * (if s.B t ≤ v then 1 else 0) := by
  have : s.A t ≤ v := (s.A_le_half ht).trans hv
  simp [kerR, this]

theorem kerR_nonneg {v t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ s.kerR v t := by
  have h0 := s.p_nonneg ht1
  have h1 := s.p_le_one ht0
  unfold kerR
  split_ifs <;> nlinarith

theorem kerR_le_one {v t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : s.kerR v t ≤ 1 := by
  have h0 := s.p_nonneg ht1
  have h1 := s.p_le_one ht0
  unfold kerR
  split_ifs <;> nlinarith

theorem kerR_mono {v v' t : ℝ} (hv : v ≤ v') (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    s.kerR v t ≤ s.kerR v' t := by
  have h0 := s.p_nonneg ht1
  have h1 := s.p_le_one ht0
  have i1 : s.A t ≤ v → s.A t ≤ v' := fun h => h.trans hv
  have i2 : s.B t ≤ v → s.B t ≤ v' := fun h => h.trans hv
  unfold kerR
  split_ifs <;> first | (exfalso; tauto) | nlinarith

theorem kerR_anti {v t t' : ℝ} (ht0 : 0 ≤ t) (htt : t ≤ t') (ht1 : t' ≤ 1) :
    s.kerR v t' ≤ s.kerR v t := by
  have h0 := s.p_nonneg ht1
  have h1 := s.p_le_one ht0
  have hp := s.antitone htt
  have hp1 := s.p_nonneg (htt.trans ht1)
  have hp2 := s.p_le_one (ht0.trans htt)
  have i1 : s.A t' ≤ v → s.A t ≤ v := fun h => (s.A_mono htt ht1).trans h
  have i2 : s.B t' ≤ v → s.B t ≤ v := fun h => (s.B_mono ht0 htt).trans h
  have i3 : s.B t ≤ v → s.A t ≤ v := fun h => (s.A_le_B ht0 (htt.trans ht1)).trans h
  have i4 : s.B t' ≤ v → s.A t' ≤ v := fun h => (s.A_le_B (ht0.trans htt) ht1).trans h
  unfold kerR
  split_ifs <;> first | (exfalso; tauto) | nlinarith

/-- The closed form (5.1) of the maximal completion `Q_A`. -/
noncomputable def Qfun (u v : ℝ) : ℝ :=
  if v ≤ 1 / 2 then min (s.A u) v else min u (s.A u + v - 1 / 2)

theorem measurableSet_A_le (v : ℝ) : MeasurableSet {t | s.A t ≤ v} :=
  measurableSet_le s.continuous_A.measurable measurable_const

theorem measurableSet_B_le (v : ℝ) : MeasurableSet {t | s.B t ≤ v} :=
  measurableSet_le s.continuous_B.measurable measurable_const

theorem integral_kerR {u v : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) :
    ∫ t in (0 : ℝ)..u, s.kerR v t = s.Qfun u v := by
  have hi1 : IntervalIntegrable (fun t => s.p t * if s.A t ≤ v then (1 : ℝ) else 0) volume 0 u :=
    intervalIntegrable_mul_ite (s.intervalIntegrable_p 0 u) _ (s.measurableSet_A_le v)
  have hi2 : IntervalIntegrable (fun t => (1 - s.p t) * if s.B t ≤ v then (1 : ℝ) else 0)
      volume 0 u :=
    intervalIntegrable_mul_ite (x := fun t => 1 - s.p t)
      (intervalIntegrable_const.sub (s.intervalIntegrable_p 0 u)) _ (s.measurableSet_B_le v)
  have h1 : ∫ t in (0 : ℝ)..u, s.p t * (if s.A t ≤ v then (1 : ℝ) else 0) = min (s.A u) v := by
    have := integral_mul_indicator_primitive (x := s.p) s.intervalIntegrable_p hu
      (fun t ht => s.p_nonneg (ht.2.trans hu1)) (a := 0) (v := v) hv
    simp only [zero_add, sub_zero] at this
    exact this
  unfold kerR
  rw [intervalIntegral.integral_add hi1 hi2, h1]
  unfold Qfun
  by_cases hv2 : v ≤ 1 / 2
  · rcases eq_or_lt_of_le hv2 with hv2 | hv2
    · have h2 : ∫ t in (0 : ℝ)..u, (1 - s.p t) * (if s.B t ≤ v then (1 : ℝ) else 0) =
          min (s.B u) v - 1 / 2 := by
        have := integral_mul_indicator_primitive (x := fun t => 1 - s.p t)
          (fun a b => intervalIntegrable_const.sub (s.intervalIntegrable_p a b)) hu
          (fun t ht => by have := s.p_le_one ht.1; linarith) (a := 1 / 2) (v := v)
          hv2.ge
        simpa only [← s.B_eq_integral] using this
      rw [h2]
      simp only [hv2.le, ↓reduceIte]
      rw [min_eq_left (s.A_le_half hu1 |>.trans hv2.ge),
        min_eq_right ((hv2 ▸ s.half_le_B hu))]
      linarith
    · have h2 : ∫ t in (0 : ℝ)..u, (1 - s.p t) * (if s.B t ≤ v then (1 : ℝ) else 0) = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
        · simp
        · intro t ht
          rw [uIcc_of_le hu] at ht
          have : ¬ s.B t ≤ v := not_le.mpr (lt_of_lt_of_le hv2 (s.half_le_B ht.1))
          simp [this]
      rw [h2]
      simp only [hv2.le, ↓reduceIte]
      ring
  · have hv2' : 1 / 2 ≤ v := (not_le.mp hv2).le
    have h2 : ∫ t in (0 : ℝ)..u, (1 - s.p t) * (if s.B t ≤ v then (1 : ℝ) else 0) =
        min (s.B u) v - 1 / 2 := by
      have := integral_mul_indicator_primitive (x := fun t => 1 - s.p t)
        (fun a b => intervalIntegrable_const.sub (s.intervalIntegrable_p a b)) hu
        (fun t ht => by have := s.p_le_one ht.1; linarith) (a := 1 / 2) (v := v) hv2'
      simpa only [← s.B_eq_integral] using this
    rw [h2]
    simp only [hv2, ↓reduceIte]
    rw [min_eq_left ((s.A_le_half hu1).trans hv2')]
    unfold B
    rcases le_total (1 / 2 + u - s.A u) v with h | h
    · rw [min_eq_left h, min_eq_left (by linarith)]; ring
    · rw [min_eq_right h, min_eq_right (by linarith)]; ring

theorem measurable_kerR (v : ℝ) : Measurable (s.kerR v) := by
  unfold kerR
  exact (s.antitone.measurable.mul
    (Measurable.ite (s.measurableSet_A_le v) measurable_const measurable_const)).add
    ((measurable_const.sub s.antitone.measurable).mul
    (Measurable.ite (s.measurableSet_B_le v) measurable_const measurable_const))

/-- The conditional distribution function `v ↦ P(V ≤ v | U = u)` of `Q_A` on the unit interval. -/
noncomputable def kernelCDF (v u : I) : ℝ := s.kerR v u

theorem measurable_kernelCDF (v : I) : Measurable (s.kernelCDF v) :=
  (s.measurable_kerR v).comp measurable_subtype_coe

theorem kernelCDF_mem (v u : I) : s.kernelCDF v u ∈ Icc (0 : ℝ) 1 :=
  ⟨s.kerR_nonneg u.2.1 u.2.2, s.kerR_le_one u.2.1 u.2.2⟩

theorem integrable_kernelCDF (v : I) : Integrable (s.kernelCDF v) :=
  Verification.integrable_unit_bounded (s.measurable_kernelCDF v) (s.kernelCDF_mem v)

theorem monotone_kernelCDF (u : I) : Monotone (fun v : I => s.kernelCDF v u) :=
  fun _ _ h => s.kerR_mono h u.2.1 u.2.2

theorem antitone_kernelCDF (v : I) : Antitone (s.kernelCDF v) :=
  fun a b (h : a ≤ b) => s.kerR_anti a.2.1 (show (a : ℝ) ≤ b from h) b.2.2

theorem kernelCDF_one (u : I) : s.kernelCDF 1 u = 1 := by
  have h1 : s.A u ≤ 1 := (s.A_le_half u.2.2).trans (by norm_num)
  have h2 : s.B u ≤ 1 := s.B_le_one u.2.1 u.2.2
  simp [kernelCDF, kerR, h1, h2]

theorem kernelCDF_zero (u : I) (hu : u ≠ 0) : s.kernelCDF 0 u = 0 := by
  have hu' : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 (fun h => hu (Subtype.ext h.symm))
  have h1 : ¬ s.A u ≤ 0 := not_le.mpr (lt_of_lt_of_le (by linarith)
    (s.half_mul_le_A u.2.1 u.2.2))
  have h2 : ¬ s.B u ≤ 0 := not_le.mpr (lt_of_lt_of_le (by norm_num) (s.half_le_B u.2.1))
  simp [kernelCDF, kerR, h1, h2]

theorem kernelCDF_zero_ae : s.kernelCDF 0 =ᵐ[volume] fun _ => 0 := by
  have h : ∀ᵐ u : I, u ∉ ({0} : Set I) := (Set.countable_singleton _).ae_notMem volume
  filter_upwards [h] with u hu
  exact s.kernelCDF_zero u hu

theorem integral_kernelCDF_Iic (u v : I) :
    ∫ t in Iic u, s.kernelCDF v t = s.Qfun u v :=
  (Copula.integral_unit_Iic (s.kerR v) u).trans (s.integral_kerR u.2.1 u.2.2 v.2.1)

theorem Qfun_one {v : ℝ} (hv1 : v ≤ 1) : s.Qfun 1 v = v := by
  unfold Qfun
  rw [A_one]
  split_ifs with h
  · exact min_eq_right h
  · rw [show (1 : ℝ) / 2 + v - 1 / 2 = v by ring]
    exact min_eq_right hv1

theorem integral_kernelCDF (v : I) : ∫ t : I, s.kernelCDF v t = v := by
  have h := s.integral_kernelCDF_Iic 1 v
  have he : Iic (1 : I) = univ := by ext x; simp [unitInterval.le_one']
  rw [he, Measure.restrict_univ] at h
  rw [h]
  exact s.Qfun_one v.2.2

/-- **The maximal completion `Q_A`** of the median section (Lemma 5.1), a genuine bivariate copula
whose Markov kernel has distribution function `kernelCDF` (mass `p(u)` at `A(u)`, mass
`1 - p(u)` at `B(u)`). -/
noncomputable def completion : Copula 2 :=
  Verification.copulaOfConditionalAE s.kernelCDF s.integrable_kernelCDF s.monotone_kernelCDF
    s.kernelCDF_zero_ae (Filter.Eventually.of_forall (fun u => s.kernelCDF_one u))
    s.integral_kernelCDF

/-- Equation (5.1): the distribution function of `Q_A`. -/
theorem cdf_completion (u v : I) : s.completion.cdf ![u, v] = s.Qfun u v :=
  (Verification.copulaOfConditionalAE_cdf _ _ _ _ _ _ u v).trans (s.integral_kernelCDF_Iic u v)

/-- The Markov kernel of `Q_A`: for a.e. `u` the conditional distribution function of `V` given
`U = u` is `p(u) 1{A(u) ≤ v} + (1 - p(u)) 1{B(u) ≤ v}`. -/
theorem conditionalCDF_completion (v : I) :
    (fun u => s.completion.conditionalCDF u v) =ᵐ[volume] s.kernelCDF v :=
  Verification.copulaOfConditionalAE_kernel _ _ _ _ _ _
    (fun v u => (s.kernelCDF_mem v u).1) v

theorem cdf_completion_eq_integral (u v : I) :
    s.completion.cdf ![u, v] = ∫ t in Iic u, s.kernelCDF v t :=
  Verification.copulaOfConditionalAE_cdf _ _ _ _ _ _ u v

theorem cdf_completion_of_le_half (u v : I) (hv : (v : ℝ) ≤ 1 / 2) :
    s.completion.cdf ![u, v] = min (s.A u) v := by
  rw [cdf_completion]; unfold Qfun; simp only [hv, ↓reduceIte]

theorem cdf_completion_of_half_le (u v : I) (hv : 1 / 2 ≤ (v : ℝ)) :
    s.completion.cdf ![u, v] = min (u : ℝ) (s.A u + v - 1 / 2) := by
  rw [cdf_completion]; unfold Qfun
  rcases eq_or_lt_of_le hv with h | h
  · simp only [← h, le_refl, ↓reduceIte]
    rw [min_eq_left (s.A_le_half u.2.2)]
    rw [min_eq_right (by linarith [s.A_le_half u.2.2, s.A_le_self u.2.1])]
    ring
  · simp only [not_le.mpr h, ↓reduceIte]

/-- Lemma 5.1 (i): `Q_A` is stochastically increasing. -/
theorem completion_isSI : s.completion.IsSI := by
  intro a b c v hab hbc
  rw [s.cdf_completion_eq_integral, s.cdf_completion_eq_integral, s.cdf_completion_eq_integral]
  exact Copula.integral_Iic_concave_of_antitone (s.integrable_kernelCDF v)
    (s.antitone_kernelCDF v) a b c hab hbc

/-- Lemma 5.1 (i): the median section of `Q_A` is `A`. -/
theorem cdf_completion_half (u : I) : s.completion.cdf ![u, Copula.unitHalf] = s.A u := by
  rw [s.cdf_completion_of_le_half u _ (by simp [Copula.unitHalf])]
  exact min_eq_left (s.A_le_half u.2.2)

/-- Lemma 5.1 (ii): every copula with median section `A` lies below `Q_A`. -/
theorem cdf_le_completion (C : Copula 2) (hC : ∀ u : I, C.cdf ![u, Copula.unitHalf] = s.A u)
    (u v : I) : C.cdf ![u, v] ≤ s.completion.cdf ![u, v] := by
  have hu : C.cdf ![u, v] ≤ u := by simpa using C.cdf_le_coord ![u, v] 0
  have hv : C.cdf ![u, v] ≤ v := by simpa using C.cdf_le_coord ![u, v] 1
  have hh : ((Copula.unitHalf : I) : ℝ) = 1 / 2 := rfl
  rcases le_total (v : ℝ) (1 / 2) with h | h
  · rw [s.cdf_completion_of_le_half u v h]
    have hvh : v ≤ Copula.unitHalf := by
      change (v : ℝ) ≤ ((Copula.unitHalf : I) : ℝ); rw [hh]; exact h
    have hm : C.cdf ![u, v] ≤ C.cdf ![u, Copula.unitHalf] :=
      C.monotone_cdf (by intro i; fin_cases i <;> simp [hvh])
    exact le_min (by rw [← hC u]; exact hm) hv
  · rw [s.cdf_completion_of_half_le u v h]
    have hvh : Copula.unitHalf ≤ v := by
      change ((Copula.unitHalf : I) : ℝ) ≤ (v : ℝ); rw [hh]; exact h
    have hl := C.cdf_sub_le_sum_abs ![u, v] ![u, Copula.unitHalf]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sub_self, abs_zero,
      zero_add] at hl
    rw [abs_of_nonneg (by rw [hh]; linarith), hh] at hl
    refine le_min hu ?_
    have := hC u
    linarith

/-- The atom `A(u)` of the kernel of `Q_A`, as a point of the unit interval. -/
noncomputable def atomA (u : I) : I := ⟨s.A u, s.A_nonneg u.2.1 u.2.2,
  (s.A_le_half u.2.2).trans (by norm_num)⟩

/-- The atom `B(u)` of the kernel of `Q_A`, as a point of the unit interval. -/
noncomputable def atomB (u : I) : I := ⟨s.B u, (by have := s.half_le_B u.2.1; linarith),
  s.B_le_one u.2.1 u.2.2⟩

theorem atomA_le_iff (u v : I) : s.atomA u ≤ v ↔ s.A u ≤ (v : ℝ) := Iff.rfl

theorem atomB_le_iff (u v : I) : s.atomB u ≤ v ↔ s.B u ≤ (v : ℝ) := Iff.rfl

/-- The Markov kernel of `Q_A`: mass `p(u)` at `A(u)` and mass `1 - p(u)` at `B(u)`. -/
noncomputable def kernelMeasure (u : I) : Measure I :=
  ENNReal.ofReal (s.p u) • Measure.dirac (s.atomA u) +
    ENNReal.ofReal (1 - s.p u) • Measure.dirac (s.atomB u)

/-- The distribution function of `kernelMeasure` is `kernelCDF`. -/
theorem kernelMeasure_real_Iic (v u : I) :
    (s.kernelMeasure u).real (Iic v) = s.kernelCDF v u := by
  have h0 := s.p_nonneg u.2.2
  have h1 := s.p_le_one u.2.1
  unfold kernelMeasure kernelCDF kerR Measure.real
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ measurableSet_Iic, Measure.dirac_apply' _ measurableSet_Iic]
  simp only [indicator, mem_Iic, atomA_le_iff, atomB_le_iff, smul_eq_mul, Pi.one_apply, mul_ite,
    mul_one, mul_zero]
  rw [ENNReal.toReal_add (by split_ifs <;> simp) (by split_ifs <;> simp)]
  by_cases ha : s.A u ≤ v <;> by_cases hb : s.B u ≤ v <;>
    simp [ha, hb, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - s.p u),
      ENNReal.toReal_ofReal h0]

/-- The maximal completion depends only on the section `A` (on `[0,1]`). -/
theorem completion_congr (t : MedianSection) (h : ∀ u ∈ Icc (0 : ℝ) 1, s.A u = t.A u) :
    s.completion = t.completion := by
  apply Copula.ext_cdf_two
  intro u v
  rw [cdf_completion, cdf_completion]
  unfold Qfun
  rw [h u u.2]

end MedianSection

end Papers.OrendayLaresRockel2026XiBeta
