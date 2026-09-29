import Papers.OrendayLaresRockel2026XiBeta.TentV2Basic
import Papers.OrendayLaresRockel2026XiBeta.TentDensity
import Papers.OrendayLaresRockel2026XiBeta.IntervalExchange

/-! # Proposition 3.1 (tent copulas), in the notation of the article

`L_b = leftBoundary b hb`, `L_b(u,v) = u v + ℓ(u) g_b(v)` (equation (3.2)):

* the CDF formula and its two strip forms,
* the copula density `c_b = 1 + σ(u) g_b'(v) ∈ {0,1,2}` a.e. (3.3), and
  `L_b(u,v) = ∫∫ c_b`,
* the Markov kernel `∂₁ L_b(u,v) = v + σ(u) g_b(v)` (3.4) (a.e. and classical derivative),
* `v ↦ v ± g_b(v)` are distribution functions,
* `β(L_b) = b`, `L_b(1/2,1/2) = (1+b)/4`, `ξ(L_b) = |b|³/2` and the integral computation
  `∫∫ (∂₁ L_b)² = 1/3 + |b|³/12`.
-/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

/-- Equation (3.2): `L_b(u,v) = u v + ℓ(u) g_b(v)`. -/
theorem leftBoundary_cdf_paper (b : ℝ) (hb : b ∈ Icc (-1) 1) (u v : I) :
    (leftBoundary b hb).cdf ![u, v] = (u : ℝ) * v + ellFun u * tentG b v := by
  rw [leftBoundary_cdf, ← tentDisplacement_eq_tentG b hb v]
  rfl

/-- `L_b(u,v) = u (v + g_b(v))` on the strip `u ≤ 1/2`. -/
theorem leftBoundary_cdf_left_strip (b : ℝ) (hb : b ∈ Icc (-1) 1) {u : I} (v : I)
    (hu : (u : ℝ) ≤ 1 / 2) :
    (leftBoundary b hb).cdf ![u, v] = u * (v + tentG b v) := by
  rw [leftBoundary_cdf_paper, ellFun, min_eq_left (by linarith)]
  ring

/-- `L_b(u,v) = u v + (1 - u) g_b(v)` on the strip `u ≥ 1/2`. -/
theorem leftBoundary_cdf_right_strip (b : ℝ) (hb : b ∈ Icc (-1) 1) {u : I} (v : I)
    (hu : 1 / 2 ≤ (u : ℝ)) :
    (leftBoundary b hb).cdf ![u, v] = u * v + (1 - u) * tentG b v := by
  rw [leftBoundary_cdf_paper, ellFun, min_eq_right (by linarith)]

theorem leftBoundary_cdf_half (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).cdf ![Copula.unitHalf, Copula.unitHalf] = (1 + b) / 4 := by
  rw [leftBoundary_cdf_paper]
  change 1 / 2 * (1 / 2) + ellFun (1 / 2) * tentG b (1 / 2) = _
  rw [tentG_half, ellFun, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, min_self]
  ring

/-- The two conditional distribution functions `v ↦ v + g_b(v)` and `v ↦ v - g_b(v)` are
nondecreasing, vanish at `0` and equal `1` at `1`. -/
theorem tent_distribution_functions (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    Monotone (fun v : ℝ => v + tentG b v) ∧ Monotone (fun v : ℝ => v - tentG b v) ∧
      tentG b 0 = 0 ∧ tentG b 1 = 0 := by
  have hb0 : |b| ≤ 1 := abs_le.mpr hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v w hvw
    have := tentG_lipschitz b w v
    rw [abs_of_nonneg (sub_nonneg.mpr hvw) |> fun h => h] at this
    · have h2 := (abs_le.mp this).1
      simp only
      linarith
  · intro v w hvw
    have := tentG_lipschitz b w v
    have h2 := (abs_le.mp this).2
    rw [abs_of_nonneg (sub_nonneg.mpr hvw)] at h2
    simp only
    linarith
  · unfold tentG medianTent
    rw [max_eq_left (by rw [zero_sub, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]; linarith),
      mul_zero]
  · unfold tentG medianTent
    rw [max_eq_left (by rw [abs_of_pos (by norm_num : (0:ℝ) < 1 - 1 / 2)]; linarith), mul_zero]

/-- Equation (3.4), classical form: for `u ≠ 1/2` the map `u ↦ L_b(u,v)` (extended by its
formula to `ℝ`) has derivative `v + σ(u) g_b(v)`. -/
theorem hasDerivAt_tent_formula (b v : ℝ) {u : ℝ} (hu : u ≠ 1 / 2) :
    HasDerivAt (fun w : ℝ => w * v + ellFun w * tentG b v) (v + sigmaFun u * tentG b v) u := by
  have h1 : HasDerivAt (fun w : ℝ => w * v) v u := by
    simpa using (hasDerivAt_id u).mul_const v
  have h2 := (hasDerivAt_ellFun hu).mul_const (tentG b v)
  have := h1.add h2
  convert this using 1

/-- Equation (3.4): the Markov kernel `∂₁ L_b(u,v) = v + σ(u) g_b(v)` for a.e. `u`. -/
theorem leftBoundary_kernel_paper (b : ℝ) (hb : b ∈ Icc (-1) 1) (v : I) :
    (fun u => (leftBoundary b hb).conditionalCDF u v) =ᵐ[volume]
      fun u : I => (v : ℝ) + sigmaFun u * tentG b v := by
  filter_upwards [leftBoundary_conditionalCDF b hb v, ae_coe_ne (1 / 2)] with u h1 h2
  rw [h1, ← tentDisplacement_eq_tentG b hb v]
  by_cases hu : u ≤ Copula.unitHalf
  · have : (u : ℝ) < 1 / 2 := lt_of_le_of_ne hu h2
    rw [ite_eq_left hu, sigmaFun, ite_eq_left this]
    ring
  · have : ¬ (u : ℝ) < 1 / 2 := fun h => hu (le_of_lt h)
    rw [ite_eq_right hu, sigmaFun, ite_eq_right this]
    ring

/-- Equation (3.4) with the classical partial derivative: for a.e. `u`,
`∂₁L_b(u,v) = v + σ(u) g_b(v)`. -/
theorem leftBoundary_deriv_paper (b : ℝ) (hb : b ∈ Icc (-1) 1) (v : I) :
    ∀ᵐ u : I, deriv ((leftBoundary b hb).cdfSection v) (u : ℝ) =
      (v : ℝ) + sigmaFun u * tentG b v := by
  filter_upwards [(leftBoundary b hb).conditionalCDF_eq_deriv v, leftBoundary_kernel_paper b hb v]
    with u h1 h2
  rw [← h1, h2]

/-! ### The density (3.3) -/

theorem tentSlope_eq (r v : I) (h1 : (v : ℝ) ≠ (1 - r) / 2) (h2 : (v : ℝ) ≠ 1 / 2)
    (h3 : (v : ℝ) ≠ (1 + r) / 2) :
    tentSlope r v = (if (1 - (r : ℝ)) / 2 < v ∧ (v : ℝ) < 1 / 2 then 1 else 0) -
      (if 1 / 2 < (v : ℝ) ∧ (v : ℝ) < (1 + r) / 2 then 1 else 0) := by
  have hr0 := r.property.1
  have hr1 := r.property.2
  by_cases hr : r = 1
  · subst hr
    have hr' : ((1 : I) : ℝ) = 1 := rfl
    simp only [tentSlope, ite_true, medianSign, hr']
    have h1' : (v : ℝ) ≠ 0 := by simpa using h1
    have h3' : (v : ℝ) ≠ 1 := by simpa [show (1 + 1 : ℝ) / 2 = 1 by norm_num] using h3
    have hv0 : 0 < (v : ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm h1')
    have hv1 : (v : ℝ) < 1 := lt_of_le_of_ne v.property.2 h3'
    by_cases hv : v ≤ Copula.unitHalf
    · have hv' : (v : ℝ) < 1 / 2 := lt_of_le_of_ne hv h2
      have hp : (1 - 1) / 2 < (v : ℝ) ∧ (v : ℝ) < 1 / 2 := ⟨by linarith, hv'⟩
      have hn : ¬ (1 / 2 < (v : ℝ) ∧ (v : ℝ) < (1 + 1) / 2) := fun h => by linarith [h.1]
      rw [ite_eq_left hv, ite_eq_left hp, ite_eq_right hn]
      norm_num
    · have hv' : 1 / 2 < (v : ℝ) := lt_of_not_ge hv
      have hn : ¬ ((1 - 1) / 2 < (v : ℝ) ∧ (v : ℝ) < 1 / 2) := fun h => by linarith [h.2]
      have hp : 1 / 2 < (v : ℝ) ∧ (v : ℝ) < (1 + 1) / 2 := ⟨hv', by linarith⟩
      rw [ite_eq_right hv, ite_eq_right hn, ite_eq_left hp]
      norm_num
  · simp only [tentSlope, ite_eq_right hr, lowerStep]
    have hs : (tentStart r : ℝ) = (1 - r) / 2 := rfl
    have he : (tentEnd r : ℝ) = (1 + r) / 2 := rfl
    have hu : (Copula.unitHalf : ℝ) = 1 / 2 := rfl
    simp only [← Subtype.coe_le_coe, hs, he, hu]
    rcases lt_or_gt_of_ne h1 with a | a
    · have hn1 : ¬ ((1 - (r : ℝ)) / 2 < v ∧ (v : ℝ) < 1 / 2) := fun h => by linarith [h.1]
      have hn2 : ¬ (1 / 2 < (v : ℝ) ∧ (v : ℝ) < (1 + r) / 2) := fun h => by linarith [h.1]
      rw [ite_eq_right hn1, ite_eq_right hn2, ite_eq_left a.le, ite_eq_left (by linarith : (v : ℝ) ≤ 1 / 2),
        ite_eq_left (by linarith : (v : ℝ) ≤ (1 + r) / 2)]
      norm_num
    · rcases lt_or_gt_of_ne h2 with b | b
      · have hp : (1 - (r : ℝ)) / 2 < v ∧ (v : ℝ) < 1 / 2 := ⟨a, b⟩
        have hn2 : ¬ (1 / 2 < (v : ℝ) ∧ (v : ℝ) < (1 + r) / 2) := fun h => by linarith [h.1]
        rw [ite_eq_left hp, ite_eq_right hn2, ite_eq_right (not_le.mpr a),
          ite_eq_left b.le, ite_eq_left (by linarith : (v : ℝ) ≤ (1 + r) / 2)]
        norm_num
      · rcases lt_or_gt_of_ne h3 with c | c
        · have hn1 : ¬ ((1 - (r : ℝ)) / 2 < v ∧ (v : ℝ) < 1 / 2) := fun h => by linarith [h.2]
          have hp : 1 / 2 < (v : ℝ) ∧ (v : ℝ) < (1 + r) / 2 := ⟨b, c⟩
          rw [ite_eq_right hn1, ite_eq_left hp, ite_eq_right (not_le.mpr a),
            ite_eq_right (not_le.mpr b), ite_eq_left c.le]
          norm_num
        · have hn1 : ¬ ((1 - (r : ℝ)) / 2 < v ∧ (v : ℝ) < 1 / 2) := fun h => by linarith [h.2]
          have hn2 : ¬ (1 / 2 < (v : ℝ) ∧ (v : ℝ) < (1 + r) / 2) := fun h => by linarith [h.2]
          rw [ite_eq_right hn1, ite_eq_right hn2, ite_eq_right (not_le.mpr a),
            ite_eq_right (not_le.mpr b), ite_eq_right (not_le.mpr c)]
          norm_num

theorem signedTentSlope_eq_tentGDeriv (b : ℝ) (hb : b ∈ Icc (-1) 1) (v : I)
    (h1 : (v : ℝ) ≠ (1 - |b|) / 2) (h2 : (v : ℝ) ≠ 1 / 2) (h3 : (v : ℝ) ≠ (1 + |b|) / 2) :
    signedTentSlope b hb v = tentGDeriv b v := by
  unfold signedTentSlope tentGDeriv
  by_cases h : 0 ≤ b
  · rw [dite_eq_left h]
    rw [abs_of_nonneg h] at h1 h3 ⊢
    have hf := tentSlope_eq ⟨b, by constructor <;> linarith [hb.2]⟩ v h1 h2 h3
    rw [hf]
    rcases h.lt_or_eq with hp | hz
    · rw [sgn_of_pos hp, one_mul]
    · subst hz
      simp [sgn_zero]
  · rw [dite_eq_right h]
    have hn : b < 0 := lt_of_not_ge h
    rw [abs_of_neg hn] at h1 h3 ⊢
    have hf := tentSlope_eq ⟨-b, by constructor <;> linarith [hb.1]⟩ v h1 h2 h3
    rw [hf, sgn_of_neg hn]
    ring

theorem ae_coord_ne (i : Fin 2) (c : ℝ) :
    ∀ᵐ x ∂(volume : Measure (Fin 2 → I)), (x i : ℝ) ≠ c := by
  rw [ae_iff]
  apply Measure.pi_eval_preimage_null (fun _ : Fin 2 => (volume : Measure I)) (i := i)
    (s := {u : I | ¬ (u : ℝ) ≠ c})
  exact ae_iff.mp (ae_coe_ne c)

/-- The density of the article, `c_b(u,v) = 1 + σ(u) g_b'(v)`. -/
noncomputable def tentDensityPaper (b : ℝ) (x : Fin 2 → I) : ℝ :=
  1 + sigmaFun (x 0) * tentGDeriv b (x 1)

/-- The version-1 density agrees a.e. with `1 + σ(u) g_b'(v)`. -/
theorem tentDensity_ae_eq_paper (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    ∀ᵐ x ∂(volume : Measure (Fin 2 → I)), tentDensity b hb x = tentDensityPaper b x := by
  filter_upwards [ae_coord_ne 1 ((1 - |b|) / 2), ae_coord_ne 1 (1 / 2),
    ae_coord_ne 1 ((1 + |b|) / 2), ae_coord_ne 0 (1 / 2)] with x h1 h2 h3 h4
  unfold tentDensity tentDensityPaper
  rw [signedTentSlope_eq_tentGDeriv b hb (x 1) h1 h2 h3]
  congr 2
  unfold medianSign sigmaFun
  by_cases hu : x 0 ≤ Copula.unitHalf
  · have : ((x 0 : I) : ℝ) < 1 / 2 := lt_of_le_of_ne hu h4
    rw [ite_eq_left hu, ite_eq_left this]
  · have : ¬ ((x 0 : I) : ℝ) < 1 / 2 := fun h => hu (le_of_lt h)
    rw [ite_eq_right hu, ite_eq_right this]

/-- Equation (3.3): the actual law of `L_b` has density `1 + σ(u) g_b'(v)`. -/
theorem leftBoundary_density_paper (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (tentDensityPaper b x)) := by
  rw [leftBoundary_density]
  apply withDensity_congr_ae
  filter_upwards [tentDensity_ae_eq_paper b hb] with x hx
  rw [hx]

/-- The density takes the values `0`, `1`, `2` almost everywhere. -/
theorem tentDensityPaper_values_ae (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    ∀ᵐ x ∂(volume : Measure (Fin 2 → I)),
      tentDensityPaper b x = 0 ∨ tentDensityPaper b x = 1 ∨ tentDensityPaper b x = 2 := by
  filter_upwards [tentDensity_ae_eq_paper b hb] with x hx
  rw [← hx]
  exact tentDensity_values b hb x

theorem measurable_tentGDeriv (b : ℝ) : Measurable (tentGDeriv b) := by
  unfold tentGDeriv
  refine measurable_const.mul (Measurable.sub ?_ ?_)
  · exact Measurable.ite ((measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const)) measurable_const measurable_const
  · exact Measurable.ite ((measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const)) measurable_const measurable_const

theorem measurable_sigmaFun : Measurable sigmaFun :=
  Measurable.ite measurableSet_Iio measurable_const measurable_const

theorem measurable_tentDensityPaper (b : ℝ) : Measurable (tentDensityPaper b) := by
  unfold tentDensityPaper
  have h0 : Measurable (fun x : Fin 2 → I => sigmaFun ((x 0 : I) : ℝ)) :=
    measurable_sigmaFun.comp (continuous_subtype_val.measurable.comp (measurable_pi_apply 0))
  have h1 : Measurable (fun x : Fin 2 → I => tentGDeriv b ((x 1 : I) : ℝ)) :=
    (measurable_tentGDeriv b).comp (continuous_subtype_val.measurable.comp (measurable_pi_apply 1))
  exact measurable_const.add (h0.mul h1)

/-- `L_b(u,v) = ∫_{[0,u]×[0,v]} c_b`. -/
theorem leftBoundary_cdf_eq_integral_density (b : ℝ) (hb : b ∈ Icc (-1) 1) (u v : I) :
    (leftBoundary b hb).cdf ![u, v] =
      ∫ x in Iic (![u, v] : Fin 2 → I), tentDensityPaper b x := by
  have hn : ∀ᵐ x ∂(volume : Measure (Fin 2 → I)), 0 ≤ tentDensityPaper b x := by
    filter_upwards [tentDensityPaper_values_ae b hb] with x hx
    rcases hx with h | h | h <;> rw [h] <;> norm_num
  have hi : Integrable (tentDensityPaper b) := by
    refine (integrable_const (2 : ℝ)).mono' (measurable_tentDensityPaper b).aestronglyMeasurable ?_
    filter_upwards [tentDensityPaper_values_ae b hb] with x hx
    rcases hx with h | h | h <;> rw [h] <;> norm_num
  change ((leftBoundary b hb).toMeasure).real (Iic ![u, v]) = _
  rw [leftBoundary_density_paper, Measure.real, withDensity_apply _ measurableSet_Iic,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_restrict_of_ae hn)]
  exact ENNReal.toReal_ofReal (integral_nonneg_of_ae (ae_restrict_of_ae hn))

theorem integral_sigmaFun_sq_kernel (g w : ℝ) :
    (∫ u : I, (w + sigmaFun u * g) ^ 2) = w ^ 2 + g ^ 2 := by
  have hae : (fun u : I => (w + sigmaFun u * g) ^ 2) =ᵐ[volume]
      fun u : I => if u ≤ Copula.unitHalf then (w + g) ^ 2 else (w - g) ^ 2 := by
    filter_upwards [ae_coe_ne (1 / 2)] with u hu
    by_cases h : u ≤ Copula.unitHalf
    · have : (u : ℝ) < 1 / 2 := lt_of_le_of_ne h hu
      rw [ite_eq_left h, sigmaFun, ite_eq_left this]
      ring
    · have : ¬ (u : ℝ) < 1 / 2 := fun h' => h (le_of_lt h')
      rw [ite_eq_right h, sigmaFun, ite_eq_right this]
      ring
  rw [integral_congr_ae hae]
  have h := integral_median_step ((w + g) ^ 2) ((w - g) ^ 2) 1
  have he : Iic (1 : I) = univ := by ext u; simp [unitInterval.le_one']
  rw [he, Measure.restrict_univ] at h
  rw [h]
  norm_num
  ring

/-- The computation in the proof of Proposition 3.1:
`∫∫ (∂₁L_b)² = ∫ (v² + g_b(v)²) dv = 1/3 + |b|³/12`. -/
theorem tent_kernel_sq_integral (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (∫ v : I, ∫ u : I, ((v : ℝ) + sigmaFun u * tentG b v) ^ 2) = 1 / 3 + |b| ^ 3 / 12 := by
  simp_rw [integral_sigmaFun_sq_kernel]
  rw [integral_add (Copula.integrable_continuous_unit volume (by fun_prop))
    (Copula.integrable_continuous_unit volume (by
      have : Continuous (tentG b) := by
        unfold tentG; exact continuous_const.mul (continuous_medianTent _)
      fun_prop)), integral_tentG_sq b hb, Copula.integral_unit_pow]
  norm_num

/-- Proposition 3.1, `ξ(L_b) = |b|³/2` computed from the kernel exactly as in the article. -/
theorem xi_leftBoundary_from_kernel (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).chatterjeeXi = 6 * (1 / 3 + |b| ^ 3 / 12) - 2 := by
  unfold Copula.chatterjeeXi
  rw [← tent_kernel_sq_integral b hb]
  congr 2
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun v => ?_)
  apply integral_congr_ae
  filter_upwards [leftBoundary_kernel_paper b hb v] with u hu
  simp only [hu]

end Papers.OrendayLaresRockel2026XiBeta
