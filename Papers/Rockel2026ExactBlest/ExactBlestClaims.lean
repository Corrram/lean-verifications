import Papers.Rockel2026ExactBlest.ExactBlestTransposeRegion
import Papers.Rockel2026ExactBlest.ExactBlestConditional

/-!
# Further claims of the revised manuscript

Checks for statements in exact-blest-regions.tex that sit outside the labeled results or were
added in the revision: the dual-certificate lemma for general continuous costs, the derivative formulas for `Υ` used in the corollary on `(ν,νᵀ)`, the
symmetries (and the failure of central symmetry) of the two regions, the trivial bound `1/2`,
the numerical fibres in the discussion, the non-extremality of `A_w` for `w > 1/2`, the shuffle
description of the `ρ - η` extremizers, and the values quoted in the figure captions.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval Topology
open Papers.Rockel2026XiBlest

namespace Papers.Rockel2026ExactBlest

noncomputable section
set_option maxHeartbeats 4000000

/-! ## The dual-certificate lemma -/

/-- Part (a) of the dual-certificate lemma: for any coupling of two uniform laws (the law of an
arbitrary copula), any continuous cost `c`, and continuous potentials with `c ≤ φ ⊕ ψ` on the
unit square, the expected cost is at most `∫ φ + ∫ ψ`, with equality exactly when the coupling
is concentrated on the contact set. -/
theorem dual_certificate (C : Copula 2) (c : ℝ → ℝ → ℝ) (φ ψ : ℝ → ℝ)
    (hc : Continuous (Function.uncurry c)) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hdual : ∀ x ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) 1, c x z ≤ φ x + ψ z) :
    (∫ p, c (p 0) (p 1) ∂C.toMeasure) ≤ (∫ u : I, φ u) + (∫ u : I, ψ u) ∧
      ((∫ p, c (p 0) (p 1) ∂C.toMeasure) = (∫ u : I, φ u) + (∫ u : I, ψ u) ↔
        ∀ᵐ p ∂C.toMeasure, φ (p 0) + ψ (p 1) = c (p 0) (p 1)) := by
  have hcc : Continuous (fun p : Fin 2 → I => c (p 0) (p 1)) :=
    hc.comp (show Continuous (fun p : Fin 2 → I => ((p 0 : ℝ), (p 1 : ℝ))) by fun_prop)
  have hi : Integrable (fun p : Fin 2 → I => c (p 0) (p 1)) C.toMeasure :=
    Copula.integrable_continuous_cube _ hcc
  have hp : Integrable (fun p : Fin 2 → I => φ (p 0)) C.toMeasure :=
    Copula.integrable_continuous_cube _ (hφ.comp (by fun_prop))
  have hq : Integrable (fun p : Fin 2 → I => ψ (p 1)) C.toMeasure :=
    Copula.integrable_continuous_cube _ (hψ.comp (by fun_prop))
  have h0 : (∫ p, φ (p 0) ∂C.toMeasure) = ∫ u : I, φ u :=
    C.integral_eval 0 (fun u : I => φ u) (hφ.measurable.comp measurable_subtype_coe)
  have h1 : (∫ p, ψ (p 1) ∂C.toMeasure) = ∫ u : I, ψ u :=
    C.integral_eval 1 (fun u : I => ψ u) (hψ.measurable.comp measurable_subtype_coe)
  let slack := fun p : Fin 2 → I => φ (p 0) + ψ (p 1) - c (p 0) (p 1)
  have hnon : 0 ≤ slack := fun p => sub_nonneg.mpr (hdual _ (p 0).property _ (p 1).property)
  have hsi : Integrable slack C.toMeasure := (hp.add hq).sub hi
  have hint : (∫ p, slack p ∂C.toMeasure) =
      (∫ u : I, φ u) + (∫ u : I, ψ u) - ∫ p, c (p 0) (p 1) ∂C.toMeasure := by
    dsimp only [slack]
    have hsub := integral_sub (hp.add hq) hi
    simp only [Pi.add_apply] at hsub
    rw [hsub, integral_add hp hq, h0, h1]
  have hge : 0 ≤ ∫ p, slack p ∂C.toMeasure := integral_nonneg hnon
  refine ⟨by linarith, ?_⟩
  constructor
  · intro heq
    have hz : (∫ p, slack p ∂C.toMeasure) = 0 := by linarith
    have hae := (integral_eq_zero_iff_of_nonneg hnon hsi).mp hz
    filter_upwards [hae] with p hp0
    have hs : slack p = 0 := hp0
    dsimp only [slack] at hs
    linarith
  · intro hae
    have hz : (∫ p, slack p ∂C.toMeasure) = 0 := by
      rw [integral_eq_zero_iff_of_nonneg hnon hsi]
      filter_upwards [hae] with p hp0
      show φ (p 0) + ψ (p 1) - c (p 0) (p 1) = 0
      linarith
    linarith

/-- Part (b) of the dual-certificate lemma: a coupling concentrated on the graph of a
measurable map over the first coordinate, up to finitely many vertical and horizontal lines,
is the law of `(X, T(X))`. -/
theorem dual_certificate_graph (C : Copula 2) (T : I → I) (hT : Measurable T)
    (N₁ N₂ : Finset ℝ)
    (hK : ∀ᵐ p ∂C.toMeasure, p 1 = T (p 0) ∨ (p 0 : ℝ) ∈ N₁ ∨ (p 1 : ℝ) ∈ N₂) :
    C.toMeasure = (volume : Measure I).map (fun u => ![u, T u]) := by
  have h1 : ∀ᵐ p ∂C.toMeasure, ∀ a ∈ N₁, (p 0 : ℝ) ≠ a :=
    (Filter.eventually_all_finset N₁).mpr (fun a _ => ae_coord_ne C 0 a)
  have h2 : ∀ᵐ p ∂C.toMeasure, ∀ a ∈ N₂, (p 1 : ℝ) ≠ a :=
    (Filter.eventually_all_finset N₂).mpr (fun a _ => ae_coord_ne C 1 a)
  have hg : ∀ᵐ p ∂C.toMeasure, p 1 = T (p 0) := by
    filter_upwards [hK, h1, h2] with p hp hp1 hp2
    rcases hp with h | h | h
    · exact h
    · exact (hp1 _ h rfl).elim
    · exact (hp2 _ h rfl).elim
  have hm : Measurable (fun u : I => ![u, T u]) := by fun_prop
  rw [← C.map_eval 0, Measure.map_map hm (measurable_pi_apply 0)]
  have hv : (fun x : Fin 2 → I => ![x 0, T (x 0)]) =ᵐ[C.toMeasure] id := by
    filter_upwards [hg] with x hx
    funext i
    fin_cases i
    · rfl
    · exact hx.symm
  change C.toMeasure = C.toMeasure.map (fun x => ![x 0, T (x 0)])
  rw [Measure.map_congr hv, Measure.map_id]

/-- Part (b) with the roles of the coordinates exchanged. -/
theorem dual_certificate_reverse_graph (C : Copula 2) (T : I → I) (hT : Measurable T)
    (N₁ N₂ : Finset ℝ)
    (hK : ∀ᵐ p ∂C.toMeasure, p 0 = T (p 1) ∨ (p 0 : ℝ) ∈ N₁ ∨ (p 1 : ℝ) ∈ N₂) :
    C.toMeasure = (volume : Measure I).map (fun u => ![T u, u]) := by
  have h1 : ∀ᵐ p ∂C.toMeasure, ∀ a ∈ N₁, (p 0 : ℝ) ≠ a :=
    (Filter.eventually_all_finset N₁).mpr (fun a _ => ae_coord_ne C 0 a)
  have h2 : ∀ᵐ p ∂C.toMeasure, ∀ a ∈ N₂, (p 1 : ℝ) ≠ a :=
    (Filter.eventually_all_finset N₂).mpr (fun a _ => ae_coord_ne C 1 a)
  have hg : ∀ᵐ p ∂C.toMeasure, p 0 = T (p 1) := by
    filter_upwards [hK, h1, h2] with p hp hp1 hp2
    rcases hp with h | h | h
    · exact h
    · exact (hp1 _ h rfl).elim
    · exact (hp2 _ h rfl).elim
  have hm : Measurable (fun u : I => ![T u, u]) := by fun_prop
  rw [← C.map_eval 1, Measure.map_map hm (measurable_pi_apply 1)]
  have hv : (fun x : Fin 2 → I => ![T (x 1), x 1]) =ᵐ[C.toMeasure] id := by
    filter_upwards [hg] with x hx
    funext i
    fin_cases i
    · exact hx.symm
    · rfl
  change C.toMeasure = C.toMeasure.map (fun x => ![T (x 1), x 1])
  rw [Measure.map_congr hv, Measure.map_id]

/-! ## Normalization and the two theorems in the form stated in the introduction -/

theorem nu_normalization :
    blestNu (Copula.comonotonic 2) = 1 ∧ blestNu Copula.countermonotonic = -1 ∧
      blestNu (Copula.independence 2) = 0 :=
  ⟨blest_comonotonic, blest_countermonotonic, blest_independence⟩

/-- The identity `2r - Φ(r) = -Φ(-r)` stated after the definition of `Φ`. -/
theorem rhoBoundary_reflect (r : ℝ) : 2 * r - rhoBoundary r = -rhoBoundary (-r) := by
  by_cases hr : 0 ≤ r
  · rw [rhoBoundary_neg r hr]
    ring
  · have h := rhoBoundary_neg (-r) (by linarith)
    rw [neg_neg] at h
    linarith

/-- In Theorem 1.1, the unique lower-boundary copula is the survival copula of the upper one. -/
theorem rho_lower_eq_survival_upper (C D : Copula 2)
    (hc : blestNu C = rhoBoundary C.spearmanRho)
    (hd : blestNu D = 2 * D.spearmanRho - rhoBoundary D.spearmanRho)
    (hr : D.spearmanRho = C.spearmanRho) : D = C.survivalCopula := by
  obtain ⟨E, _, hE⟩ := rho_lower_exists_unique C.spearmanRho C.spearmanRho_mem_Icc
  have h1 := hE D ⟨hr, by rw [hd, hr]⟩
  have h2 := hE C.survivalCopula
    ⟨Copula.spearmanRho_survivalCopula C, by rw [nu_survival, hc]⟩
  exact h1.trans h2.symm

/-- In Theorem 1.2, the unique lower-boundary copula is the transpose of the upper one. -/
theorem eta_lower_eq_transpose_upper (C D : Copula 2)
    (hc : blestNu C = eta C + etaGap (eta C))
    (hd : blestNu D = eta D - etaGap (eta D)) (he : eta D = eta C) : D = C.transpose := by
  apply eta_lower_unique D C.transpose (he.trans (eta_transpose C).symm) hd
  rw [eta_transpose, nu_transpose, hc]
  ring

/-- The fibre above `η = e` has length `2 Υ(e)`, the largest asymmetry at that `η`. -/
theorem eta_fibre_max_asymmetry (e : ℝ) (he : e ∈ Icc (-1 : ℝ) 1) :
    IsGreatest {d | ∃ C : Copula 2, eta C = e ∧ |blestNu C - blestNu C.transpose| = d}
      (2 * etaGap e) := by
  constructor
  · obtain ⟨C, hc, _⟩ := eta_upper_exists_unique e he
    refine ⟨C, hc.1, ?_⟩
    rw [asymmetry_identity, hc.2, hc.1, show e + etaGap e - e = etaGap e by ring,
      abs_of_nonneg (etaGap_nonneg e he)]
  · rintro d ⟨C, hc, rfl⟩
    rw [asymmetry_identity]
    have h := (eta_fibre_displayed e (blestNu C)).mp ⟨C, hc, rfl⟩
    rw [hc]
    linarith [h.2]

/-! ## Symmetries of the two regions -/

/-- `C ↦ C^⊥` negates `(ρ,ν)`, so the `(ρ,ν)`-region is symmetric about the origin. -/
theorem rho_nu_region_neg (p : ℝ × ℝ)
    (hp : p ∈ Set.range (fun C : Copula 2 => (C.spearmanRho, blestNu C))) :
    -p ∈ Set.range (fun C : Copula 2 => (C.spearmanRho, blestNu C)) := by
  obtain ⟨C, rfl⟩ := hp
  refine ⟨C.reflect {1}, ?_⟩
  simp only [Copula.spearmanRho_reflect_second, blest_reflect_second, Prod.neg_mk]

/-- Survival reflects every `(ρ,ν)`-fibre about the diagonal. -/
theorem rho_nu_fibre_reflect (r n : ℝ)
    (hp : (r, n) ∈ Set.range (fun C : Copula 2 => (C.spearmanRho, blestNu C))) :
    (r, 2 * r - n) ∈ Set.range (fun C : Copula 2 => (C.spearmanRho, blestNu C)) := by
  obtain ⟨C, hC⟩ := hp
  simp only [Prod.mk.injEq] at hC
  refine ⟨C.survivalCopula, ?_⟩
  simp only [Prod.mk.injEq]
  rw [Copula.spearmanRho_survivalCopula, nu_survival, hC.1, hC.2]
  exact ⟨rfl, rfl⟩

/-- Transposition reflects every `(η,ν)`-fibre about the diagonal. -/
theorem eta_nu_fibre_reflect (e n : ℝ)
    (hp : (e, n) ∈ Set.range (fun C : Copula 2 => (eta C, blestNu C))) :
    (e, 2 * e - n) ∈ Set.range (fun C : Copula 2 => (eta C, blestNu C)) := by
  obtain ⟨C, hC⟩ := hp
  simp only [Prod.mk.injEq] at hC
  refine ⟨C.transpose, ?_⟩
  simp only [Prod.mk.injEq]
  rw [eta_transpose, nu_transpose, hC.1, hC.2]
  exact ⟨rfl, rfl⟩

/-- The `(η,ν)`-region is not symmetric about the origin. -/
theorem eta_nu_region_not_symmetric :
    ((-5 / 32 : ℝ), (7 / 128 : ℝ)) ∈ Set.range (fun C : Copula 2 => (eta C, blestNu C)) ∧
      ((5 / 32 : ℝ), (-7 / 128 : ℝ)) ∉ Set.range (fun C : Copula 2 => (eta C, blestNu C)) := by
  have hq := quarter_values
  refine ⟨⟨familyA quarter, ?_⟩, ?_⟩
  · show (eta (familyA quarter), blestNu (familyA quarter)) = _
    rw [hq.1, hq.2]
  rintro ⟨C, hC⟩
  simp only [Prod.mk.injEq] at hC
  obtain ⟨he, hn⟩ := hC
  have hlow : blestNu C - eta C = -27 / 128 := by
    rw [he, hn]
    norm_num
  have hC := asymmetry_lower_unique C hlow
  rw [hC, eta_transpose, hq.1] at he
  norm_num at he

/-! ## The bound `1/2` from the `(ρ,ν)`-region alone -/

theorem nu_transpose_half_bound (C : Copula 2) : |blestNu C - blestNu C.transpose| ≤ 1 / 2 := by
  have h1 := abs_le.mp (nu_rho_bound C)
  have h2 := abs_le.mp (nu_rho_bound C.transpose)
  rw [Copula.spearmanRho_transpose] at h2
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- `ν(C) - ρ(C)` and `ν(Cᵀ) - ρ(C)` cannot be extreme in opposite directions. -/
theorem no_opposite_extremes (C : Copula 2) :
    ¬(blestNu C - C.spearmanRho = 1 / 4 ∧ blestNu C.transpose - C.spearmanRho = -1 / 4) ∧
      ¬(blestNu C - C.spearmanRho = -1 / 4 ∧ blestNu C.transpose - C.spearmanRho = 1 / 4) := by
  have hb := abs_le.mp (nu_transpose_bound C)
  constructor <;> rintro ⟨h1, h2⟩ <;> linarith [hb.1, hb.2]

/-! ## Derivatives of `Υ` -/

theorem hasDerivAt_graphGap (e : ℝ) (he : -1 < e) :
    HasDerivAt graphGap (1 - 4 / 3 * (2 : ℝ) ^ (-1 / 3 : ℝ) * (1 + e) ^ (1 / 3 : ℝ)) e := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 e := (hasDerivAt_id e).const_add 1
  have h2 := h1.rpow_const (p := 4 / 3) (Or.inl (ne_of_gt (show (0 : ℝ) < 1 + e by linarith)))
  have h3 := h1.sub (h2.const_mul ((2 : ℝ) ^ (-1 / 3 : ℝ)))
  convert h3 using 1
  · funext x
    rfl
  · rw [show (4 / 3 : ℝ) - 1 = 1 / 3 by norm_num]
    ring

theorem etaGap_of_ge (e : ℝ) (he : -3 / 4 ≤ e) : etaGap e = graphGap e := by
  rw [etaGap, ite_eq_right (not_lt.mpr he)]

/-- The derivative of `Υ` on `[-3/4,1)`, one-sided at `-3/4`. -/
theorem hasDerivWithinAt_etaGap_graph (e : ℝ) (he : e ∈ Ico (-3 / 4 : ℝ) 1) :
    HasDerivWithinAt etaGap (1 - 4 / 3 * (2 : ℝ) ^ (-1 / 3 : ℝ) * (1 + e) ^ (1 / 3 : ℝ))
      (Ici (-3 / 4)) e :=
  (hasDerivAt_graphGap e (by linarith [he.1])).hasDerivWithinAt.congr
    (fun x hx => etaGap_of_ge x hx) (etaGap_of_ge e he.1)

theorem hasDerivAt_etaGap_graph (e : ℝ) (he : e ∈ Ioo (-3 / 4 : ℝ) 1) :
    HasDerivAt etaGap (1 - 4 / 3 * (2 : ℝ) ^ (-1 / 3 : ℝ) * (1 + e) ^ (1 / 3 : ℝ)) e := by
  apply (hasDerivAt_graphGap e (by linarith [he.1])).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds he.1] with x hx
  exact etaGap_of_ge x (le_of_lt hx)

theorem cubeRoot_factor (e : ℝ) (he : -1 ≤ e) :
    0 ≤ (2 : ℝ) ^ (-1 / 3 : ℝ) * (1 + e) ^ (1 / 3 : ℝ) ∧
      ((2 : ℝ) ^ (-1 / 3 : ℝ) * (1 + e) ^ (1 / 3 : ℝ)) ^ 3 = (1 + e) / 2 := by
  have hx : 0 ≤ 1 + e := by linarith
  refine ⟨mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hx _), ?_⟩
  rw [mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ (-1 / 3 : ℝ)) 3, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_natCast ((1 + e) ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hx]
  norm_num
  ring

/-- `Υ'(e) ∈ [-1/3, 1/3]` on the graph branch. -/
theorem graphGap_deriv_bounds (e : ℝ) (he : e ∈ Icc (-3 / 4 : ℝ) 1) :
    1 - 4 / 3 * (2 : ℝ) ^ (-1 / 3 : ℝ) * (1 + e) ^ (1 / 3 : ℝ) ∈ Icc (-1 / 3 : ℝ) (1 / 3) := by
  obtain ⟨hq0, hq⟩ := cubeRoot_factor e (by linarith [he.1])
  set q := (2 : ℝ) ^ (-1 / 3 : ℝ) * (1 + e) ^ (1 / 3 : ℝ) with hqdef
  have hlo : 1 / 2 ≤ q := by
    by_contra h
    push Not at h
    have := pow_lt_pow_left₀ h hq0 (by norm_num : (3 : ℕ) ≠ 0)
    norm_num at this
    linarith [he.1]
  have hhi : q ≤ 1 := by
    by_contra h
    push Not at h
    have := pow_lt_pow_left₀ h (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
    norm_num at this
    linarith [he.2]
  have hform : 1 - 4 / 3 * (2 : ℝ) ^ (-1 / 3 : ℝ) * (1 + e) ^ (1 / 3 : ℝ) = 1 - 4 / 3 * q := by
    rw [hqdef]
    ring
  rw [hform]
  constructor <;> linarith

/-- The inverse parameter `e ↦ a` of the randomized branch, as a real function. -/
def randomParam (e : ℝ) : ℝ := (randomEtaParameter e : ℝ)

theorem etaB_open (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1) : etaB a ∈ Ioo (-1 : ℝ) (-3 / 4) := by
  have hl := randomized_parameter_strictAnti ⟨ha.le, ha1.le⟩
    (show (1 : ℝ) ∈ Icc (1 / 2) 1 by norm_num) ha1
  have hu := randomized_parameter_strictAnti (show (1 / 2 : ℝ) ∈ Icc (1 / 2) 1 by norm_num)
    ⟨ha.le, ha1.le⟩ ha
  have h1 : etaB 1 = -1 := by norm_num [etaB]
  have h2 : etaB (1 / 2) = -3 / 4 := by norm_num [etaB]
  rw [h1] at hl
  rw [h2] at hu
  exact ⟨hl, hu⟩

theorem randomParam_etaB (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1) : randomParam (etaB a) = a := by
  unfold randomParam
  exact congrArg Subtype.val
    (randomEtaParameter_value ⟨a, by linarith, ha1.le⟩ ha.le)

theorem randomParam_spec (e : ℝ) (he : e ∈ Ioo (-1 : ℝ) (-3 / 4)) :
    randomParam e ∈ Ioo (1 / 2 : ℝ) 1 ∧ etaB (randomParam e) = e := by
  obtain ⟨a, ha, ha1, hav⟩ := randomized_parameter_exists_open e he
  have h : randomParam e = a := by
    rw [← hav]
    exact randomParam_etaB a ha ha1
  rw [h]
  exact ⟨⟨ha, ha1⟩, hav⟩

theorem randomParam_continuousAt (e : ℝ) (he : e ∈ Ioo (-1 : ℝ) (-3 / 4)) :
    ContinuousAt randomParam e := by
  have hmono : MonotoneOn (fun x => -randomParam x) (Ioo (-1 : ℝ) (-3 / 4)) := by
    intro x hx y hy hxy
    obtain ⟨hax, hvx⟩ := randomParam_spec x hx
    obtain ⟨hay, hvy⟩ := randomParam_spec y hy
    show -randomParam x ≤ -randomParam y
    by_contra h
    push Not at h
    have hlt := randomized_parameter_strictAnti ⟨hax.1.le, hax.2.le⟩ ⟨hay.1.le, hay.2.le⟩
      (show randomParam x < randomParam y by linarith)
    rw [hvx, hvy] at hlt
    linarith
  have himg : (fun x => -randomParam x) '' Ioo (-1 : ℝ) (-3 / 4) ∈ 𝓝 (-randomParam e) := by
    obtain ⟨ha, _⟩ := randomParam_spec e he
    apply mem_of_superset (Ioo_mem_nhds (show (-1 : ℝ) < -randomParam e by linarith [ha.2])
      (show -randomParam e < -1 / 2 by linarith [ha.1]))
    intro b hb
    refine ⟨etaB (-b), etaB_open (-b) (by linarith [hb.2]) (by linarith [hb.1]), ?_⟩
    show -randomParam (etaB (-b)) = b
    rw [randomParam_etaB (-b) (by linarith [hb.2]) (by linarith [hb.1])]
    ring
  have hc := continuousAt_of_monotoneOn_of_image_mem_nhds hmono (Ioo_mem_nhds he.1 he.2) himg
  have h2 : randomParam = fun x => -(-randomParam x) := by
    funext x
    ring
  rw [h2]
  exact hc.neg

theorem hasDerivAt_randomParam (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1) :
    HasDerivAt randomParam
      (-((1 - a) ^ 2 * (1 + a) * (3 * a ^ 2 + 2 * a + 1)) / (4 * a ^ 3))⁻¹ (etaB a) := by
  have he := etaB_open a ha ha1
  have hpa := randomParam_etaB a ha ha1
  have ha0 : 0 < a := by linarith
  have h1 : 0 < 1 - a := by linarith
  apply HasDerivAt.of_local_left_inverse (randomParam_continuousAt _ he)
  · rw [hpa]
    exact hasDerivAt_etaB a ha0.ne'
  · have hp : 0 < (1 - a) ^ 2 * (1 + a) * (3 * a ^ 2 + 2 * a + 1) / (4 * a ^ 3) := by
      apply div_pos _ (by positivity)
      exact mul_pos (mul_pos (pow_pos h1 2) (by linarith)) (by positivity)
    rw [neg_div]
    exact neg_ne_zero.mpr hp.ne'
  · filter_upwards [Ioo_mem_nhds he.1 he.2] with y hy
    exact (randomParam_spec y hy).2

/-- Along the parametric branch, `Υ'(e_a) = (3a-1)/(1+a)`. -/
theorem hasDerivAt_etaGap_param (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1) :
    HasDerivAt etaGap ((3 * a - 1) / (1 + a)) (etaB a) := by
  have he := etaB_open a ha ha1
  have hpa := randomParam_etaB a ha ha1
  have ha0 : a ≠ 0 := by linarith
  have h1 : (1 - a) ≠ 0 := by linarith
  have h2 : (1 + a) ≠ 0 := by linarith
  have h3 : (3 * a ^ 2 + 2 * a + 1) ≠ 0 := by positivity
  have hcomp := HasDerivAt.comp_of_eq (etaB a) (hasDerivAt_randomGap a ha0)
    (hasDerivAt_randomParam a ha ha1) hpa.symm
  have hval : -((1 - a) ^ 2 * (3 * a - 1) * (3 * a ^ 2 + 2 * a + 1)) / (4 * a ^ 3) *
      (-((1 - a) ^ 2 * (1 + a) * (3 * a ^ 2 + 2 * a + 1)) / (4 * a ^ 3))⁻¹ =
      (3 * a - 1) / (1 + a) := by
    field_simp
  rw [hval] at hcomp
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds he.1 he.2] with y hy
  rw [etaGap, ite_eq_left hy.2]
  rfl

theorem param_slope_bounds (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1) :
    (3 * a - 1) / (1 + a) ∈ Ioo (1 / 3 : ℝ) 1 := by
  have h2 : 0 < 1 + a := by linarith
  constructor
  · rw [lt_div_iff₀ h2]
    linarith
  · rw [div_lt_one h2]
    linarith

/-- Dividing the two `a`-derivatives gives the slope `(3a-1)/(1+a)`, as in the proof. -/
theorem param_slope_ratio (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1) :
    (-((1 - a) ^ 2 * (3 * a - 1) * (3 * a ^ 2 + 2 * a + 1)) / (4 * a ^ 3)) /
      (-((1 - a) ^ 2 * (1 + a) * (3 * a ^ 2 + 2 * a + 1)) / (4 * a ^ 3)) =
      (3 * a - 1) / (1 + a) := by
  have ha0 : a ≠ 0 := by linarith
  have h1 : (1 - a) ≠ 0 := by linarith
  have h2 : (1 + a) ≠ 0 := by linarith
  have h3 : (3 * a ^ 2 + 2 * a + 1) ≠ 0 := by positivity
  field_simp

/-! ## Numerical fibres in the discussion -/

theorem rho_zero_fibre :
    {n | ∃ C : Copula 2, C.spearmanRho = 0 ∧ blestNu C = n} = Icc (-1 / 4 : ℝ) (1 / 4) := by
  have hb : rhoBoundary 0 = 1 / 4 := by
    rw [rhoBoundary, ite_eq_left le_rfl]
    norm_num
  ext n
  simp only [Set.mem_ofPred_eq]
  rw [rho_fibre_complete, hb]
  norm_num

theorem nu_zero_fibre :
    {m | ∃ C : Copula 2, blestNu C = 0 ∧ blestNu C.transpose = m} =
      Icc (LambdaInv 0) (Lambda 0) :=
  nu_transpose_fibre_eq 0 (by norm_num)

theorem Lambda_zero_bounds : (375 / 1000 : ℝ) < Lambda 0 ∧ Lambda 0 < 385 / 1000 := by
  obtain ⟨hs0, hs⟩ := closed_root 0 (by norm_num)
  rw [Lambda_closed_branch 0 (by norm_num), lambdaClosed_root 0 (by norm_num)]
  set s := ((1 + (0 : ℝ)) / 2) ^ (1 / 4 : ℝ) with hsdef
  have h4 : s ^ 4 = 1 / 2 := by linarith
  have hlo : (8408 / 10000 : ℝ) < s := by
    by_contra h
    push Not at h
    have := pow_le_pow_left₀ hs0 h 4
    norm_num at this
    linarith
  have hhi : s < (841 / 1000 : ℝ) := by
    by_contra h
    push Not at h
    have := pow_le_pow_left₀ (by norm_num) h 4
    norm_num at this
    linarith
  have c1 : (8408 / 10000 : ℝ) ^ 3 < s ^ 3 :=
    pow_lt_pow_left₀ hlo (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
  have c2 : s ^ 3 < (841 / 1000 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hhi hs0 (by norm_num : (3 : ℕ) ≠ 0)
  norm_num at c1 c2
  constructor <;> linarith

theorem LambdaInv_zero_bounds :
    (-425 / 1000 : ℝ) < LambdaInv 0 ∧ LambdaInv 0 < -415 / 1000 := by
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hm := LambdaInv_mem 0 h0
  have hL := Lambda_LambdaInv 0 h0
  have key : ∀ t : ℝ, 0 ≤ t → -7 / 8 ≤ 2 * t ^ 4 - 1 →
      Lambda (2 * t ^ 4 - 1) = 4 * t ^ 3 - 2 * t ^ 4 - 1 := by
    intro t ht hn
    rw [Lambda_closed_branch _ hn, lambdaClosed_param t ht]
  have hn1 : (2 * (733 / 1000 : ℝ) ^ 4 - 1) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hn2 : (2 * (734 / 1000 : ℝ) ^ 4 - 1) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hL1 := key (733 / 1000) (by norm_num) (by norm_num)
  have hL2 := key (734 / 1000) (by norm_num) (by norm_num)
  constructor
  · have hlt : 2 * (733 / 1000 : ℝ) ^ 4 - 1 < LambdaInv 0 := by
      by_contra h
      push Not at h
      have hmono := Lambda_strictMonoOn.monotoneOn hm hn1 h
      rw [hL, hL1] at hmono
      norm_num at hmono
    have hc : (-425 / 1000 : ℝ) < 2 * (733 / 1000 : ℝ) ^ 4 - 1 := by norm_num
    linarith
  · have hlt : LambdaInv 0 < 2 * (734 / 1000 : ℝ) ^ 4 - 1 := by
      by_contra h
      push Not at h
      have hmono := Lambda_strictMonoOn.monotoneOn hn2 hm h
      rw [hL, hL2] at hmono
      norm_num at hmono
    have hc : 2 * (734 / 1000 : ℝ) ^ 4 - 1 < (-415 / 1000 : ℝ) := by norm_num
    linarith

/-- At `ν = 0`, the `νᵀ`-fibre is longer than the `ν`-fibre at `ρ = 0`. -/
theorem transposition_fibre_longer : (1 / 2 : ℝ) < Lambda 0 - LambdaInv 0 := by
  linarith [Lambda_zero_bounds.1, LambdaInv_zero_bounds.2]

/-! ## Remark on randomization and the by-product -/

theorem familyA_gap (w : I) :
    blestNu (familyA w) - eta (familyA w) = 2 * (w : ℝ) * (1 - (w : ℝ)) ^ 3 := by
  rw [nu_familyA, eta_familyA]
  ring

/-- For `w ∈ (1/2,1)`, `A_w` lies strictly below the upper boundary. -/
theorem familyA_not_extremal (w : I) (hw : 1 / 2 < (w : ℝ)) (hw1 : (w : ℝ) < 1) :
    eta (familyA w) ∈ Ioo (-1 : ℝ) (-3 / 4) ∧
      blestNu (familyA w) < eta (familyA w) + etaGap (eta (familyA w)) := by
  have h1 : 0 < 1 - (w : ℝ) := by linarith
  have heI : eta (familyA w) ∈ Ioo (-1 : ℝ) (-3 / 4) := by
    rw [eta_familyA]
    have c1 : 0 < (1 - (w : ℝ)) ^ 3 := pow_pos h1 3
    have c2 : (1 - (w : ℝ)) ^ 3 < (1 / 2) ^ 3 :=
      pow_lt_pow_left₀ (by linarith) h1.le (by norm_num : (3 : ℕ) ≠ 0)
    norm_num at c2
    constructor <;> linarith
  refine ⟨heI, ?_⟩
  have h := (eta_fibre_displayed _ _).mp ⟨familyA w, rfl, rfl⟩
  have hle := (abs_le.mp h.2).2
  refine lt_of_le_of_ne (by linarith) ?_
  intro heq
  rcases upper_extremizer_cases (familyA w) heq with ⟨v, hv, hA⟩ | ⟨a, ha, ha1, hB⟩ | hW
  · have hwv : w = v := eta_familyA_strictAnti.injective (congrArg eta hA)
    subst hwv
    linarith
  · have hg := familyA_graph_all w
    rw [hB] at hg
    exact familyB_not_first_graph a ha ha1 (graphRank w) (measurable_graphRank w) hg
  · have hv := congrArg blestNu hW
    rw [nu_familyA, blest_countermonotonic] at hv
    have hp : 0 < 2 * (1 + (w : ℝ)) * (1 - (w : ℝ)) ^ 3 :=
      mul_pos (by linarith [w.property.1]) (pow_pos h1 3)
    linarith

/-- In Lemma 4.1, `η(B_a) → -1` as `a → 1`. -/
theorem etaB_tendsto_one : Tendsto etaB (𝓝[<] 1) (𝓝 (-1)) := by
  have h := (hasDerivAt_etaB 1 one_ne_zero).continuousAt.tendsto
  have h1 : etaB 1 = -1 := by norm_num [etaB]
  rw [h1] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- The branch probabilities in the right panel of the extremizer figure, for `a = 3/4`. -/
theorem figure_values :
    etaB (3 / 4) = -2257 / 2304 ∧ 1 / (2 * (3 / 4 : ℝ)) = 2 / 3 ∧
      (2 * (3 / 4 : ℝ) - 1) / (2 * (3 / 4)) = 1 / 3 := by
  norm_num [etaB]

/-- The panels of the Spearman figure: `c = 1/4, 1/2, 3/4` give `ρ = 7/8, 0, -7/8`. -/
theorem rho_figure_values :
    (rhoFullFamily ⟨1 / 4, by norm_num⟩).spearmanRho = 7 / 8 ∧
      (rhoFullFamily ⟨1 / 2, by norm_num⟩).spearmanRho = 0 ∧
      (rhoFullFamily ⟨3 / 4, by norm_num⟩).spearmanRho = -7 / 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [(rhoFullFamily_values _).1] <;> norm_num

/-- The coefficient values printed above the panels of the two extremizer figures. -/
theorem figure_panel_values :
    ((rhoFullFamily ⟨1 / 4, by norm_num⟩).spearmanRho = 7 / 8 ∧
      blestNu (rhoFullFamily ⟨1 / 4, by norm_num⟩) = 61 / 64 ∧
      blestNu (rhoFullFamily ⟨1 / 4, by norm_num⟩).survivalCopula = 51 / 64) ∧
    ((rhoFullFamily ⟨1 / 2, by norm_num⟩).spearmanRho = 0 ∧
      blestNu (rhoFullFamily ⟨1 / 2, by norm_num⟩) = 1 / 4 ∧
      blestNu (rhoFullFamily ⟨1 / 2, by norm_num⟩).survivalCopula = -1 / 4) ∧
    ((rhoFullFamily ⟨3 / 4, by norm_num⟩).spearmanRho = -7 / 8 ∧
      blestNu (rhoFullFamily ⟨3 / 4, by norm_num⟩) = -51 / 64 ∧
      blestNu (rhoFullFamily ⟨3 / 4, by norm_num⟩).survivalCopula = -61 / 64) ∧
    (eta (familyA quarter) = -5 / 32 ∧ blestNu (familyA quarter) = 7 / 128 ∧
      blestNu (familyA quarter).transpose = -47 / 128) ∧
    (eta (familyA ⟨1 / 2, by norm_num⟩) = -3 / 4 ∧
      blestNu (familyA ⟨1 / 2, by norm_num⟩) = -5 / 8 ∧
      blestNu (familyA ⟨1 / 2, by norm_num⟩).transpose = -7 / 8) ∧
    (eta (familyB ⟨3 / 4, by norm_num⟩ (by norm_num)) = -2257 / 2304 ∧
      blestNu (familyB ⟨3 / 4, by norm_num⟩ (by norm_num)) = -185 / 192 ∧
      blestNu (familyB ⟨3 / 4, by norm_num⟩ (by norm_num)).transpose = -1147 / 1152) := by
  have hD (c : I) (r n : ℝ) (hr : (rhoFullFamily c).spearmanRho = r)
      (hn : blestNu (rhoFullFamily c) = n) :
      (rhoFullFamily c).spearmanRho = r ∧ blestNu (rhoFullFamily c) = n ∧
        blestNu (rhoFullFamily c).survivalCopula = 2 * r - n :=
    ⟨hr, hn, by rw [nu_survival, hr, hn]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hD ⟨1 / 4, by norm_num⟩ (7 / 8) (61 / 64)
      (by rw [(rhoFullFamily_values _).1]; norm_num)
      (by rw [(rhoFullFamily_values _).2]; norm_num)
    norm_num at h ⊢
    exact h
  · have h := hD ⟨1 / 2, by norm_num⟩ 0 (1 / 4)
      (by rw [(rhoFullFamily_values _).1]; norm_num)
      (by rw [(rhoFullFamily_values _).2]; norm_num)
    norm_num at h ⊢
    exact h
  · have h := hD ⟨3 / 4, by norm_num⟩ (-7 / 8) (-51 / 64)
      (by rw [(rhoFullFamily_values _).1]; norm_num)
      (by rw [(rhoFullFamily_values _).2]; norm_num)
    norm_num at h ⊢
    exact h
  · refine ⟨quarter_values.1, quarter_values.2, ?_⟩
    rw [nu_transpose_familyA]
    norm_num [quarter]
  · refine ⟨?_, ?_, ?_⟩
    · rw [eta_familyA]; norm_num
    · rw [nu_familyA]; norm_num
    · rw [nu_transpose_familyA]; norm_num
  · refine ⟨?_, ?_, ?_⟩
    · rw [eta_familyB]; norm_num [etaB]
    · rw [nu_familyB]; norm_num [nuB]
    · rw [nu_transpose_familyB]; norm_num [etaB, nuB]

theorem countermonotonic_transpose :
    Copula.countermonotonic.transpose = Copula.countermonotonic := by
  apply blest_min_unique
  · rw [← familyA_one, nu_transpose_familyA]
    norm_num
  · exact blest_countermonotonic

/-- The shuffle of `M` that is countermonotone on `[0,3/4]` and comonotone on `[3/4,1]`. -/
def shuffleQuarter : Copula 2 :=
  Copula.countermonotonic.ordinalSum (Copula.comonotonic 2) ⟨3 / 4, by norm_num⟩

theorem shuffleQuarter_values :
    shuffleQuarter.spearmanRho = 5 / 32 ∧ blestNu shuffleQuarter = -7 / 128 ∧
      blestNu shuffleQuarter.transpose = -7 / 128 := by
  have hr : shuffleQuarter.spearmanRho = 5 / 32 := by
    rw [shuffleQuarter, Copula.spearmanRho_ordinalSum, Copula.spearmanRho_countermonotonic,
      Copula.spearmanRho_comonotonic]
    norm_num
  have hn : blestNu shuffleQuarter = -7 / 128 := by
    rw [shuffleQuarter, blest_ordinalSum, blest_countermonotonic, blest_comonotonic,
      Copula.spearmanRho_countermonotonic]
    norm_num
  refine ⟨hr, hn, ?_⟩
  rw [shuffleQuarter, Copula.transpose_ordinalSum, countermonotonic_transpose,
    transpose_comonotonic_two]
  exact hn

/-- The unique maximizer of `ρ - η` is `A_(1/4)^⊥`, which is this shuffle of `M`. -/
theorem rho_eta_maximizer_shuffle : (familyA quarter).reflect {1} = shuffleQuarter := by
  symm
  apply rho_eta_upper_unique
  obtain ⟨hr, hn, ht⟩ := shuffleQuarter_values
  rw [hr, eta, hn, ht]
  norm_num

/-- The unique minimizer `(A_(1/4)ᵀ)^⊥` is the survival copula of the maximizer. -/
theorem rho_eta_minimizer_survival :
    (familyA quarter).transpose.reflect {1} = ((familyA quarter).reflect {1}).survivalCopula := by
  symm
  apply rho_eta_lower_unique
  rw [Copula.spearmanRho_survivalCopula, eta_survival, rho_eta_maximizer_shuffle]
  obtain ⟨hr, hn, ht⟩ := shuffleQuarter_values
  rw [hr, eta, hn, ht]
  norm_num

#assert_standard_axioms Papers.Rockel2026ExactBlest.dual_certificate
#assert_standard_axioms Papers.Rockel2026ExactBlest.dual_certificate_graph
#assert_standard_axioms Papers.Rockel2026ExactBlest.dual_certificate_reverse_graph
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_normalization
#assert_standard_axioms Papers.Rockel2026ExactBlest.rhoBoundary_reflect
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_lower_eq_survival_upper
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_lower_eq_transpose_upper
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_fibre_max_asymmetry
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_nu_region_neg
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_nu_fibre_reflect
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_nu_fibre_reflect
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_nu_region_not_symmetric
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_half_bound
#assert_standard_axioms Papers.Rockel2026ExactBlest.no_opposite_extremes
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_graphGap
#assert_standard_axioms Papers.Rockel2026ExactBlest.etaGap_of_ge
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivWithinAt_etaGap_graph
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_etaGap_graph
#assert_standard_axioms Papers.Rockel2026ExactBlest.cubeRoot_factor
#assert_standard_axioms Papers.Rockel2026ExactBlest.graphGap_deriv_bounds
#assert_standard_axioms Papers.Rockel2026ExactBlest.etaB_open
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomParam_etaB
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomParam_spec
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomParam_continuousAt
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_randomParam
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_etaGap_param
#assert_standard_axioms Papers.Rockel2026ExactBlest.param_slope_bounds
#assert_standard_axioms Papers.Rockel2026ExactBlest.param_slope_ratio
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_zero_fibre
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_zero_fibre
#assert_standard_axioms Papers.Rockel2026ExactBlest.Lambda_zero_bounds
#assert_standard_axioms Papers.Rockel2026ExactBlest.LambdaInv_zero_bounds
#assert_standard_axioms Papers.Rockel2026ExactBlest.transposition_fibre_longer
#assert_standard_axioms Papers.Rockel2026ExactBlest.familyA_gap
#assert_standard_axioms Papers.Rockel2026ExactBlest.familyA_not_extremal
#assert_standard_axioms Papers.Rockel2026ExactBlest.etaB_tendsto_one
#assert_standard_axioms Papers.Rockel2026ExactBlest.figure_values
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_figure_values
#assert_standard_axioms Papers.Rockel2026ExactBlest.figure_panel_values
#assert_standard_axioms Papers.Rockel2026ExactBlest.countermonotonic_transpose
#assert_standard_axioms Papers.Rockel2026ExactBlest.shuffleQuarter_values
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_eta_maximizer_shuffle
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_eta_minimizer_survival

end
end Papers.Rockel2026ExactBlest
