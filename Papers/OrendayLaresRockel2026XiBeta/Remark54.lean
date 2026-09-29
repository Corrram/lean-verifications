import Papers.OrendayLaresRockel2026XiBeta.SIRegion
import Mathlib.MeasureTheory.Function.Floor

/-! # Remark 5.4, the introduction's claims for SI copulas and the caption of Figure 1

* (a) At `β = 0` the SI region is the segment `0 ≤ ξ ≤ 1/4`, whose upper endpoint is attained by
  `R_0`, the copula of `(U, (U + ε)/2)`; `R_0ᵀ` is completely dependent (`U = 2V_0 - ε`,
  `ε = ⌊2 V_0⌋`), so `ξ(R_0ᵀ) = 1`, while `R_0` is SI and `R_0ᵀ` is not.
* (b) `ξ(R_b) ≤ τ(R_b) ≤ ρ(R_b)` for `b ∈ [0,1]`.
* Introduction: for SI copulas `ξ > 1/4` forces `β > 0`, `β ≥ 1 - 2√((1-ξ)/3)`, and `β = 0` is
  compatible with every `ξ ∈ [0, 1/4]`.
* Figure 1: the SI region lies between the cubic `ξ = β³/2` and the curve
  `ξ = 1 - (3/4)(1-β)²`, degenerates to `[0, 1/4]` at `β = 0`, and the dots `Π, R_0, L_1, M`
  are attained by SI copulas.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

/-! ### Remark 5.4 (a) -/

/-- The fibre of the SI region over `β = 0` is the segment `0 ≤ ξ ≤ 1/4`. -/
theorem siRegion_fibre_beta_zero (x : ℝ) : (x, (0 : ℝ)) ∈ siRegion ↔ x ∈ Icc (0 : ℝ) (1 / 4) := by
  constructor
  · rintro ⟨hx, -, h1, h2⟩
    constructor
    · exact hx.1
    · nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, by linarith⟩, ⟨le_refl _, zero_le_one⟩, ?_, ?_⟩ <;> simp <;> linarith

/-- Remark 5.4 (a): at `β = 0` the SI region is exactly the segment `0 ≤ ξ ≤ 1/4`. -/
theorem xiBetaRegion_classSI_fibre_beta_zero (x : ℝ) :
    (x, (0 : ℝ)) ∈ xiBetaRegion classSI ↔ x ∈ Icc (0 : ℝ) (1 / 4) := by
  rw [theorem_1_2_region.1, siRegion_fibre_beta_zero]

/-- Remark 5.4 (a): the upper endpoint `(1/4, 0)` is attained by `R_0`, which is SI. -/
theorem R0_upper_endpoint :
    (Rb 0 zero_mem_Icc01).chatterjeeXi = 1 / 4 ∧ (Rb 0 zero_mem_Icc01).blomqvistBeta = 0 ∧
      (Rb 0 zero_mem_Icc01).IsSI := by
  refine ⟨?_, Rb_beta _, Rb_isSI _⟩
  rw [xi_Rb]; norm_num

/-- Remark 5.4 (a): `R_0` is the copula of `(U, (U + ε)/2)`: almost surely `V_0 = (U + ε)/2`
for the coupling `(U, ε)` of Proposition 5.3. -/
theorem V0_ae_eq :
    ∀ᵐ ω ∂(probVb : ProbabilityMeasure (I × Bool)).toMeasure,
      ((Vb 0 ω.1 ω.2 : I) : ℝ) = ((ω.1 : ℝ) + (if ω.2 then 1 else 0)) / 2 := by
  have hae : ∀ᵐ u : I ∂(volume : Measure I), 0 < (u : ℝ) ∧ (u : ℝ) < 1 := by
    rw [ae_iff]
    have : {u : I | ¬ (0 < (u : ℝ) ∧ (u : ℝ) < 1)} ⊆ {u : I | (u : ℝ) = 0} ∪ {u : I | (u : ℝ) = 1} := by
      intro u hu
      simp only [mem_ofPred_eq, not_and_or, not_lt] at hu
      rcases hu with h | h
      · exact Or.inl (le_antisymm h u.2.1)
      · exact Or.inr (le_antisymm u.2.2 h)
    exact measure_mono_null this (measure_union_null (volume_coe_eq_null 0) (volume_coe_eq_null 1))
  have := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure I)) (ν := bernoulliHalf)).ae hae
  filter_upwards [this] with ω hω
  rw [coe_Vb zero_mem_Icc01]
  unfold vbReal
  have hc : (0 : ℝ) / 2 < (ω.1 : ℝ) ∧ (ω.1 : ℝ) < 1 - 0 / 2 := by
    constructor <;> [simpa using hω.1; simpa using hω.2]
  simp only [hc, and_self, ↓reduceIte]
  cases ω.2 <;> simp <;> ring

/-- Remark 5.4 (a): `U = 2V_0 - ε` with `ε = ⌊2V_0⌋` almost surely. -/
theorem V0_floor_ae :
    ∀ᵐ ω ∂(probVb : ProbabilityMeasure (I × Bool)).toMeasure,
      (⌊2 * ((Vb 0 ω.1 ω.2 : I) : ℝ)⌋ : ℝ) = (if ω.2 then 1 else 0) ∧
      (ω.1 : ℝ) = 2 * ((Vb 0 ω.1 ω.2 : I) : ℝ) - ⌊2 * ((Vb 0 ω.1 ω.2 : I) : ℝ)⌋ := by
  have hae : ∀ᵐ u : I ∂(volume : Measure I), (u : ℝ) < 1 := by
    rw [ae_iff]
    have : {u : I | ¬ ((u : ℝ) < 1)} ⊆ {u : I | (u : ℝ) = 1} := by
      intro u hu
      simp only [mem_ofPred_eq, not_lt] at hu
      exact le_antisymm u.2.2 hu
    exact measure_mono_null this (volume_coe_eq_null 1)
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure I)) (ν := bernoulliHalf)).ae hae
  filter_upwards [V0_ae_eq, h1] with ω hv hu
  have hu0 := ω.1.2.1
  have hfl : (⌊2 * ((Vb 0 ω.1 ω.2 : I) : ℝ)⌋ : ℝ) = (if ω.2 then 1 else 0) := by
    rw [hv]
    have h2 : (2 : ℝ) * (((ω.1 : ℝ) + (if ω.2 then 1 else 0)) / 2) =
        (ω.1 : ℝ) + (if ω.2 then 1 else 0) := by ring
    rw [h2]
    cases ω.2
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      have : ⌊(ω.1 : ℝ)⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨hu0, hu⟩
      simp [this]
    · simp only [↓reduceIte]
      have : ⌊(ω.1 : ℝ) + 1⌋ = 1 := by
        rw [Int.floor_add_one]
        have : ⌊(ω.1 : ℝ)⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨hu0, hu⟩
        simp [this]
      simp [this]
  refine ⟨hfl, ?_⟩
  rw [hfl, hv]
  ring

/-- The doubling map `v ↦ 2v - ⌊2v⌋` (fractional part of `2v`) on the unit interval. -/
noncomputable def doubling (v : I) : I :=
  ⟨Int.fract (2 * (v : ℝ)), Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

theorem measurable_doubling : Measurable doubling :=
  Measurable.subtype_mk (Measurable.fract (by fun_prop))

/-- Remark 5.4 (a): `R_0ᵀ` lives on the graph of the doubling map, i.e. it is completely
dependent: `U = 2V_0 - ⌊2V_0⌋` almost surely. -/
theorem R0_transpose_ae_graph :
    ∀ᵐ x ∂(Rb 0 zero_mem_Icc01).transpose.toMeasure, x 1 = doubling (x 0) := by
  have hm : MeasurableSet {x : Fin 2 → I | x 1 = doubling (x 0)} :=
    measurableSet_eq_fun (measurable_pi_apply 1) (measurable_doubling.comp (measurable_pi_apply 0))
  unfold Copula.transpose
  rw [Copula.toMeasure_reindex, ae_map_iff (f := fun (x : Fin 2 → I) (i : Fin 2) => x (![1, 0] i))
      (Measurable.of_eval fun i => measurable_pi_apply (![1, 0] i)).aemeasurable hm,
    Rb_toMeasure_eq_lawVb, lawVb]
  have hm' : MeasurableSet {x : Fin 2 → I |
      (fun i => x (![1, 0] i)) ∈ {x : Fin 2 → I | x 1 = doubling (x 0)}} :=
    (Measurable.of_eval fun i => measurable_pi_apply (![1, 0] i)) hm
  refine (ae_map_iff (measurable_Xb 0).aemeasurable hm').2 ?_
  filter_upwards [V0_floor_ae] with ω h
  change ω.1 = doubling (Vb 0 ω.1 ω.2)
  apply Subtype.ext
  change (ω.1 : ℝ) = Int.fract (2 * ((Vb 0 ω.1 ω.2 : I) : ℝ))
  rw [Int.fract, h.2]

/-- Remark 5.4 (a): `R_0ᵀ` is completely dependent, so `ξ(R_0ᵀ) = 1`. -/
theorem xi_R0_transpose : (Rb 0 zero_mem_Icc01).transpose.chatterjeeXi = 1 :=
  Copula.chatterjeeXi_eq_one_of_function _ measurable_doubling R0_transpose_ae_graph

/-- Remark 5.4 (a): `R_0` is SI while `R_0ᵀ` is not; `ξ(R_0) = 1/4 < 1 = ξ(R_0ᵀ)`. -/
theorem R0_SI_transpose_not_SI :
    (Rb 0 zero_mem_Icc01).IsSI ∧ ¬ (Rb 0 zero_mem_Icc01).transpose.IsSI ∧
      (Rb 0 zero_mem_Icc01).chatterjeeXi = 1 / 4 ∧ (Rb 0 zero_mem_Icc01).transpose.chatterjeeXi = 1 :=
  ⟨Rb_isSI _, Rb_transpose_not_isSI _ (by norm_num), R0_upper_endpoint.1, xi_R0_transpose⟩

/-! ### Remark 5.4 (b) -/

/-- Remark 5.4 (b): `ξ(R_b) ≤ τ(R_b) ≤ ρ(R_b)` for all `b ∈ [0,1]`. -/
theorem xi_le_tau_le_rho_Rb (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    (Rb b hb).chatterjeeXi ≤ (Rb b hb).kendallTau ∧ (Rb b hb).kendallTau ≤ (Rb b hb).spearmanRho := by
  obtain ⟨h1, h2, h3, h4⟩ := proposition_5_3_iii_iv b hb
  obtain ⟨hb0, hb1⟩ := hb
  rw [h2, h3, h4]
  have hc0 : 0 ≤ 1 - b := by linarith
  have hc1 : 1 - b ≤ 1 := by linarith
  constructor
  · nlinarith [sq_nonneg (1 - b)]
  · nlinarith [mul_nonneg (sq_nonneg (1 - b)) hc0, mul_nonneg (sq_nonneg (1 - b)) (sub_nonneg.2 hc1)]

/-! ### Claims of the introduction for SI copulas -/

/-- Introduction: for SI copulas, `ξ > 1/4` forces `β > 0`. -/
theorem si_xi_gt_quarter_beta_pos (C : Copula 2) (hC : C.IsSI) (h : 1 / 4 < C.chatterjeeXi) :
    0 < C.blomqvistBeta :=
  xi_gt_quarter_beta_pos (si_beta_mem_Icc C hC).1 (theorem_1_2_inequality_alt C hC) h

/-- Introduction: `β = 0` is compatible with every `ξ ∈ [0, 1/4]` under stochastic
increasingness (even with radial symmetry). -/
theorem si_beta_zero_compatible (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (1 / 4)) :
    ∃ C : Copula 2, C.IsSI ∧ C.IsRadiallySymmetric ∧ C.chatterjeeXi = x ∧ C.blomqvistBeta = 0 := by
  have h : (x, (0 : ℝ)) ∈ xiBetaRegion (classSI ∩ classRS) := by
    rw [theorem_1_2_region.2]
    exact (siRegion_fibre_beta_zero x).2 hx
  obtain ⟨C, ⟨hC1, hC2⟩, h1, h2⟩ := h
  exact ⟨C, hC1, hC2, h1, h2⟩

/-- Introduction: for SI copulas with `β = 0`, necessarily `ξ ≤ 1/4`. -/
theorem si_beta_zero_xi_le (C : Copula 2) (hC : C.IsSI) (h : C.blomqvistBeta = 0) :
    C.chatterjeeXi ≤ 1 / 4 := by
  have := xi_le_of_isSI C hC
  rw [h] at this
  linarith

/-! ### Figure 1: the SI region -/

/-- The SI region is the set between the cubic `ξ = β³/2` and the curve `ξ = 1 - (3/4)(1-β)²`. -/
theorem siRegion_iff (x y : ℝ) :
    (x, y) ∈ siRegion ↔ y ∈ Icc (0 : ℝ) 1 ∧ y ^ 3 / 2 ≤ x ∧ x ≤ 1 - 3 / 4 * (1 - y) ^ 2 := by
  constructor
  · rintro ⟨-, hy, h1, h2⟩
    exact ⟨hy, by linarith, by linarith⟩
  · rintro ⟨hy, h1, h2⟩
    obtain ⟨hy0, hy1⟩ := hy
    refine ⟨⟨?_, ?_⟩, ⟨hy0, hy1⟩, by linarith, by linarith⟩
    · have : 0 ≤ y ^ 3 := by positivity
      linarith
    · nlinarith [sq_nonneg (1 - y)]

/-- Figure 1: the boundary curves of the SI region are attained by `L_b` (cubic) and `R_b`
(dash-dotted curve), both SI and radially symmetric. -/
theorem figure1_si_boundary (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) (hb' : b ∈ Icc (-1 : ℝ) 1) :
    ((leftBoundary b hb').IsSI ∧ (leftBoundary b hb').chatterjeeXi = b ^ 3 / 2 ∧
      (leftBoundary b hb').blomqvistBeta = b) ∧
    ((Rb b hb).IsSI ∧ (Rb b hb).chatterjeeXi = 1 - 3 / 4 * (1 - b) ^ 2 ∧
      (Rb b hb).blomqvistBeta = b) := by
  refine ⟨⟨leftBoundary_isSI _ _ hb.1, ?_, leftBoundary_beta _ _⟩, Rb_isSI hb, xi_Rb b hb, Rb_beta hb⟩
  rw [leftBoundary_xi, abs_of_nonneg hb.1]

/-- Figure 1: the dots `Π, R_0, L_1, M`, all attained by SI copulas. -/
theorem figure1_si_dots :
    ((Copula.independence 2).IsSI ∧ (Copula.independence 2).chatterjeeXi = 0 ∧
      (Copula.independence 2).blomqvistBeta = 0) ∧
    ((Rb 0 zero_mem_Icc01).IsSI ∧ (Rb 0 zero_mem_Icc01).chatterjeeXi = 1 / 4 ∧
      (Rb 0 zero_mem_Icc01).blomqvistBeta = 0) ∧
    ((leftBoundary 1 (by norm_num)).IsSI ∧ (leftBoundary 1 (by norm_num)).chatterjeeXi = 1 / 2 ∧
      (leftBoundary 1 (by norm_num)).blomqvistBeta = 1) ∧
    ((Copula.comonotonic 2).IsSI ∧ (Copula.comonotonic 2).chatterjeeXi = 1 ∧
      (Copula.comonotonic 2).blomqvistBeta = 1) := by
  refine ⟨⟨Copula.isSI_independence, Copula.chatterjeeXi_independence, by simp⟩,
    ⟨R0_upper_endpoint.2.2, R0_upper_endpoint.1, R0_upper_endpoint.2.1⟩,
    ⟨leftBoundary_isSI _ _ (by norm_num), ?_, leftBoundary_beta _ _⟩,
    ⟨Copula.isSI_comonotonic, Copula.chatterjeeXi_comonotonic, Copula.blomqvistBeta_comonotonic⟩⟩
  rw [leftBoundary_xi]; norm_num

/-- Figure 1: the SD region (dark orange) has right boundary attained by the mirror images
`Ř_b` of `R_b`, which are SD with `ξ(Ř_b) = ξ(R_b)`, `β(Ř_b) = -b`. -/
theorem figure1_sd_boundary (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    ((Rb b hb).reflect {1}).IsSD ∧ ((Rb b hb).reflect {1}).chatterjeeXi = 1 - 3 / 4 * (1 - b) ^ 2 ∧
      ((Rb b hb).reflect {1}).blomqvistBeta = -b := by
  refine ⟨?_, ?_, ?_⟩
  · have : (Rb b hb).reflect {1} ∈ checkClass classSI := ⟨_, Rb_isSI hb, rfl⟩
    rw [checkClass_si] at this
    exact this
  · rw [xi_check, xi_Rb b hb]
  · rw [beta_check, Rb_beta hb]

end Papers.OrendayLaresRockel2026XiBeta
