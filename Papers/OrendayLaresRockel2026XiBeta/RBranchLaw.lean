import Papers.OrendayLaresRockel2026XiBeta.RBranchBasic
import Copula.CDF.Extensionality

/-! # The law of `(U, V_b)` (Proposition 5.3, first statement)

`U ~ U(0,1)` and an independent fair coin `ε` (`Bool`); `V_b = U` if `U ∉ (b/2, 1 - b/2)` and
`V_b = (2U + b)/4 + ε (1 - b)/2` otherwise. We show that the law of `(U, V_b)` is the measure of
the copula `R_b`, so that `R_b` is the copula of `(U, V_b)`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal

namespace Papers.OrendayLaresRockel2026XiBeta

/-- The fair coin: `P(ε = 0) = P(ε = 1) = 1/2` (`false ↦ 0`, `true ↦ 1`). -/
noncomputable def bernoulliHalf : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac false + Measure.dirac true)

instance : IsProbabilityMeasure bernoulliHalf := by
  refine ⟨?_⟩
  simp [bernoulliHalf, ENNReal.inv_two_add_inv_two]

theorem integral_bernoulliHalf (f : Bool → ℝ) :
    ∫ e, f e ∂bernoulliHalf = (f false + f true) / 2 := by
  unfold bernoulliHalf
  rw [integral_smul_measure, integral_add_measure (Integrable.of_finite) (Integrable.of_finite),
    integral_dirac, integral_dirac]
  simp only [smul_eq_mul]
  norm_num
  ring

/-- The real-valued formula for `V_b` as a function of `(U, ε)`. -/
noncomputable def vbReal (b u : ℝ) (e : Bool) : ℝ :=
  if b / 2 < u ∧ u < 1 - b / 2 then (2 * u + b) / 4 + (if e then (1 - b) / 2 else 0) else u

theorem vbReal_mem {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (e : Bool) :
    vbReal b u e ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨hu0, hu1⟩ := hu
  unfold vbReal
  split_ifs with h1 h2 <;> first | exact ⟨hu0, hu1⟩ | (constructor <;> linarith [h1.1, h1.2])

/-- `V_b` as a point of the unit interval. -/
noncomputable def Vb (b : ℝ) (u : I) (e : Bool) : I :=
  Set.projIcc 0 1 zero_le_one (vbReal b u e)

theorem coe_Vb {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (u : I) (e : Bool) :
    ((Vb b u e : I) : ℝ) = vbReal b u e := by
  unfold Vb
  rw [Set.projIcc_of_mem zero_le_one (vbReal_mem hb u.2 e)]

theorem measurable_Vb (b : ℝ) : Measurable (fun p : I × Bool => Vb b p.1 p.2) := by
  refine measurable_from_prod_countable_left (fun e => ?_)
  unfold Vb vbReal
  refine (continuous_projIcc.measurable).comp ?_
  refine Measurable.ite ?_ ?_ ?_
  · exact (measurableSet_lt measurable_const measurable_subtype_coe).inter
      (measurableSet_lt measurable_subtype_coe measurable_const)
  · cases e <;> simp <;> fun_prop
  · fun_prop

/-- The random vector `(U, V_b)` on `I × Bool`. -/
noncomputable def Xb (b : ℝ) (p : I × Bool) : Fin 2 → I := ![p.1, Vb b p.1 p.2]

theorem measurable_Xb (b : ℝ) : Measurable (Xb b) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  fin_cases i
  · exact measurable_fst
  · exact measurable_Vb b

/-- The law of `(U, V_b)`. -/
noncomputable def lawVb (b : ℝ) : Measure (Fin 2 → I) :=
  (volume.prod bernoulliHalf).map (Xb b)

instance (b : ℝ) : IsProbabilityMeasure (lawVb b) := by
  unfold lawVb; infer_instance

theorem rightSection_B {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 ≤ t) :
    (rightSection b hb).B t = 1 / 2 + t - rbA b t := by
  unfold MedianSection.B
  rw [rightSection_A hb ht]
  rfl

/-- The kernel of `R_b` at `t ≠ 1 - b/2` is the law of `V_b` given `U = t`. -/
theorem kerR_rightSection {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) {t v : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hne : t ≠ 1 - b / 2) :
    (rightSection b hb).kerR v t =
      ((if vbReal b t false ≤ v then 1 else 0) + (if vbReal b t true ≤ v then 1 else 0)) / 2 := by
  have hb' := hb
  obtain ⟨hb0, hb1⟩ := hb'
  obtain ⟨ht0, ht1⟩ := ht
  have hp : (rightSection b hb).p t = rightSlope b t := rfl
  unfold MedianSection.kerR
  rw [hp, rightSection_A hb ht0, rightSection_B hb ht0]
  unfold rightSlope vbReal rbA
  rcases lt_or_ge (b / 2) t with h1 | h1
  · rcases lt_or_gt_of_ne hne with h2 | h2
    · have e1 : ¬ t ≤ b / 2 := not_le.2 h1
      have e2 : t ≤ 1 - b / 2 := h2.le
      have hc : b / 2 < t ∧ t < 1 - b / 2 := ⟨h1, h2⟩
      have m1 : min t ((2 * t + b) / 4) = (2 * t + b) / 4 := min_eq_right (by linarith)
      have m2 : min ((2 * t + b) / 4) (1 / 2) = (2 * t + b) / 4 := min_eq_left (by linarith)
      have m3 : 1 / 2 + t - (2 * t + b) / 4 = (2 * t + b) / 4 + (1 - b) / 2 := by ring
      simp only [e1, e2, hc, m1, m2, m3, ↓reduceIte, Bool.false_eq_true, add_zero, and_self]
      ring
    · have e1 : ¬ t ≤ b / 2 := not_le.2 h1
      have e2 : ¬ t ≤ 1 - b / 2 := not_le.2 h2
      have hc : ¬ (b / 2 < t ∧ t < 1 - b / 2) := fun h => absurd h.2 (not_lt.2 h2.le)
      have m1 : min t ((2 * t + b) / 4) = (2 * t + b) / 4 := min_eq_right (by linarith)
      have m2 : min ((2 * t + b) / 4) (1 / 2) = 1 / 2 := min_eq_right (by linarith)
      have m3 : 1 / 2 + t - 1 / 2 = t := by ring
      simp only [e1, e2, hc, m1, m2, m3, ↓reduceIte]
      ring
  · have e1 : t ≤ b / 2 := h1
    have hc : ¬ (b / 2 < t ∧ t < 1 - b / 2) := fun h => absurd h.1 (not_lt.2 h1)
    have m1 : min t ((2 * t + b) / 4) = t := min_eq_left (by linarith)
    have m2 : min t (1 / 2) = t := min_eq_left (by linarith)
    have m3 : 1 / 2 + t - t = 1 / 2 := by ring
    simp only [e1, hc, m1, m2, m3, ↓reduceIte]
    ring

theorem volume_coe_eq_null (c : ℝ) : (volume : Measure I) {t : I | (t : ℝ) = c} = 0 :=
  Set.Subsingleton.measure_zero (fun _ hx _ hy => Subtype.ext (hx.trans hy.symm)) _

/-- The distribution function of the law of `(U, V_b)` is that of `R_b`. -/
theorem cdf_lawVb {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (u v : I) :
    (lawVb b).real (Iic ![u, v]) = (Rb b hb).cdf ![u, v] := by
  set S : Set (I × Bool) := {p | p.1 ≤ u ∧ Vb b p.1 p.2 ≤ v} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le (f := fun p : I × Bool => Vb b p.1 p.2) (g := fun _ => v)
        (measurable_Vb b) measurable_const)
  have hpre : Xb b ⁻¹' Iic ![u, v] = S := by
    ext p
    simp [Xb, Pi.le_def, Fin.forall_fin_two, hS]
  have hint : Integrable (S.indicator (1 : I × Bool → ℝ)) (volume.prod bernoulliHalf) :=
    (integrable_const (1 : ℝ)).indicator hSm
  unfold lawVb
  rw [map_measureReal_apply (measurable_Xb b) measurableSet_Iic, hpre, ← integral_indicator_one hSm,
    integral_prod _ hint]
  simp_rw [integral_bernoulliHalf]
  change _ = (rightSection b hb).completion.cdf ![u, v]
  rw [MedianSection.cdf_completion_eq_integral, ← integral_indicator measurableSet_Iic]
  have hnull : ∀ᵐ t : I ∂volume, (t : ℝ) ≠ 1 - b / 2 := by
    rw [ae_iff]
    simpa using volume_coe_eq_null (1 - b / 2)
  refine integral_congr_ae ?_
  filter_upwards [hnull] with t ht
  have hk := kerR_rightSection hb (v := (v : ℝ)) t.2 ht
  have h0 : (Vb b t false ≤ v) ↔ vbReal b t false ≤ (v : ℝ) := by
    rw [← Subtype.coe_le_coe, coe_Vb hb]
  have h1 : (Vb b t true ≤ v) ↔ vbReal b t true ≤ (v : ℝ) := by
    rw [← Subtype.coe_le_coe, coe_Vb hb]
  by_cases htu : t ≤ u
  · simp only [Set.indicator_apply, hS, Set.mem_ofPred_eq, htu, true_and, Set.mem_Iic, Pi.one_apply,
      h0, h1]
    change _ = (rightSection b hb).kerR (v : ℝ) (t : ℝ)
    rw [hk]
  · simp [hS, htu]

/-- Two probability measures on the unit square with equal distribution functions coincide. -/
theorem measure_eq_of_real_Iic_eq (μ ν : Measure (Fin 2 → I)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : ∀ w, μ.real (Iic w) = ν.real (Iic w)) : μ = ν := by
  classical
  let S : Fin 2 → Set (Set I) := fun _ => range Iic
  have hgen (i : Fin 2) : MeasurableSpace.generateFrom (S i) = (inferInstance : MeasurableSpace I) :=
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic I)).symm
  have hspan (i : Fin 2) : IsCountablySpanning (S i) := by
    refine ⟨fun _ : ℕ => univ, fun _ => ?_, ?_⟩
    · refine ⟨1, ?_⟩
      ext x
      simp [unitInterval.le_one']
    · apply Subset.antisymm (subset_univ _)
      intro x _
      exact mem_iUnion.mpr ⟨0, mem_univ x⟩
  refine ext_of_generate_finite _ (generateFrom_eq_pi hgen hspan).symm
    (IsPiSystem.pi fun _ => isPiSystem_Iic) ?_ (by simp)
  rintro _ ⟨s, hs, rfl⟩
  have hs' : ∀ i, ∃ u : I, Iic u = s i := fun i => hs i (mem_univ i)
  choose u hu using hs'
  have hbox : Set.pi univ s = Iic u := by
    ext x
    simp only [mem_univ_pi, ← hu, mem_Iic, Pi.le_def]
  rw [hbox]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (h u)

/-- **Proposition 5.3, first statement**: the measure of `R_b` is the law of `(U, V_b)`. -/
theorem Rb_toMeasure_eq_lawVb {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    (Rb b hb).toMeasure = lawVb b := by
  apply measure_eq_of_real_Iic_eq
  intro w
  have hw : ![w 0, w 1] = w := by ext i; fin_cases i <;> rfl
  have h := cdf_lawVb hb (w 0) (w 1)
  rw [hw] at h
  exact h.symm

end Papers.OrendayLaresRockel2026XiBeta
