import Papers.OrendayLaresRockel2026XiBeta.RBranchSingular
import Copula.Rank.Integration

/-! # Kendall's `τ` and Spearman's `ρ` of `R_b` (Proposition 5.3 (iv))

`τ(R_b) = 1 - (1/2)(1-b)²` and `ρ(R_b) = 1 - (1/2)(1-b)³`, computed from the representation of
`R_b` as the law of `(U, V_b)`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal

namespace Papers.OrendayLaresRockel2026XiBeta

/-- Integrals against `R_b` reduce to a one-dimensional integral over `U` of the average over the
two coin outcomes. -/
theorem integral_Rb {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) {g : (Fin 2 → I) → ℝ} (hg : Continuous g) :
    ∫ x, g x ∂(Rb b hb).toMeasure =
      ∫ t : I, (g (Xb b (t, false)) + g (Xb b (t, true))) / 2 := by
  have hi : Integrable g (lawVb b) := Copula.integrable_continuous_cube _ hg
  have hi2 : Integrable (g ∘ Xb b) (volume.prod bernoulliHalf) :=
    (integrable_map_measure hg.aestronglyMeasurable (measurable_Xb b).aemeasurable).1 hi
  rw [Rb_toMeasure_eq_lawVb hb]
  unfold lawVb
  rw [integral_map (measurable_Xb b).aemeasurable hg.aestronglyMeasurable]
  have h := integral_prod (g ∘ Xb b) hi2
  simp only [Function.comp_apply] at h
  rw [h]
  simp_rw [integral_bernoulliHalf]

theorem integral_unit_add_Ioo (f1 h : ℝ → ℝ) (hf1 : Continuous f1) (hh : Continuous h)
    {s e : ℝ} (hs0 : 0 ≤ s) (hse : s ≤ e) (he1 : e ≤ 1) :
    (∫ t : I, (f1 t + (Ioo s e).indicator h t)) =
      (∫ x in (0 : ℝ)..1, f1 x) + ∫ x in s..e, h x := by
  rw [Copula.integral_unitInterval (fun t => f1 t + (Ioo s e).indicator h t)]
  have hInt : IntervalIntegrable ((Ioo s e).indicator h) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (hh.integrableOn_Icc.mono_set Ioc_subset_Icc_self).indicator measurableSet_Ioo
  rw [intervalIntegral.integral_add (hf1.intervalIntegrable _ _) hInt]
  congr 1
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le hse,
    integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
  have hs : Ioo s e ∩ Ioc (0 : ℝ) 1 = Ioo s e := by
    apply Set.inter_eq_left.2
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [hs, integral_Ioc_eq_integral_Ioo]

theorem integral_quad (A B D l r : ℝ) :
    (∫ x in l..r, (A * x ^ 2 + B * x + D)) =
      A * (r ^ 3 - l ^ 3) / 3 + B * (r ^ 2 - l ^ 2) / 2 + D * (r - l) := by
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul A (fun x : ℝ => x ^ 2),
      intervalIntegral.integral_const_mul B (fun x : ℝ => x), integral_pow, integral_id,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  · exact (by fun_prop : Continuous fun x : ℝ => A * x ^ 2).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun x : ℝ => B * x).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun x : ℝ => A * x ^ 2 + B * x).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun _ : ℝ => D).intervalIntegrable _ _

/-- On the support, `R_b(t, V_b) = t` outside `(b/2, 1 - b/2)`. -/
theorem Rb_cdf_Xb_outside {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (t : I) (e : Bool)
    (hc : ¬ (b / 2 < (t : ℝ) ∧ (t : ℝ) < 1 - b / 2)) :
    (Rb b hb).cdf (Xb b (t, e)) = t := by
  have hv : ((Vb b t e : I) : ℝ) = t := by
    rw [coe_Vb hb]; unfold vbReal; simp only [hc, ↓reduceIte]
  have hx : Xb b (t, e) = ![t, Vb b t e] := rfl
  obtain ⟨hb0, hb1⟩ := hb
  by_cases h1 : (t : ℝ) ≤ b / 2
  · rw [hx, Rb_cdf_of_le_half ⟨hb0, hb1⟩ t _ (by rw [hv]; linarith), hv]
    unfold rbA
    simp only [min_def]
    split_ifs <;> linarith [t.2.1, t.2.2]
  · have h2 : 1 - b / 2 ≤ (t : ℝ) := by
      by_contra h
      exact hc ⟨not_le.1 h1, not_le.1 h⟩
    rw [hx, Rb_cdf_of_half_le ⟨hb0, hb1⟩ t _ (by rw [hv]; linarith), hv]
    unfold rbA
    simp only [min_def]
    split_ifs <;> linarith [t.2.1, t.2.2]

/-- On the support, in the middle block: `R_b(t, A_b(t)) = A_b(t)` and `R_b(t, B_b(t)) = t`. -/
theorem Rb_cdf_Xb_mid {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (t : I)
    (hc : b / 2 < (t : ℝ) ∧ (t : ℝ) < 1 - b / 2) :
    (Rb b hb).cdf (Xb b (t, false)) = (2 * (t : ℝ) + b) / 4 ∧
      (Rb b hb).cdf (Xb b (t, true)) = t := by
  have hv0 : ((Vb b t false : I) : ℝ) = (2 * (t : ℝ) + b) / 4 := by
    rw [coe_Vb hb]; unfold vbReal; simp only [hc, and_self, ↓reduceIte, Bool.false_eq_true, add_zero]
  have hv1 : ((Vb b t true : I) : ℝ) = (2 * (t : ℝ) + b) / 4 + (1 - b) / 2 := by
    rw [coe_Vb hb]; unfold vbReal; simp only [hc, and_self, ↓reduceIte]
  have hx0 : Xb b (t, false) = ![t, Vb b t false] := rfl
  have hx1 : Xb b (t, true) = ![t, Vb b t true] := rfl
  obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  constructor
  · rw [hx0, Rb_cdf_of_le_half ⟨hb0, hb1⟩ t _ (by rw [hv0]; linarith), hv0]
    unfold rbA
    simp only [min_def]
    split_ifs <;> linarith [t.2.1, t.2.2]
  · rw [hx1, Rb_cdf_of_half_le ⟨hb0, hb1⟩ t _ (by rw [hv1]; linarith), hv1]
    unfold rbA
    simp only [min_def]
    split_ifs <;> linarith [t.2.1, t.2.2]

/-- **Proposition 5.3 (iv)**: `τ(R_b) = 1 - (1/2)(1 - b)²`. -/
theorem kendallTau_Rb {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    (Rb b hb).kendallTau = 1 - 1 / 2 * (1 - b) ^ 2 := by
  obtain ⟨hb0, hb1⟩ := hb
  have hb' : b ∈ Icc (0 : ℝ) 1 := ⟨hb0, hb1⟩
  unfold Copula.kendallTau
  rw [integral_Rb hb' (Rb b hb').continuous_cdf]
  have hpt : ∀ t : I, ((Rb b hb').cdf (Xb b (t, false)) + (Rb b hb').cdf (Xb b (t, true))) / 2 =
      (t : ℝ) + (Ioo (b / 2) (1 - b / 2)).indicator (fun x : ℝ => (b - 2 * x) / 8) (t : ℝ) := by
    intro t
    by_cases hc : b / 2 < (t : ℝ) ∧ (t : ℝ) < 1 - b / 2
    · obtain ⟨h0, h1⟩ := Rb_cdf_Xb_mid hb' t hc
      rw [h0, h1, Set.indicator_of_mem (show (t : ℝ) ∈ Ioo (b / 2) (1 - b / 2) from hc)]
      ring
    · rw [Rb_cdf_Xb_outside hb' t false hc, Rb_cdf_Xb_outside hb' t true hc,
        Set.indicator_of_notMem (show (t : ℝ) ∉ Ioo (b / 2) (1 - b / 2) from hc)]
      ring
  simp_rw [hpt]
  have hh : (fun x : ℝ => (b - 2 * x) / 8) = fun x => 0 * x ^ 2 + (-1 / 4) * x + b / 8 := by
    funext x; ring
  rw [integral_unit_add_Ioo (fun x => x) (fun x => (b - 2 * x) / 8) (by fun_prop) (by fun_prop)
    (by linarith) (by linarith) (by linarith), hh, integral_quad]
  simp only [integral_id]
  ring

/-- **Proposition 5.3 (iv)**: `ρ(R_b) = 1 - (1/2)(1 - b)³`. -/
theorem spearmanRho_Rb {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    (Rb b hb).spearmanRho = 1 - 1 / 2 * (1 - b) ^ 3 := by
  obtain ⟨hb0, hb1⟩ := hb
  have hb' : b ∈ Icc (0 : ℝ) 1 := ⟨hb0, hb1⟩
  unfold Copula.spearmanRho
  rw [integral_Rb hb' (g := fun x : Fin 2 → I => (x 0 : ℝ) * (x 1 : ℝ)) (by fun_prop)]
  have hpt : ∀ t : I, (((Xb b (t, false)) 0 : ℝ) * ((Xb b (t, false)) 1 : ℝ) +
      ((Xb b (t, true)) 0 : ℝ) * ((Xb b (t, true)) 1 : ℝ)) / 2 =
      (t : ℝ) ^ 2 + (Ioo (b / 2) (1 - b / 2)).indicator
        (fun x : ℝ => (-1 / 2) * x ^ 2 + (1 / 4) * x + 0) (t : ℝ) := by
    intro t
    have hx0 : ((Xb b (t, false)) 0 : ℝ) = t := rfl
    have hx1 : ((Xb b (t, true)) 0 : ℝ) = t := rfl
    have hy0 : ((Xb b (t, false)) 1 : ℝ) = vbReal b t false := coe_Vb hb' t false
    have hy1 : ((Xb b (t, true)) 1 : ℝ) = vbReal b t true := coe_Vb hb' t true
    rw [hx0, hx1, hy0, hy1]
    by_cases hc : b / 2 < (t : ℝ) ∧ (t : ℝ) < 1 - b / 2
    · rw [Set.indicator_of_mem (show (t : ℝ) ∈ Ioo (b / 2) (1 - b / 2) from hc)]
      unfold vbReal
      simp only [hc, and_self, ↓reduceIte, Bool.false_eq_true]
      ring
    · rw [Set.indicator_of_notMem (show (t : ℝ) ∉ Ioo (b / 2) (1 - b / 2) from hc)]
      unfold vbReal
      simp only [hc, ↓reduceIte]
      ring
  simp_rw [hpt]
  rw [integral_unit_add_Ioo (fun x => x ^ 2) (fun x => (-1 / 2) * x ^ 2 + (1 / 4) * x + 0)
    (by fun_prop) (by fun_prop) (by linarith) (by linarith) (by linarith), integral_quad,
    integral_pow]
  ring

end Papers.OrendayLaresRockel2026XiBeta
