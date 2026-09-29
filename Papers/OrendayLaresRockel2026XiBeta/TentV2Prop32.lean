import Papers.OrendayLaresRockel2026XiBeta.TentV2Prop31
import Papers.OrendayLaresRockel2026XiBeta.TentTotalPositivity
import Papers.OrendayLaresRockel2026XiBeta.TentTranspose
import Copula.OrdinalSum.Basic

/-! # Proposition 3.2 (further properties of `L_b`) and Remark 3.3

* (i) `Ľ_b = L_{-b}`, `L̂_b = L_b`, exchangeability iff `b ∈ {-1,0,1}`, `L_0 = Π`,
  `L_1 = Π ⊕_{1/2} Π` (ordinal sum), `L_{-1} = Ľ_1`, the explicit asymmetry
  `L_b(u,1/2) ≠ L_b(1/2,u)` and the density `c_1`;
* (ii) stochastic monotonicity and quadrant dependence;
* (iii) reverse direction;
* (iv) total positivity (with the article's density `1 + σ g_b'`);
* (v) `ρ(L_b) = 3b|b|/4`, `τ(L_b) = b|b|/2`.
-/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

theorem tentG_one (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : tentG 1 v = min v (1 - v) := by
  unfold tentG medianTent
  rw [sgn_of_pos one_pos, abs_one, one_mul]
  rcases le_total v (1 / 2) with h | h
  · rw [abs_of_nonpos (by linarith), min_eq_left (by linarith), max_eq_right (by linarith [hv.1])]
    ring
  · rw [abs_of_nonneg (by linarith), min_eq_right (by linarith), max_eq_right (by linarith [hv.2])]
    ring

theorem tentG_neg_one (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : tentG (-1) v = -min v (1 - v) := by
  rw [tentG_neg, tentG_one v hv]

/-- `L_{±1}(u,v) = u v ± ℓ(u) ℓ(v)`. -/
theorem leftBoundary_one_cdf (hb : (1 : ℝ) ∈ Icc (-1) 1) (u v : I) :
    (leftBoundary 1 hb).cdf ![u, v] = (u : ℝ) * v + ellFun u * ellFun v := by
  rw [leftBoundary_cdf_paper, tentG_one v v.property]
  rfl

theorem leftBoundary_neg_one_cdf (hb : (-1 : ℝ) ∈ Icc (-1) 1) (u v : I) :
    (leftBoundary (-1) hb).cdf ![u, v] = (u : ℝ) * v - ellFun u * ellFun v := by
  rw [leftBoundary_cdf_paper, tentG_neg_one v v.property]
  unfold ellFun
  ring

/-- Proposition 3.2(i): `L_1` is the ordinal sum of `Π` and `Π` with respect to the
partition `{[0,1/2],[1/2,1]}`. -/
theorem leftBoundary_one_eq_ordinalSum (hb : (1 : ℝ) ∈ Icc (-1) 1) :
    leftBoundary 1 hb = (Copula.independence 2).ordinalSum (Copula.independence 2) Copula.unitHalf := by
  apply Copula.ext_cdf_two
  intro u v
  rw [leftBoundary_one_cdf]
  have ha : (0 : I) < Copula.unitHalf := by change (0 : ℝ) < 1 / 2; norm_num
  have ha1 : Copula.unitHalf < (1 : I) := by change (1 / 2 : ℝ) < 1; norm_num
  have hu : ((Copula.unitHalf : I) : ℝ) = 1 / 2 := rfl
  rcases le_total u Copula.unitHalf with h1 | h1 <;> rcases le_total v Copula.unitHalf with h2 | h2
  · rw [Copula.cdf_ordinalSum_lower _ _ _ _ _ h1 h2, Copula.cdf_independence,
      Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Copula.OrdinalSum.coe_lowerCoord_of_le _ _ ha h1, Copula.OrdinalSum.coe_lowerCoord_of_le _ _ ha h2, hu]
    have h1' : (u : ℝ) ≤ 1 / 2 := h1
    have h2' : (v : ℝ) ≤ 1 / 2 := h2
    unfold ellFun
    rw [min_eq_left (by linarith), min_eq_left (by linarith)]
    field_simp
    ring
  · rw [Copula.cdf_ordinalSum_lower_upper _ _ _ _ _ h1 h2]
    have h1' : (u : ℝ) ≤ 1 / 2 := h1
    have h2' : 1 / 2 ≤ (v : ℝ) := h2
    unfold ellFun
    rw [min_eq_left (by linarith), min_eq_right (by linarith)]
    ring
  · rw [Copula.cdf_ordinalSum_upper_lower _ _ _ _ _ h1 h2]
    have h1' : 1 / 2 ≤ (u : ℝ) := h1
    have h2' : (v : ℝ) ≤ 1 / 2 := h2
    unfold ellFun
    rw [min_eq_right (by linarith), min_eq_left (by linarith)]
    ring
  · rw [Copula.cdf_ordinalSum_upper _ _ _ _ _ h1 h2, Copula.cdf_independence,
      Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Copula.OrdinalSum.coe_upperCoord_of_ge _ _ ha1 h1, Copula.OrdinalSum.coe_upperCoord_of_ge _ _ ha1 h2, hu]
    have h1' : 1 / 2 ≤ (u : ℝ) := h1
    have h2' : 1 / 2 ≤ (v : ℝ) := h2
    unfold ellFun
    rw [min_eq_right (by linarith), min_eq_right (by linarith)]
    field_simp
    ring

/-- `L_{-1} = Ľ_1`. -/
theorem leftBoundary_neg_one_eq_check (hb : (1 : ℝ) ∈ Icc (-1) 1)
    (hb' : (-1 : ℝ) ∈ Icc (-1) 1) : leftBoundary (-1) hb' = (leftBoundary 1 hb).reflect {1} := by
  have h := leftBoundary_reflect_second 1 hb
  simp only [h]

/-- Proposition 3.2(i): `Ľ_b = L_{-b}`. -/
theorem leftBoundary_check (b : ℝ) (hb : b ∈ Icc (-1) 1) (hb' : -b ∈ Icc (-1) 1) :
    (leftBoundary b hb).reflect {1} = leftBoundary (-b) hb' :=
  leftBoundary_reflect_second b hb

/-- Proposition 3.2(i): `L̂_b = L_b`. -/
theorem leftBoundary_survival (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).survivalCopula = leftBoundary b hb :=
  leftBoundary_radiallySymmetric b hb

/-- The explicit asymmetry from the proof of (i): for `0 < |b| < 1` and `0 < u < α_b`,
`L_b(u,1/2) = u/2 + (b/2) ℓ(u) ≠ u/2 = L_b(1/2,u)`. -/
theorem leftBoundary_asymmetry (b : ℝ) (hb : b ∈ Icc (-1) 1) {u : I}
    (hu0 : 0 < (u : ℝ)) (hu : (u : ℝ) < (1 - |b|) / 2) (hb0 : b ≠ 0) :
    (leftBoundary b hb).cdf ![u, Copula.unitHalf] = u / 2 + b / 2 * ellFun u ∧
      (leftBoundary b hb).cdf ![Copula.unitHalf, u] = u / 2 ∧
      (leftBoundary b hb).cdf ![u, Copula.unitHalf] ≠ (leftBoundary b hb).cdf ![Copula.unitHalf, u] := by
  have h1 : (leftBoundary b hb).cdf ![u, Copula.unitHalf] = u / 2 + b / 2 * ellFun u := by
    rw [leftBoundary_cdf_paper]
    change (u : ℝ) * (1 / 2) + ellFun u * tentG b (1 / 2) = _
    rw [tentG_half]
    ring
  have h2 : (leftBoundary b hb).cdf ![Copula.unitHalf, u] = u / 2 := by
    rw [leftBoundary_cdf_paper, tentG_eq_zero (Or.inl hu)]
    change 1 / 2 * (u : ℝ) + ellFun (1 / 2) * 0 = _
    ring
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  have hl : 0 < ellFun u := by
    unfold ellFun
    exact lt_min hu0 (by linarith [u.property.2, hu, abs_nonneg b])
  intro h
  have : b / 2 * ellFun u = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact hb0 (by linarith)
  · exact hl.ne' h

/-- The density `c_1 = 1 + σ(u) σ(v)`-type formula: `c_1 = 2` on the two diagonal median
quadrants and `0` on the other two (with the half-open convention at `1/2`). -/
theorem tentDensity_one (hb : (1 : ℝ) ∈ Icc (-1) 1) (x : Fin 2 → I) :
    tentDensity 1 hb x = 1 + medianSign (x 0) * medianSign (x 1) := by
  unfold tentDensity signedTentSlope
  rw [dite_eq_left (by norm_num : (0 : ℝ) ≤ 1)]
  change 1 + medianSign (x 0) * tentSlope 1 (x 1) = _
  simp [tentSlope]

theorem tentDensity_one_diagonal (hb : (1 : ℝ) ∈ Icc (-1) 1) (x : Fin 2 → I)
    (h : (x 0 ≤ Copula.unitHalf ∧ x 1 ≤ Copula.unitHalf) ∨
      (¬ x 0 ≤ Copula.unitHalf ∧ ¬ x 1 ≤ Copula.unitHalf)) : tentDensity 1 hb x = 2 := by
  rw [tentDensity_one]
  unfold medianSign
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [ite_eq_left h1, ite_eq_left h2]; norm_num
  · rw [ite_eq_right h1, ite_eq_right h2]; norm_num

theorem tentDensity_one_antidiagonal (hb : (1 : ℝ) ∈ Icc (-1) 1) (x : Fin 2 → I)
    (h : (x 0 ≤ Copula.unitHalf ∧ ¬ x 1 ≤ Copula.unitHalf) ∨
      (¬ x 0 ≤ Copula.unitHalf ∧ x 1 ≤ Copula.unitHalf)) : tentDensity 1 hb x = 0 := by
  rw [tentDensity_one]
  unfold medianSign
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [ite_eq_left h1, ite_eq_right h2]; norm_num
  · rw [ite_eq_right h1, ite_eq_left h2]; norm_num

theorem tentDensityPaper_nonneg (b : ℝ) (x : Fin 2 → I) : 0 ≤ tentDensityPaper b x := by
  unfold tentDensityPaper
  have hs : |sigmaFun (x 0)| = 1 := by unfold sigmaFun; split_ifs <;> norm_num
  have hg : |tentGDeriv b (x 1)| ≤ 1 := by
    unfold tentGDeriv
    rw [abs_mul]
    have h2 : |(if (1 - |b|) / 2 < ((x 1 : I) : ℝ) ∧ ((x 1 : I) : ℝ) < 1 / 2 then (1 : ℝ) else 0) -
        (if 1 / 2 < ((x 1 : I) : ℝ) ∧ ((x 1 : I) : ℝ) < (1 + |b|) / 2 then (1 : ℝ) else 0)| ≤ 1 := by
      split_ifs with a b
      · exact absurd (lt_trans a.2 b.1) (lt_irrefl _)
      · norm_num
      · norm_num
      · norm_num
    calc _ ≤ 1 * 1 := mul_le_mul (abs_sgn_le b) h2 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have := abs_le.mp (show |sigmaFun (x 0) * tentGDeriv b (x 1)| ≤ 1 by
    rw [abs_mul, hs, one_mul]; exact hg)
  linarith [this.1]

/-- Proposition 3.2(iv) for the article's density `c_b = 1 + σ(u) g_b'(v)`. -/
theorem tentDensityPaper_ae_tp2_iff (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    HasAEOrderedMinors 1 (fun u v => tentDensityPaper b ![u, v]) ↔ b = 0 ∨ b = 1 :=
  (leftBoundary_density_version_ae_minors_iff b hb (measurable_tentDensityPaper b)
    (tentDensityPaper_nonneg b) (leftBoundary_density_paper b hb) 1).trans
    (tentDensity_ae_tp2_iff b hb)

theorem tentDensityPaper_ae_rr2_iff (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    HasAEOrderedMinors (-1) (fun u v => tentDensityPaper b ![u, v]) ↔ b = 0 ∨ b = -1 :=
  (leftBoundary_density_version_ae_minors_iff b hb (measurable_tentDensityPaper b)
    (tentDensityPaper_nonneg b) (leftBoundary_density_paper b hb) (-1)).trans
    (tentDensity_ae_rr2_iff b hb)

/-- Proposition 3.2, all five parts in the article's notation. -/
theorem proposition_3_2 (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    -- (i) symmetries and exchangeability
    ((leftBoundary b hb).reflect {1} =
        leftBoundary (-b) (by constructor <;> linarith [hb.1, hb.2])) ∧
      (leftBoundary b hb).survivalCopula = leftBoundary b hb ∧
      ((leftBoundary b hb).IsExchangeable ↔ b = -1 ∨ b = 0 ∨ b = 1) ∧
    -- (ii) stochastic monotonicity and quadrant dependence
    (0 ≤ b → (leftBoundary b hb).IsSI) ∧ (b ≤ 0 → (leftBoundary b hb).IsSD) ∧
      ((leftBoundary b hb).IsPQD ↔ 0 ≤ b) ∧ ((leftBoundary b hb).IsNQD ↔ b ≤ 0) ∧
    -- (iii) reverse direction
    ((leftBoundary b hb).transpose.IsSI ↔ b = 0 ∨ b = 1) ∧
      ((leftBoundary b hb).transpose.IsSD ↔ b = 0 ∨ b = -1) ∧
    -- (iv) total positivity of the density
    (HasAEOrderedMinors 1 (fun u v => tentDensityPaper b ![u, v]) ↔ b = 0 ∨ b = 1) ∧
      (HasAEOrderedMinors (-1) (fun u v => tentDensityPaper b ![u, v]) ↔ b = 0 ∨ b = -1) ∧
    -- (v) concordance
    (leftBoundary b hb).spearmanRho = 3 * b * |b| / 4 ∧
      (leftBoundary b hb).kendallTau = b * |b| / 2 :=
  ⟨leftBoundary_reflect_second b hb, leftBoundary_radiallySymmetric b hb,
    leftBoundary_exchangeable_iff b hb, leftBoundary_isSI b hb, leftBoundary_isSD b hb,
    leftBoundary_pqd_iff b hb, leftBoundary_nqd_iff b hb, leftBoundary_transpose_isSI_iff b hb,
    leftBoundary_transpose_isSD_iff b hb, tentDensityPaper_ae_tp2_iff b hb,
    tentDensityPaper_ae_rr2_iff b hb, by rw [leftBoundary_rho]; ring, by rw [leftBoundary_tau]; ring⟩

/-- Proposition 3.2(i): `L_0 = Π`. -/
theorem leftBoundary_zero_eq_independence (h0 : (0 : ℝ) ∈ Icc (-1) 1) :
    leftBoundary 0 h0 = Copula.independence 2 := leftBoundary_zero h0

/-! ### Values of the density (Figure 2) and the second partial derivative -/

/-- Proposition 3.2(iii): `∂₂ L_b(u,v) = u + ℓ(u) g_b'(v)` away from the break points of `g_b`. -/
theorem hasDerivAt_tent_formula_second (b u : ℝ) {v : ℝ} (h1 : v ≠ (1 - |b|) / 2)
    (h2 : v ≠ 1 / 2) (h3 : v ≠ (1 + |b|) / 2) :
    HasDerivAt (fun w : ℝ => u * w + ellFun u * tentG b w) (u + ellFun u * tentGDeriv b v) v := by
  have h := ((hasDerivAt_id v).const_mul u).add ((hasDerivAt_tentG b h1 h2 h3).const_mul (ellFun u))
  convert h using 1
  · rfl
  · ring

/-- Figure 2, strip `u < 1/2`: the density is `1 + sgn b` on `(α_b, 1/2)`, `1 - sgn b` on
`(1/2, 1 - α_b)` and `1` elsewhere. -/
theorem tentDensityPaper_left {b : ℝ} {x : Fin 2 → I} (hu : (x 0 : ℝ) < 1 / 2) :
    (((1 - |b|) / 2 < (x 1 : ℝ) ∧ (x 1 : ℝ) < 1 / 2) → tentDensityPaper b x = 1 + sgn b) ∧
    ((1 / 2 < (x 1 : ℝ) ∧ (x 1 : ℝ) < (1 + |b|) / 2) → tentDensityPaper b x = 1 - sgn b) ∧
    ((¬ ((1 - |b|) / 2 < (x 1 : ℝ) ∧ (x 1 : ℝ) < 1 / 2)) →
      (¬ (1 / 2 < (x 1 : ℝ) ∧ (x 1 : ℝ) < (1 + |b|) / 2)) → tentDensityPaper b x = 1) := by
  have hs : sigmaFun (x 0) = 1 := by rw [sigmaFun, ite_eq_left hu]
  refine ⟨fun h => ?_, fun h => ?_, fun h h' => ?_⟩
  · have hn : ¬ (1 / 2 < (x 1 : ℝ) ∧ (x 1 : ℝ) < (1 + |b|) / 2) := fun h' => by linarith [h.2, h'.1]
    unfold tentDensityPaper tentGDeriv
    rw [hs, ite_eq_left h, ite_eq_right hn]; ring
  · have hn : ¬ ((1 - |b|) / 2 < (x 1 : ℝ) ∧ (x 1 : ℝ) < 1 / 2) := fun h' => by linarith [h.1, h'.2]
    unfold tentDensityPaper tentGDeriv
    rw [hs, ite_eq_right hn, ite_eq_left h]; ring
  · unfold tentDensityPaper tentGDeriv
    rw [hs, ite_eq_right h, ite_eq_right h']; ring

/-- Figure 2, strip `u ≥ 1/2`: the density is `1 - sgn b` on `(α_b, 1/2)`, `1 + sgn b` on
`(1/2, 1 - α_b)` and `1` elsewhere. -/
theorem tentDensityPaper_right {b : ℝ} {x : Fin 2 → I} (hu : 1 / 2 ≤ (x 0 : ℝ)) :
    (((1 - |b|) / 2 < (x 1 : ℝ) ∧ (x 1 : ℝ) < 1 / 2) → tentDensityPaper b x = 1 - sgn b) ∧
    ((1 / 2 < (x 1 : ℝ) ∧ (x 1 : ℝ) < (1 + |b|) / 2) → tentDensityPaper b x = 1 + sgn b) ∧
    ((¬ ((1 - |b|) / 2 < (x 1 : ℝ) ∧ (x 1 : ℝ) < 1 / 2)) →
      (¬ (1 / 2 < (x 1 : ℝ) ∧ (x 1 : ℝ) < (1 + |b|) / 2)) → tentDensityPaper b x = 1) := by
  have hs : sigmaFun (x 0) = -1 := by rw [sigmaFun, ite_eq_right (not_lt.mpr hu)]
  refine ⟨fun h => ?_, fun h => ?_, fun h h' => ?_⟩
  · have hn : ¬ (1 / 2 < (x 1 : ℝ) ∧ (x 1 : ℝ) < (1 + |b|) / 2) := fun h' => by linarith [h.2, h'.1]
    unfold tentDensityPaper tentGDeriv
    rw [hs, ite_eq_left h, ite_eq_right hn]; ring
  · have hn : ¬ ((1 - |b|) / 2 < (x 1 : ℝ) ∧ (x 1 : ℝ) < 1 / 2) := fun h' => by linarith [h.1, h'.2]
    unfold tentDensityPaper tentGDeriv
    rw [hs, ite_eq_right hn, ite_eq_left h]; ring
  · unfold tentDensityPaper tentGDeriv
    rw [hs, ite_eq_right h, ite_eq_right h']; ring

end Papers.OrendayLaresRockel2026XiBeta
