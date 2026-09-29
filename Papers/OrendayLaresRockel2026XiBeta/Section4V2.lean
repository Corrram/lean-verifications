import Papers.OrendayLaresRockel2026XiBeta.Section2Classes
import Papers.OrendayLaresRockel2026XiBeta.DExchange
import Papers.OrendayLaresRockel2026XiBeta.TentV2Prop32
import Copula.Order.StrictSpearman

/-! # Theorem 1.1, Corollary 4.3 and quantitative introduction claims (version 2)

The witnesses are the article's own: the tent copulas `L_b` (`leftBoundary`) and the
interval-exchange copulas `D_b` (`dExchange`). Regions are the sets `xiBetaRegion A`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

/-- The region `{(x, y) ∈ [0,1] × [-1,1] : |y|³ ≤ 2x}`. -/
def exactRegion : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (-1 : ℝ) 1 ∧ |p.2| ^ 3 ≤ 2 * p.1}

/-- Theorem 1.1, region statement: `R_{ξ,β} = {(x,y) ∈ [0,1]×[-1,1] : |y|³ ≤ 2x}`. -/
theorem theorem_1_1_region : xiBetaRegion (Set.univ : Set (Copula 2)) = exactRegion := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨C, -, rfl, rfl⟩
    exact ⟨C.chatterjeeXi_mem_Icc, C.blomqvistBeta_mem_Icc, beta_cubic_le_two_xi C⟩
  · intro h
    obtain ⟨C, hxi, hbeta⟩ := (exact_xi_beta_region x y).mpr ⟨h.1, h.2.1, h.2.2⟩
    exact ⟨C, trivial, hxi, hbeta⟩

/-- Theorem 1.1, inequality (1.3) with the equality case: `|β(C)|³ ≤ 2ξ(C)` with equality iff
`C = L_{β(C)}`. -/
theorem theorem_1_1_inequality (C : Copula 2) :
    |C.blomqvistBeta| ^ 3 ≤ 2 * C.chatterjeeXi ∧
      (|C.blomqvistBeta| ^ 3 = 2 * C.chatterjeeXi ↔
        C = leftBoundary C.blomqvistBeta C.blomqvistBeta_mem_Icc) := by
  refine ⟨beta_cubic_le_two_xi C, ?_⟩
  rw [← xi_eq_lower_iff C C.blomqvistBeta C.blomqvistBeta_mem_Icc rfl]
  constructor <;> intro h <;> linarith

/-- Theorem 1.1: every point of the right boundary `{1} × [-1,1]` is attained by `D_b`,
a deterministic (completely dependent) copula. -/
theorem theorem_1_1_right_boundary (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) :
    (dExchange b hb).chatterjeeXi = 1 ∧ (dExchange b hb).blomqvistBeta = b ∧
      ∃ f : I → I, Measurable f ∧ MeasurePreserving f volume volume ∧
        ∀ᵐ x ∂(dExchange b hb).toMeasure, x 1 = f (x 0) :=
  ⟨dExchange_xi b hb, dExchange_beta b hb, dExchange_completelyDependent b hb⟩

/-- `R_{ξ,β}` is symmetric under `y ↦ -y`. -/
theorem exactRegion_neg (x y : ℝ) : (x, -y) ∈ exactRegion ↔ (x, y) ∈ exactRegion := by
  constructor
  · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
    exact ⟨h1, ⟨by linarith, by linarith⟩, by simpa only [abs_neg] using h4⟩
  · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
    exact ⟨h1, ⟨by linarith, by linarith⟩, by simpa only [abs_neg] using h4⟩

/-- `L_b` and `D_b` both belong to any class `A` containing all radially symmetric copulas of
the kind used in Corollary 4.3; here the general interpolation step. -/
theorem region_of_witnesses {A : Set (Copula 2)} (hA : IsConvexClass A) {b x : ℝ}
    (hb : b ∈ Icc (-1 : ℝ) 1) (hL : leftBoundary b hb ∈ A) (hD : dExchange b hb ∈ A)
    (hx : x ∈ Icc (0 : ℝ) 1) (hbound : |b| ^ 3 ≤ 2 * x) : (x, b) ∈ xiBetaRegion A := by
  obtain ⟨C, hC, hxi, hbeta⟩ := interpolation_lemma hA hL hD (leftBoundary_beta b hb)
    (dExchange_beta b hb) (x := x) (by
      rw [leftBoundary_xi, dExchange_xi]
      exact Set.mem_uIcc.mpr (Or.inl ⟨by linarith, hx.2⟩))
  exact ⟨C, hC, hxi, hbeta⟩

/-- Corollary 4.3: `R^{RS} = R`. -/
theorem corollary_4_3_rs : xiBetaRegion classRS = exactRegion := by
  apply Subset.antisymm
  · rw [← theorem_1_1_region]
    exact xiBetaRegion_mono (subset_univ _)
  · rintro ⟨x, b⟩ ⟨hx, hb, hbound⟩
    exact region_of_witnesses convex_rs hb (leftBoundary_radiallySymmetric b hb)
      (dExchange_radiallySymmetric b hb) hx hbound

/-- The upper half `R ∩ ([0,1] × [0,1])`. -/
def exactRegionUpper : Set (ℝ × ℝ) := exactRegion ∩ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)

/-- The lower half `R ∩ ([0,1] × [-1,0])`. -/
def exactRegionLower : Set (ℝ × ℝ) := exactRegion ∩ (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 0)

/-- Corollary 4.3: `R^{PQD} = R^{PQD,RS} = R ∩ ([0,1] × [0,1])`. -/
theorem corollary_4_3_pqd :
    xiBetaRegion classPQD = exactRegionUpper ∧ xiBetaRegion (classPQD ∩ classRS) = exactRegionUpper := by
  have hup : xiBetaRegion classPQD ⊆ exactRegionUpper := by
    rintro ⟨x, y⟩ ⟨C, hC, rfl, rfl⟩
    have hb : 0 ≤ C.blomqvistBeta := Copula.IsPQD.blomqvistBeta_nonneg hC
    exact ⟨⟨C.chatterjeeXi_mem_Icc, C.blomqvistBeta_mem_Icc, beta_cubic_le_two_xi C⟩,
      C.chatterjeeXi_mem_Icc, ⟨hb, C.blomqvistBeta_mem_Icc.2⟩⟩
  have hlow : exactRegionUpper ⊆ xiBetaRegion (classPQD ∩ classRS) := by
    rintro ⟨x, b⟩ ⟨⟨hx, hb, hbound⟩, -, hb0, -⟩
    exact region_of_witnesses (convex_pqd.inter convex_rs) hb
      ⟨(leftBoundary_pqd_iff b hb).mpr hb0, leftBoundary_radiallySymmetric b hb⟩
      ⟨dExchange_pqd b hb hb0, dExchange_radiallySymmetric b hb⟩ hx hbound
  have hmid : xiBetaRegion (classPQD ∩ classRS) ⊆ xiBetaRegion classPQD :=
    xiBetaRegion_mono inter_subset_left
  exact ⟨Subset.antisymm hup (hlow.trans hmid), Subset.antisymm (hmid.trans hup) hlow⟩

/-- Corollary 4.3: `R^{NQD} = R^{NQD,RS} = R ∩ ([0,1] × [-1,0])`, by the reflection (2.4). -/
theorem corollary_4_3_nqd :
    xiBetaRegion classNQD = exactRegionLower ∧ xiBetaRegion (classNQD ∩ classRS) = exactRegionLower := by
  have hneg : (fun p : ℝ × ℝ => (p.1, -p.2)) '' exactRegionUpper = exactRegionLower := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨⟨x', y'⟩, ⟨hR, hx, hy⟩, he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨(exactRegion_neg x' y').mpr hR, hx, ?_⟩
      simp only [mem_Icc] at hy ⊢
      constructor <;> linarith [hy.1, hy.2]
    · rintro ⟨hR, hx, hy⟩
      refine ⟨(x, -y), ⟨(exactRegion_neg x y).mpr hR |> fun h => by simpa using h, hx, ?_⟩, by simp⟩
      simp only [mem_Icc] at hy ⊢
      constructor <;> linarith [hy.1, hy.2]
  have h1 : xiBetaRegion classNQD = exactRegionLower := by
    rw [xiBetaRegion_nqd_eq, (corollary_4_3_pqd).1, hneg]
  have h2 : xiBetaRegion (classNQD ∩ classRS) = exactRegionLower := by
    have : classNQD ∩ classRS = checkClass (classPQD ∩ classRS) := by
      rw [checkClass_inter, checkClass_pqd, checkClass_rs]
    rw [this, xiBetaRegion_checkClass, (corollary_4_3_pqd).2, hneg]
  exact ⟨h1, h2⟩

/-- Reflection for the SD/RS intersection, used with Theorem 1.2: `Č` maps `SI ∩ RS` onto
`SD ∩ RS`, hence `R^{SD,RS}` is the mirror image of `R^{SI,RS}`. -/
theorem xiBetaRegion_sd_rs_eq :
    xiBetaRegion (classSD ∩ classRS) =
      (fun p : ℝ × ℝ => (p.1, -p.2)) '' xiBetaRegion (classSI ∩ classRS) := by
  have : classSD ∩ classRS = checkClass (classSI ∩ classRS) := by
    rw [checkClass_inter, checkClass_si, checkClass_rs]
  rw [this, xiBetaRegion_checkClass]

/-- If `R^{SI} = R^{SI,RS}` then `R^{SD} = R^{SD,RS}` (used for Theorem 1.2). -/
theorem xiBetaRegion_sd_eq_sd_rs (h : xiBetaRegion classSI = xiBetaRegion (classSI ∩ classRS)) :
    xiBetaRegion classSD = xiBetaRegion (classSD ∩ classRS) := by
  rw [xiBetaRegion_sd_eq, xiBetaRegion_sd_rs_eq, h]

/-! ### Quantitative claims of the introduction -/

/-- `L_{±1}` attain the lower endpoint `ξ = 1/2` of the horizontal edges `β = ±1`. -/
theorem leftBoundary_pm_one_xi :
    (leftBoundary 1 (by norm_num)).chatterjeeXi = 1 / 2 ∧
      (leftBoundary (-1) (by norm_num)).chatterjeeXi = 1 / 2 := by
  constructor <;> (rw [leftBoundary_xi]; norm_num)

/-- Mixtures of `D_b` and `L_b` fill the vertical segment of the fibre over `β = b`:
for each `x ∈ [|b|³/2, 1]` there is a mixture with `ξ = x` and `β = b`. -/
theorem exists_mixture_leftBoundary_dExchange (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) {x : ℝ}
    (hx : x ∈ Icc (|b| ^ 3 / 2) 1) :
    ∃ a : I, ((dExchange b hb).mix (leftBoundary b hb) a).chatterjeeXi = x ∧
      ((dExchange b hb).mix (leftBoundary b hb) a).blomqvistBeta = b := by
  obtain ⟨a, ha⟩ := Verification.exists_unitInterval_eq
    (xi_mixture_continuous (dExchange b hb) (leftBoundary b hb)) (z := x)
    (by simpa [leftBoundary_xi] using hx.1) (by simpa [dExchange_xi] using hx.2)
  exact ⟨a, ha, beta_mixture_fixed _ _ (dExchange_beta b hb) (leftBoundary_beta b hb) a⟩

/-- "Mixtures of `L_{±1}` and `D_{±1}` fill the horizontal edges at `β = ±1`." -/
theorem horizontal_edges_attained (x : ℝ) (hx : x ∈ Icc (1 / 2 : ℝ) 1) :
    (x, (1 : ℝ)) ∈ xiBetaRegion (Set.univ : Set (Copula 2)) ∧
      (x, (-1 : ℝ)) ∈ xiBetaRegion (Set.univ : Set (Copula 2)) := by
  rw [theorem_1_1_region]
  constructor <;> refine ⟨⟨by linarith [hx.1], hx.2⟩, ⟨by norm_num, by norm_num⟩, ?_⟩ <;>
    simp <;> linarith [hx.1]

/-- Introduction: for positively quadrant dependent copulas, Spearman's `ρ` vanishes only under
independence. -/
theorem pqd_rho_eq_zero_iff (C : Copula 2) (h : C.IsPQD) : C.spearmanRho = 0 ↔ C = Copula.independence 2 :=
  Copula.IsPQD.spearmanRho_eq_zero_iff h

/-- Introduction, inequality (1.5) rewritten: `3(1-y)² ≤ 4(1-x)` iff `y ≥ 1 - 2√((1-x)/3)`
(for `y ≤ 1`, `x ≤ 1`). -/
theorem one_sub_sq_le_iff {x y : ℝ} (hx : x ≤ 1) (hy : y ≤ 1) :
    3 * (1 - y) ^ 2 ≤ 4 * (1 - x) ↔ 1 - 2 * Real.sqrt ((1 - x) / 3) ≤ y := by
  have hs : 0 ≤ (1 - x) / 3 := by linarith
  have hq := Real.sq_sqrt hs
  have hq0 := Real.sqrt_nonneg ((1 - x) / 3)
  constructor
  · intro h
    by_contra hlt
    have hlt' := lt_of_not_ge hlt
    nlinarith
  · intro h
    nlinarith

/-- Introduction: in the SI region, `ξ > 1/4` forces `β > 0`
(from `3(1-β)² ≤ 4(1-ξ)` and `β ≥ 0`). -/
theorem xi_gt_quarter_beta_pos {x y : ℝ} (hy0 : 0 ≤ y) (h : 3 * (1 - y) ^ 2 ≤ 4 * (1 - x))
    (hx : 1 / 4 < x) : 0 < y := by
  by_contra hn
  have : y = 0 := le_antisymm (not_lt.mp hn) hy0
  subst this
  linarith

/-- Introduction: a small value of `ξ` pins `β` near zero, `|β(C)| ≤ (2 ξ(C))^{1/3}`. -/
theorem abs_beta_le_rpow (C : Copula 2) :
    |C.blomqvistBeta| ≤ (2 * C.chatterjeeXi) ^ ((3 : ℕ)⁻¹ : ℝ) := by
  have h := beta_cubic_le_two_xi C
  calc |C.blomqvistBeta| = (|C.blomqvistBeta| ^ 3) ^ ((3 : ℕ)⁻¹ : ℝ) :=
        (Real.pow_rpow_inv_natCast (abs_nonneg _) (by norm_num)).symm
    _ ≤ (2 * C.chatterjeeXi) ^ ((3 : ℕ)⁻¹ : ℝ) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)

/-- The dots of Figure 1 (except `R_0`): `Π = (0,0)`, `M = (1,1)`, `W = (1,-1)`,
`L_{±1} = (1/2, ±1)`. -/
theorem figure1_dots :
    ((Copula.independence 2).chatterjeeXi = 0 ∧ (Copula.independence 2).blomqvistBeta = 0) ∧
    ((Copula.comonotonic 2).chatterjeeXi = 1 ∧ (Copula.comonotonic 2).blomqvistBeta = 1) ∧
    ((Copula.countermonotonic).chatterjeeXi = 1 ∧ (Copula.countermonotonic).blomqvistBeta = -1) ∧
    ((leftBoundary 1 (by norm_num)).chatterjeeXi = 1 / 2 ∧
      (leftBoundary 1 (by norm_num)).blomqvistBeta = 1) ∧
    ((leftBoundary (-1) (by norm_num)).chatterjeeXi = 1 / 2 ∧
      (leftBoundary (-1) (by norm_num)).blomqvistBeta = -1) := by
  refine ⟨⟨Copula.chatterjeeXi_independence, ?_⟩, ⟨Copula.chatterjeeXi_comonotonic, ?_⟩,
    ⟨Copula.chatterjeeXi_countermonotonic, Copula.blomqvistBeta_countermonotonic⟩,
    ⟨?_, leftBoundary_beta _ _⟩, ⟨?_, leftBoundary_beta _ _⟩⟩
  · simp
  · exact Copula.blomqvistBeta_comonotonic
  · rw [leftBoundary_xi]; norm_num
  · rw [leftBoundary_xi]; norm_num

end Papers.OrendayLaresRockel2026XiBeta
