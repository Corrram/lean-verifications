import Papers.Rockel2026ExactBlest.ExactBlestClaims

/-!
# The manuscript's parametrization of the extremal families

In exact-blest-regions.tex every family parameter increases with dependence:

* `D_c` (Section 3, the rank map `ζ_c` centred at `1-c`) runs from `D_0 = W` to `D_1 = M`;
* `A_w` (Section 4.1) pairs the leading fraction `w` of the first variable comonotonically
  and runs from `A_0 = W` to `A_1 = M`;
* `B_b` (Section 4.1), `b ∈ (0,1/2]`, splits the leading fraction `b` between two branches,
  with `B_{1/2} = A_{1/2}` and `B_b → W` as `b → 0`.

The other modules work with the reflected parameters `1-c`, `1-w`, and `a = 1-b`. This module
defines the families exactly as printed (`paperD`, `paperA`, `paperB`) and restates every
family-dependent claim of the manuscript in that notation: the coefficient formulas, parameter
monotonicity and derivatives, graph laws and rank maps, the potentials of Propositions 4.3 and
4.4 with their contact sets, the extremizers in Theorems 1.1 and 1.2 and Corollaries 3.2, 4.5,
and 4.6, Remark 4.7, and all values printed above the panels of Figures 2 and 3.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval Topology
open Papers.Rockel2026XiBlest

namespace Papers.Rockel2026ExactBlest

noncomputable section
set_option maxHeartbeats 4000000

/-! ## Reflection of the parameter -/

theorem symm_lt_symm_iff (v w : I) : unitInterval.symm w < unitInterval.symm v ↔ v < w := by
  rw [← Subtype.coe_lt_coe, ← Subtype.coe_lt_coe, unitInterval.coe_symm_eq,
    unitInterval.coe_symm_eq]
  constructor <;> intro h <;> linarith

theorem symm_half : unitInterval.symm Copula.unitHalf = Copula.unitHalf := by
  apply Subtype.ext
  rw [unitInterval.coe_symm_eq]
  norm_num [Copula.unitHalf]

/-! ## The family `A_w` -/

/-- The manuscript's `A_w`: under its reflected-coordinate coupling the leading fraction `w` of
the first variable is comonotone with the trailing fraction of the second, and the remaining
bottom ranks are countermonotone with the top ranks of the second. -/
def paperA (w : I) : Copula 2 := familyA (unitInterval.symm w)

theorem paperA_symm (w : I) : paperA (unitInterval.symm w) = familyA w := by
  rw [paperA, unitInterval.symm_symm]

theorem eta_paperA (w : I) : eta (paperA w) = 2 * (w : ℝ) ^ 3 - 1 := by
  rw [paperA, eta_familyA, unitInterval.coe_symm_eq]
  ring

theorem nu_paperA (w : I) : blestNu (paperA w) = 2 * (2 - (w : ℝ)) * (w : ℝ) ^ 3 - 1 := by
  rw [paperA, nu_familyA, unitInterval.coe_symm_eq]
  ring

theorem nu_transpose_paperA (w : I) : blestNu (paperA w).transpose = 2 * (w : ℝ) ^ 4 - 1 := by
  rw [paperA, nu_transpose_familyA, unitInterval.coe_symm_eq]
  ring

/-- Lemma 4.1: `ν(A_w) - η(A_w) = 2(1-w)w³`. -/
theorem paperA_gap (w : I) :
    blestNu (paperA w) - eta (paperA w) = 2 * (1 - (w : ℝ)) * (w : ℝ) ^ 3 := by
  rw [nu_paperA, eta_paperA]
  ring

theorem paperA_zero : paperA 0 = Copula.countermonotonic := by
  rw [paperA, unitInterval.symm_zero, familyA_one]

theorem paperA_one : paperA 1 = Copula.comonotonic 2 := by
  rw [paperA, unitInterval.symm_one, familyA_zero]

/-- Lemma 4.1: `w ↦ η(A_w)` is strictly increasing. -/
theorem eta_paperA_strictMono : StrictMono (fun w : I => eta (paperA w)) := by
  intro v w h
  exact eta_familyA_strictAnti ((symm_lt_symm_iff v w).mpr h)

/-- Lemma 4.1: for `w ∈ [1/2,1]`, `η(A_w)` ranges over `[-3/4,1]`. -/
theorem paperA_eta_range (w : I) (hw : (1 / 2 : ℝ) ≤ w) : eta (paperA w) ∈ Icc (-3 / 4 : ℝ) 1 := by
  apply graph_eta_range
  rw [unitInterval.coe_symm_eq]
  linarith

/-- The map `T_w` of Section 4.1. -/
theorem paperT_formula (w u : I) :
    (graphRank (unitInterval.symm w) u : ℝ) =
      if (u : ℝ) ≤ 1 - (w : ℝ) then 1 - (u : ℝ) else (u : ℝ) + (w : ℝ) - 1 := by
  change (if (u : ℝ) ≤ (unitInterval.symm w : ℝ) then 1 - (u : ℝ)
    else (u : ℝ) - (unitInterval.symm w : ℝ)) = _
  rw [unitInterval.coe_symm_eq]
  split_ifs <;> ring

/-- `A_w` is the copula associated with the law of `(X, T_w(X))`. -/
theorem paperA_graph_law (w : I) :
    (paperA w).survivalCopula.toMeasure =
      (volume : Measure I).map (fun u => ![u, graphRank (unitInterval.symm w) u]) :=
  familyA_graph_law_all _

/-! ## The family `B_b` -/

theorem symm_half_le (b : I) (hb : (b : ℝ) ≤ 1 / 2) : (1 / 2 : ℝ) ≤ unitInterval.symm b := by
  rw [unitInterval.coe_symm_eq]
  linarith

/-- The manuscript's `B_b` for `b ∈ [0,1/2]`: the leading fraction `b` of the first variable is
split between the two branches of `R_b`, the rest is countermonotone. The value `b = 0` gives `W`,
the continuous endpoint of the family. -/
def paperB (b : I) (hb : (b : ℝ) ≤ 1 / 2) : Copula 2 :=
  familyB (unitInterval.symm b) (symm_half_le b hb)

theorem paperB_symm (a : I) (ha : (1 / 2 : ℝ) ≤ a) (hb : ((unitInterval.symm a : I) : ℝ) ≤ 1 / 2) :
    paperB (unitInterval.symm a) hb = familyB a ha := by
  unfold paperB
  congr 1
  exact unitInterval.symm_symm a

/-- `e_b` in (6) and (17). -/
def paperEtaB (b : ℝ) : ℝ := -1 + b ^ 3 * (2 * b ^ 2 - 9 * b + 8) / (8 * (1 - b) ^ 2)
/-- `ν(B_b)` in (17), equivalently `Λ(n_b)` in (22). -/
def paperNuB (b : ℝ) : ℝ := -1 + (2 - b) * b ^ 3 / (1 - b)
/-- `n_b = ν(B_bᵀ)` in (22). -/
def paperNB (b : ℝ) : ℝ := -1 + b ^ 4 * (3 - 2 * b) / (4 * (1 - b) ^ 2)
/-- `Υ(e_b)` in (6). -/
def paperUpsB (b : ℝ) : ℝ := b ^ 3 * (6 * b ^ 2 - 15 * b + 8) / (8 * (1 - b) ^ 2)

theorem paperEtaB_eq (b : ℝ) : paperEtaB b = etaB (1 - b) := by
  unfold paperEtaB etaB
  congr 2
  ring

theorem paperNuB_eq (b : ℝ) : paperNuB b = nuB (1 - b) := by
  unfold paperNuB nuB
  congr 2
  ring

theorem paperNB_eq (b : ℝ) : paperNB b = transposeParam (1 - b) := by
  unfold paperNB transposeParam
  congr 2
  ring

theorem paperUpsB_eq (b : ℝ) (hb : b ≠ 1) : paperUpsB b = paperNuB b - paperEtaB b := by
  have h : 1 - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  unfold paperUpsB paperNuB paperEtaB
  field_simp
  ring

theorem eta_paperB (b : I) (hb : (b : ℝ) ≤ 1 / 2) : eta (paperB b hb) = paperEtaB b := by
  rw [paperB, eta_familyB, unitInterval.coe_symm_eq, paperEtaB_eq]

theorem nu_paperB (b : I) (hb : (b : ℝ) ≤ 1 / 2) : blestNu (paperB b hb) = paperNuB b := by
  rw [paperB, nu_familyB, unitInterval.coe_symm_eq, paperNuB_eq]

theorem nu_transpose_paperB (b : I) (hb : (b : ℝ) ≤ 1 / 2) :
    blestNu (paperB b hb).transpose = paperNB b := by
  rw [paperB, nu_transpose_familyB_param, unitInterval.coe_symm_eq, paperNB_eq]

/-- Lemma 4.1: `ν(B_b) - η(B_b) = Υ(e_b)` with the displayed formula (6). -/
theorem paperB_gap (b : I) (hb : (b : ℝ) ≤ 1 / 2) :
    blestNu (paperB b hb) - eta (paperB b hb) = paperUpsB b := by
  rw [nu_paperB, eta_paperB, paperUpsB_eq _ (by linarith)]

/-- For `b = 1/2`, the second branch carries no mass and `B_{1/2} = A_{1/2}`. -/
theorem paperB_half :
    paperB Copula.unitHalf (by norm_num [Copula.unitHalf]) = paperA Copula.unitHalf := by
  have h : paperB Copula.unitHalf (by norm_num [Copula.unitHalf]) =
      familyB Copula.unitHalf (by norm_num [Copula.unitHalf]) := by
    unfold paperB
    congr 1
    exact symm_half
  rw [h, familyB_half, paperA, symm_half]

/-- The endpoint `b = 0` is `W`. -/
theorem paperB_zero : paperB 0 (by norm_num) = Copula.countermonotonic := by
  have h : paperB 0 (by norm_num) = familyB 1 (by norm_num) := by
    unfold paperB
    congr 1
    exact unitInterval.symm_zero
  rw [h, familyB_one]

/-- Lemma 4.1: `b ↦ e_b` is strictly increasing on `[0,1/2]`. -/
theorem paperEtaB_strictMonoOn : StrictMonoOn paperEtaB (Icc 0 (1 / 2)) := by
  intro x hx y hy hxy
  rw [paperEtaB_eq, paperEtaB_eq]
  exact randomized_parameter_strictAnti ⟨by linarith [hy.2], by linarith [hy.1]⟩
    ⟨by linarith [hx.2], by linarith [hx.1]⟩ (by linarith)

/-- Lemma 4.1: the displayed derivative `∂_b η(B_b)`. -/
theorem hasDerivAt_paperEtaB (b : ℝ) (hb : b ≠ 1) :
    HasDerivAt paperEtaB (b ^ 2 * (2 - b) * (3 * b ^ 2 - 8 * b + 6) / (4 * (1 - b) ^ 3)) b := by
  have h0 : 1 - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have hfun : paperEtaB = etaB ∘ (fun t : ℝ => 1 - t) := funext paperEtaB_eq
  have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) b := by
    simpa using (hasDerivAt_id b).const_sub 1
  have h := (hasDerivAt_etaB (1 - b) h0).comp b h1
  rw [hfun]
  convert h using 1
  field_simp
  ring

theorem deriv_paperEtaB_pos (b : ℝ) (hb0 : 0 < b) (hb : b < 1) :
    0 < b ^ 2 * (2 - b) * (3 * b ^ 2 - 8 * b + 6) / (4 * (1 - b) ^ 3) := by
  have h1 : 0 < 1 - b := by linarith
  have hq : 0 < 3 * b ^ 2 - 8 * b + 6 := by nlinarith [sq_nonneg (3 * b - 4)]
  apply div_pos
  · exact mul_pos (mul_pos (pow_pos hb0 2) (by linarith)) hq
  · exact mul_pos (by norm_num) (pow_pos h1 3)

/-- Lemma 4.1: `e_{1/2} = -3/4` and `e_b → -1` as `b → 0`. -/
theorem paperEtaB_endpoints :
    paperEtaB (1 / 2) = -3 / 4 ∧ paperEtaB 0 = -1 ∧
      Tendsto paperEtaB (𝓝[>] 0) (𝓝 (-1)) := by
  refine ⟨by norm_num [paperEtaB], by norm_num [paperEtaB], ?_⟩
  have h := (hasDerivAt_paperEtaB 0 (by norm_num)).continuousAt.tendsto
  have h0 : paperEtaB 0 = -1 := by norm_num [paperEtaB]
  rw [h0] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem paperEtaB_range (b : I) (hb : (b : ℝ) ≤ 1 / 2) : paperEtaB b ∈ Icc (-1 : ℝ) (-3 / 4) := by
  have h := etaB_range (unitInterval.symm b) (symm_half_le b hb)
  rwa [unitInterval.coe_symm_eq, ← paperEtaB_eq] at h

/-- The map `R_b` of Section 4.1. -/
def paperR (b z : ℝ) : ℝ :=
  if z ≤ b / (2 * (1 - b)) then 2 * (1 - b) * z + 1 - b
  else if z ≤ b then (1 - b) * (1 - 2 * z) / (1 - 2 * b) else 1 - z

theorem cutB_paper (b : ℝ) : cutB (1 - b) = b / (2 * (1 - b)) := by
  unfold cutB
  congr 1
  ring

theorem kA_paper (w : ℝ) : kA (1 - w) = (3 - 2 * w) / (2 * w) := by
  unfold kA
  congr 1 <;> ring

theorem kB_paper (b : ℝ) : kB (1 - b) = 2 * (1 - b) / b := by
  unfold kB
  congr 1
  ring

theorem paperR_eq (b z : ℝ) : randomRankReal (1 - b) z = paperR b z := by
  unfold randomRankReal paperR
  rw [cutB_paper, sub_sub_cancel, show 2 * (1 - b) - 1 = 1 - 2 * b by ring]
  split_ifs <;> ring

/-- `B_b` is the copula associated with the law of `(R_b(Z), Z)`. -/
theorem paperB_graph_law (b : I) (hb0 : 0 < (b : ℝ)) (hb : (b : ℝ) < 1 / 2) :
    (paperB b hb.le).survivalCopula.toMeasure =
      (volume : Measure I).map (fun z => ![randomRank (unitInterval.symm b)
        (by rw [unitInterval.coe_symm_eq]; linarith)
        (by rw [unitInterval.coe_symm_eq]; linarith) z, z]) :=
  familyB_graph_law _ _ _

theorem paperR_formula (b : I) (hb0 : 0 < (b : ℝ)) (hb : (b : ℝ) < 1 / 2) (z : I) :
    (randomRank (unitInterval.symm b) (by rw [unitInterval.coe_symm_eq]; linarith)
      (by rw [unitInterval.coe_symm_eq]; linarith) z : ℝ) = paperR b z := by
  change randomRankReal (unitInterval.symm b : ℝ) z = _
  rw [unitInterval.coe_symm_eq, paperR_eq]

/-- The two conditional atoms (15) and their probabilities for `B_b`. -/
theorem paperB_conditional_formula (b : I) (hb0 : 0 < (b : ℝ)) (hb : (b : ℝ) ≤ 1 / 2) (x : I) :
    (blockKernel (unitInterval.symm b) (randomSplit (unitInterval.symm b) (symm_half_le b hb))
        x).map (fun z : I => (z : ℝ)) =
      if (x : ℝ) ≤ 1 - b then Measure.dirac (1 - (x : ℝ))
      else ENNReal.ofReal (1 / (2 * (1 - (b : ℝ)))) •
          Measure.dirac (((x : ℝ) + b - 1) / (2 * (1 - b))) +
        ENNReal.ofReal ((1 - 2 * (b : ℝ)) / (2 * (1 - b))) •
          Measure.dirac ((1 - (b : ℝ) - (1 - 2 * b) * x) / (2 * (1 - b))) := by
  have h := familyB_conditional_formula (unitInterval.symm b) (symm_half_le b hb)
    (by rw [unitInterval.coe_symm_eq]; linarith) x
  rw [h]
  have hle : (x ≤ unitInterval.symm b) ↔ (x : ℝ) ≤ 1 - b := by
    rw [← Subtype.coe_le_coe, unitInterval.coe_symm_eq]
  by_cases hx : (x : ℝ) ≤ 1 - b
  · rw [ite_eq_left (hle.mpr hx), ite_eq_left hx]
  · rw [ite_eq_right (fun h' => hx (hle.mp h')), ite_eq_right hx, unitInterval.coe_symm_eq]
    congr 3
    · ring
    · ring
    · ring

/-! ## The parameters `n_b` and `Λ` -/

theorem one_sub_bijOn : BijOn (fun b : ℝ => 1 - b) (Ioo 0 (1 / 2)) (Ioo (1 / 2) 1) := by
  refine ⟨fun b hb => ⟨by linarith [hb.2], by linarith [hb.1]⟩, ?_, ?_⟩
  · intro x _ y _ h
    simp only at h
    linarith
  · intro a ha
    exact ⟨1 - a, ⟨by linarith [ha.2], by linarith [ha.1]⟩, by simp⟩

/-- Section 4.3: `b ↦ n_b` increases bijectively from `(0,1/2)` onto `(-1,-7/8)`. -/
theorem paperNB_bijOn :
    StrictMonoOn paperNB (Ioo 0 (1 / 2)) ∧ BijOn paperNB (Ioo 0 (1 / 2)) (Ioo (-1 : ℝ) (-7 / 8)) := by
  have hfun : paperNB = transposeParam ∘ (fun t : ℝ => 1 - t) := funext paperNB_eq
  obtain ⟨hmono, hbij⟩ := transposeParam_bijOn
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    rw [paperNB_eq, paperNB_eq]
    exact hmono ⟨by linarith [hy.2], by linarith [hy.1]⟩ ⟨by linarith [hx.2], by linarith [hx.1]⟩
      (by linarith)
  · rw [hfun]
    exact hbij.comp one_sub_bijOn

/-- (22): `Λ(n_b) = ν(B_b)` on the parametric branch. -/
theorem Lambda_paperNB (b : ℝ) (hb0 : 0 < b) (hb : b < 1 / 2) : Lambda (paperNB b) = paperNuB b := by
  have h := Lambda_transposeParam ⟨1 - b, by linarith, by linarith⟩
    (by change (1 / 2 : ℝ) < 1 - b; linarith) (by change 1 - b < (1 : ℝ); linarith)
  change Lambda (transposeParam (1 - b)) = nuB (1 - b) at h
  rw [paperNB_eq, paperNuB_eq, h]

theorem paper_Lambda_junction : paperNB (1 / 2) = -7 / 8 ∧ paperNuB (1 / 2) = -5 / 8 := by
  norm_num [paperNB, paperNuB]

/-! ## Derivatives of `Υ` along the parametric branch -/

/-- Proof of Corollary 4.5: `∂_b Υ(e_b) = b²(2-3b)(3b²-8b+6)/(4(1-b)³) > 0`. -/
theorem hasDerivAt_paperUps (b : ℝ) (hb0 : 0 < b) (hb : b < 1 / 2) :
    HasDerivAt (fun t : ℝ => etaGap (paperEtaB t))
      (b ^ 2 * (2 - 3 * b) * (3 * b ^ 2 - 8 * b + 6) / (4 * (1 - b) ^ 3)) b := by
  have h0 : 1 - b ≠ 0 := by intro h; linarith
  have hfun : (fun t : ℝ => etaGap (paperEtaB t)) =
      (fun t : ℝ => etaGap (etaB t)) ∘ (fun t : ℝ => 1 - t) := by
    funext t
    simp only [Function.comp, paperEtaB_eq]
  have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) b := by
    simpa using (hasDerivAt_id b).const_sub 1
  have h := (hasDerivAt_etaGap_randomized (1 - b) (by linarith) (by linarith)).comp b h1
  rw [hfun]
  convert h using 1
  field_simp
  ring

theorem paperUps_deriv_pos (b : ℝ) (hb0 : 0 < b) (hb : b < 1 / 2) :
    0 < b ^ 2 * (2 - 3 * b) * (3 * b ^ 2 - 8 * b + 6) / (4 * (1 - b) ^ 3) := by
  have h1 : 0 < 1 - b := by linarith
  have h2 : 0 < 2 - 3 * b := by linarith
  have hq : 0 < 3 * b ^ 2 - 8 * b + 6 := by nlinarith [sq_nonneg (3 * b - 4)]
  apply div_pos
  · exact mul_pos (mul_pos (pow_pos hb0 2) h2) hq
  · exact mul_pos (by norm_num) (pow_pos h1 3)

/-- Proof of Corollary 4.6: `Υ'(e_b) = (2-3b)/(2-b) ∈ (1/3,1)`. -/
theorem hasDerivAt_etaGap_paper (b : ℝ) (hb0 : 0 < b) (hb : b < 1 / 2) :
    HasDerivAt etaGap ((2 - 3 * b) / (2 - b)) (paperEtaB b) ∧
      (2 - 3 * b) / (2 - b) ∈ Ioo (1 / 3 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · have h := hasDerivAt_etaGap_param (1 - b) (by linarith) (by linarith)
    rw [paperEtaB_eq]
    convert h using 1
    congr 1 <;> ring
  · have h2 : 0 < 2 - b := by linarith
    constructor
    · rw [lt_div_iff₀ h2]; linarith
    · rw [div_lt_one h2]; linarith

/-- (6): the parametric formula for `Υ(e_b)`. -/
theorem etaGap_paperEtaB (b : ℝ) (hb0 : 0 < b) (hb : b < 1 / 2) :
    etaGap (paperEtaB b) = paperUpsB b := by
  have h := etaGap_randomized_formula ⟨1 - b, by linarith, by linarith⟩
    (by change (1 / 2 : ℝ) < 1 - b; linarith)
  change etaGap (etaB (1 - b)) = (1 - (1 - b)) ^ 3 * (6 * (1 - b) ^ 2 + 3 * (1 - b) - 1) /
    (8 * (1 - b) ^ 2) at h
  rw [paperEtaB_eq, h, paperUpsB]
  congr 1
  ring

/-! ## The family `D_c` -/

/-- The manuscript's `D_c`: the copula of `(X, ζ_c(X))` for the rank map `ζ_c` centred at
`1-c`, so that `D_0 = W`, `D_1 = M`, and the support has its kink at `u = c`. -/
def paperD (c : I) : Copula 2 := rhoFullFamily (unitInterval.symm c)

/-- Lemma 3.1, displayed formulas (12). -/
theorem paperD_values (c : I) :
    (paperD c).spearmanRho =
        (if (c : ℝ) ≤ 1 / 2 then 8 * (c : ℝ) ^ 3 - 1 else 1 - 8 * (1 - (c : ℝ)) ^ 3) ∧
      blestNu (paperD c) =
        (if (c : ℝ) ≤ 1 / 2 then 16 * (c : ℝ) ^ 3 - 12 * (c : ℝ) ^ 4 - 1
         else 1 - 12 * (1 - (c : ℝ)) ^ 4) := by
  obtain ⟨h1, h2⟩ := rhoFullFamily_values (unitInterval.symm c)
  rw [unitInterval.coe_symm_eq] at h1 h2
  rw [paperD, h1, h2]
  constructor
  · split_ifs with h h'
    · have hc : (c : ℝ) = 1 / 2 := by linarith
      rw [hc]; norm_num
    · ring
    · ring
    · exfalso; linarith
  · split_ifs with h h'
    · have hc : (c : ℝ) = 1 / 2 := by linarith
      rw [hc]; norm_num
    · ring
    · ring
    · exfalso; linarith

/-- Lemma 3.1: `c ↦ ρ(D_c)` is strictly increasing. -/
theorem paperD_strictMono : StrictMono (fun c : I => (paperD c).spearmanRho) := by
  intro v w h
  exact rhoFullFamily_parameter_strictAnti ((symm_lt_symm_iff v w).mpr h)

/-- Lemma 3.1: `c ↦ ρ(D_c)` is a bijection of `[0,1]` onto `[-1,1]`. -/
theorem paperD_parameter_exists_unique (r : ℝ) (hr : r ∈ Icc (-1 : ℝ) 1) :
    ∃! c : I, (paperD c).spearmanRho = r := by
  obtain ⟨c0, hc0, huniq⟩ := rhoFullFamily_parameter_exists_unique r hr
  refine ⟨unitInterval.symm c0, ?_, ?_⟩
  · simp only [paperD, unitInterval.symm_symm]
    exact hc0
  · intro c hc
    have := huniq (unitInterval.symm c) hc
    rw [← this, unitInterval.symm_symm]

theorem paperD_parameter_range :
    Set.range (fun c : I => (paperD c).spearmanRho) = Icc (-1 : ℝ) 1 := by
  rw [← rhoFullFamily_parameter_range]
  ext r
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨unitInterval.symm c, rfl⟩
  · rintro ⟨c, rfl⟩
    refine ⟨unitInterval.symm c, ?_⟩
    simp only [paperD, unitInterval.symm_symm]

/-- Lemma 3.1: `ν(D_c) = Φ(ρ(D_c))`. -/
theorem paperD_on_boundary (c : I) :
    blestNu (paperD c) = rhoBoundary (paperD c).spearmanRho :=
  rhoFullFamily_on_boundary _

theorem paperD_one : paperD 1 = Copula.comonotonic 2 := by
  apply blest_max_unique
  · rw [(paperD_values 1).2]; norm_num
  · exact blest_comonotonic

theorem paperD_zero : paperD 0 = Copula.countermonotonic := by
  apply blest_min_unique
  · rw [(paperD_values 0).2]; norm_num
  · exact blest_countermonotonic

theorem paperD_half : paperD Copula.unitHalf = rhoFullFamily Copula.unitHalf := by
  rw [paperD, symm_half]

/-- The rank map `ζ_c` of (11), centred at `1-c`. -/
theorem paperZeta_formula (c x : I) :
    (quadraticRank (unitInterval.symm c) x : ℝ) =
      if |(x : ℝ) + c - 1| ≤ min (c : ℝ) (1 - c) then 2 * |(x : ℝ) + c - 1|
      else if 2 - 2 * (c : ℝ) ≤ x then (x : ℝ) else 1 - (x : ℝ) := by
  rw [quadraticRank_paper, unitInterval.coe_symm_eq]
  rw [show (x : ℝ) - (1 - c) = x + c - 1 by ring, sub_sub_cancel, min_comm,
    show 2 * (1 - (c : ℝ)) = 2 - 2 * c by ring]

/-- `D_c` is the copula associated with the law of `(X, ζ_c(X))`. -/
theorem paperD_graph_law (c : I) :
    (paperD c).survivalCopula.toMeasure =
      (volume : Measure I).map (fun x => ![x, quadraticRank (unitInterval.symm c) x]) :=
  rhoFullFamily_graph_law _

/-- Theorem 1.1 and its proof: `D_c` is the only copula with `ρ = ρ(D_c)` on the upper
boundary, and its survival copula is the only one on the lower boundary. -/
theorem paper_rho_upper_unique (c : I) (C : Copula 2)
    (hr : C.spearmanRho = (paperD c).spearmanRho)
    (hn : blestNu C = rhoBoundary C.spearmanRho) : C = paperD c :=
  rho_upper_unique C (paperD c) hr hn (paperD_on_boundary c)

theorem paper_rho_lower_unique (c : I) (C : Copula 2)
    (hr : C.spearmanRho = (paperD c).spearmanRho)
    (hn : blestNu C = 2 * C.spearmanRho - rhoBoundary C.spearmanRho) :
    C = (paperD c).survivalCopula := by
  apply rho_lower_unique C _ (hr.trans (Copula.spearmanRho_survivalCopula _).symm) hn
  rw [nu_survival, Copula.spearmanRho_survivalCopula, paperD_on_boundary]

/-- Corollary 3.2: the maximum `ν - ρ = 1/4` is attained only by `D_{1/2}`. -/
theorem paper_nu_rho_max_unique (C : Copula 2) (hc : blestNu C - C.spearmanRho = 1 / 4) :
    C = paperD Copula.unitHalf := by
  apply nu_rho_upper_unique C _ hc
  rw [(paperD_values _).1, (paperD_values _).2]
  norm_num [Copula.unitHalf]

theorem paper_nu_rho_min_unique (C : Copula 2) (hc : blestNu C - C.spearmanRho = -1 / 4) :
    C = (paperD Copula.unitHalf).survivalCopula := by
  apply nu_rho_lower_unique C _ hc
  rw [nu_survival, Copula.spearmanRho_survivalCopula, (paperD_values _).1, (paperD_values _).2]
  norm_num [Copula.unitHalf]

/-! ## Theorem 1.2 in the manuscript's parametrization -/

theorem cube_root_spec (e : ℝ) (he : e ∈ Icc (-3 / 4 : ℝ) 1) :
    (1 / 2 : ℝ) ≤ ((1 + e) / 2) ^ (1 / 3 : ℝ) ∧ ((1 + e) / 2) ^ (1 / 3 : ℝ) ≤ 1 ∧
      (((1 + e) / 2) ^ (1 / 3 : ℝ)) ^ 3 = (1 + e) / 2 := by
  have h0 : 0 ≤ (1 + e) / 2 := by linarith [he.1]
  have hcube : (((1 + e) / 2) ^ (1 / 3 : ℝ)) ^ 3 = (1 + e) / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
    norm_num
  have hs0 : 0 ≤ ((1 + e) / 2) ^ (1 / 3 : ℝ) := Real.rpow_nonneg h0 _
  refine ⟨?_, ?_, hcube⟩
  · by_contra h
    replace h := not_le.mp h
    have : (((1 + e) / 2) ^ (1 / 3 : ℝ)) ^ 3 < (1 / 2) ^ 3 :=
      pow_lt_pow_left₀ h hs0 (by norm_num)
    rw [hcube] at this
    linarith [he.1]
  · by_contra h
    replace h := not_le.mp h
    have : (1 : ℝ) ^ 3 < (((1 + e) / 2) ^ (1 / 3 : ℝ)) ^ 3 :=
      pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    rw [hcube] at this
    linarith [he.2]

/-- Theorem 1.2 for `η ∈ [-3/4,1]`: the unique upper extremizer is `A_w` with
`w = ((1+η)/2)^{1/3} ∈ [1/2,1]`, and the unique lower one is its transpose. -/
theorem paper_eta_graph_extremizers (e : ℝ) (he : e ∈ Icc (-3 / 4 : ℝ) 1) :
    ∃ w : I, (w : ℝ) = ((1 + e) / 2) ^ (1 / 3 : ℝ) ∧ (1 / 2 : ℝ) ≤ w ∧
      eta (paperA w) = e ∧ blestNu (paperA w) = e + etaGap e ∧
      (∀ C : Copula 2, eta C = e → blestNu C = e + etaGap e → C = paperA w) ∧
      (∀ C : Copula 2, eta C = e → blestNu C = e - etaGap e → C = (paperA w).transpose) := by
  obtain ⟨hl, hu, hcube⟩ := cube_root_spec e he
  set s := ((1 + e) / 2) ^ (1 / 3 : ℝ) with hs
  let w : I := ⟨s, by constructor <;> linarith⟩
  have hw : (w : ℝ) = s := rfl
  have heta : eta (paperA w) = e := by
    rw [eta_paperA, hw, hcube]; ring
  have hsw : ((unitInterval.symm w : I) : ℝ) ≤ 1 / 2 := by
    rw [unitInterval.coe_symm_eq, hw]; linarith
  have hetaF : eta (familyA (unitInterval.symm w)) = e := heta
  have hgap : etaGap e = blestNu (paperA w) - e := by
    have := etaGap_graph (unitInterval.symm w) hsw
    rw [hetaF] at this
    rw [this]
    rfl
  refine ⟨w, hw, by rw [hw]; exact hl, heta, by rw [hgap]; ring, ?_, ?_⟩
  · intro C hC hn
    apply graph_upper_unique C _ hsw
    · rw [hC]; exact hetaF.symm
    · rw [hn, hgap]; change e + (blestNu (paperA w) - e) = blestNu (paperA w); ring
  · intro C hC hn
    apply graph_lower_unique C _ hsw
    · rw [hC]; exact hetaF.symm
    · rw [hn, hgap, hetaF]; change e - (blestNu (paperA w) - e) = 2 * e - blestNu (paperA w); ring

/-- Theorem 1.2 for `η ∈ (-1,-3/4)`: the unique upper extremizer is `B_b` with `e_b = η` and
`b ∈ (0,1/2)`, and the unique lower one is its transpose. -/
theorem paper_eta_random_extremizers (e : ℝ) (he : e ∈ Ioo (-1 : ℝ) (-3 / 4)) :
    ∃ b : I, ∃ hb : (b : ℝ) < 1 / 2, 0 < (b : ℝ) ∧ paperEtaB b = e ∧
      eta (paperB b hb.le) = e ∧ blestNu (paperB b hb.le) = e + etaGap e ∧
      (∀ C : Copula 2, eta C = e → blestNu C = e + etaGap e → C = paperB b hb.le) ∧
      (∀ C : Copula 2, eta C = e → blestNu C = e - etaGap e →
        C = (paperB b hb.le).transpose) := by
  obtain ⟨a, ha, ha1, hae⟩ := randomized_parameter_exists_open e he
  have hb : ((unitInterval.symm a : I) : ℝ) < 1 / 2 := by
    rw [unitInterval.coe_symm_eq]; linarith
  have hB : paperB (unitInterval.symm a) hb.le = familyB a ha.le := paperB_symm a ha.le hb.le
  have hgap : etaGap e = nuB a - e := by
    rw [← hae, etaGap_randomized a ha]
  have hpe : paperEtaB (unitInterval.symm a : I) = e := by
    rw [unitInterval.coe_symm_eq, paperEtaB_eq, sub_sub_cancel, hae]
  refine ⟨unitInterval.symm a, hb, by rw [unitInterval.coe_symm_eq]; linarith, hpe, ?_, ?_, ?_, ?_⟩
  · rw [hB, eta_familyB, hae]
  · rw [hB, nu_familyB, hgap]; ring
  · intro C hC hn
    rw [hB]
    apply randomized_upper_unique C a ha ha1
    · rw [hC, hae]
    · rw [hn, hgap]; ring
  · intro C hC hn
    rw [hB]
    apply randomized_lower_unique C a ha ha1
    · rw [hC, hae]
    · rw [hn, hgap, hae]; ring

/-! ## Potentials of Propositions 4.3 and 4.4 -/

/-- `φ_w` and `ψ_w` of (18). -/
def paperPhiA (w x : ℝ) : ℝ := phiA (1 - w) x
def paperPsiA (w z : ℝ) : ℝ := psiA (1 - w) z

theorem paperPotentialsA_normalized (w : ℝ) (hw : 0 ≤ w) :
    paperPhiA w (1 - w) = 0 ∧ paperPsiA w 0 = 0 :=
  potentialsA_normalized (1 - w) (by linarith)

theorem hasDerivAt_paperPhiA (w x : ℝ) (hx : x ≠ 1 - w) :
    HasDerivAt (paperPhiA w)
      (if x ≤ 1 - w then (1 - x) * (2 * x - (3 - 2 * w) / (2 * w) * (1 - x))
       else (x + w - 1) * (2 * x - (3 - 2 * w) / (2 * w) * (x + w - 1))) x := by
  have h := hasDerivAt_phiA (1 - w) x hx
  rw [kA_paper] at h
  convert h using 1 <;> try rfl
  split_ifs <;> ring

theorem hasDerivAt_paperPsiA (w z : ℝ) (hz : z ≠ w) :
    HasDerivAt (paperPsiA w)
      (if z ≤ w then (z + 1 - w) * (z + 1 - w - 2 * ((3 - 2 * w) / (2 * w)) * z)
       else (1 - z) * (1 - z - 2 * ((3 - 2 * w) / (2 * w)) * z)) z := by
  have h := hasDerivAt_psiA (1 - w) z (by rwa [sub_sub_cancel])
  rw [kA_paper, sub_sub_cancel] at h
  convert h using 1 <;> try rfl
  split_ifs <;> ring

/-- Proposition 4.3 (inequality) with `κ_w = (3-2w)/(2w)`, `w ∈ [1/2,1]`. -/
theorem paper_dualA (w x z : ℝ) (hw : 1 / 2 ≤ w) (hw1 : w ≤ 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    cost ((3 - 2 * w) / (2 * w)) x z ≤ paperPhiA w x + paperPsiA w z := by
  rw [← kA_paper]
  exact dualA (1 - w) x z (by linarith) (by linarith) hx hz

/-- Proposition 4.3 (equality set): `S_w`, plus `[1/2,1] × {1/2}` when `w = 1/2`. -/
theorem paper_contactA (w x z : ℝ) (hw : 1 / 2 ≤ w) (hw1 : w < 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    paperPhiA w x + paperPsiA w z - cost ((3 - 2 * w) / (2 * w)) x z = 0 ↔
      (x ≤ 1 - w ∧ z = 1 - x) ∨ (1 - w ≤ x ∧ z = x + w - 1) ∨
        (w = 1 / 2 ∧ 1 / 2 ≤ x ∧ z = 1 / 2) := by
  rw [← kA_paper]
  unfold paperPhiA paperPsiA
  rw [graph_contact_complete (1 - w) x z (by linarith) (by linarith) hx hz]
  unfold contactA
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h.1, by rw [h.2]; ring⟩)
    · exact Or.inr (Or.inr ⟨by linarith [h.1], by linarith [h.1, h.2.1], h.2.2⟩)
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h.1, by rw [h.2]; ring⟩)
    · exact Or.inr (Or.inr ⟨by linarith [h.1], by linarith [h.1, h.2.1], h.2.2⟩)

/-- `φ_b` and `ψ_b` of (20). -/
def paperPhiB (b x : ℝ) : ℝ := phiB (1 - b) x
def paperPsiB (b z : ℝ) : ℝ := psiB (1 - b) z

theorem paperPotentialsB_normalized (b : ℝ) (hb0 : 0 < b) (hb : b < 1 / 2) :
    paperPhiB b (1 - b) = 0 ∧ paperPsiB b 0 = 0 :=
  potentialsB_normalized (1 - b) (by linarith) (by linarith)

theorem hasDerivAt_paperPhiB (b x : ℝ) (hb : b ≠ 1) (hx : x ≠ 1 - b) :
    HasDerivAt (paperPhiB b)
      (if x ≤ 1 - b then (1 - x) * (2 * x - 2 * (1 - b) / b * (1 - x))
       else ((x + b - 1) / (2 * (1 - b))) *
         (2 * x - 2 * (1 - b) / b * ((x + b - 1) / (2 * (1 - b))))) x := by
  have h := hasDerivAt_phiB (1 - b) x (sub_ne_zero.mpr (Ne.symm hb)) hx
  rw [kB_paper] at h
  convert h using 1 <;> try rfl
  split_ifs <;> ring

theorem hasDerivAt_paperPsiB (b z : ℝ) (hzc : z ≠ b / (2 * (1 - b))) (hzb : z ≠ b) :
    HasDerivAt (paperPsiB b) (paperR b z * (paperR b z - 2 * (2 * (1 - b) / b) * z)) z := by
  have h := hasDerivAt_psiB (1 - b) z (by rwa [cutB_paper]) (by rwa [sub_sub_cancel])
  rw [kB_paper, paperR_eq] at h
  exact h

/-- Proposition 4.4 (inequality) with `κ_b = 2(1-b)/b`, `b ∈ (0,1/2)`. -/
theorem paper_dualB (b x z : ℝ) (hb0 : 0 < b) (hb : b < 1 / 2)
    (hx : x ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    cost (2 * (1 - b) / b) x z ≤ paperPhiB b x + paperPsiB b z := by
  rw [← kB_paper]
  exact dualB (1 - b) x z (by linarith) (by linarith) hx hz

/-- Proposition 4.4 (equality set): exactly the graph `x = R_b(z)`. -/
theorem paper_contactB (b x z : ℝ) (hb0 : 0 < b) (hb : b < 1 / 2)
    (hx : x ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    paperPhiB b x + paperPsiB b z - cost (2 * (1 - b) / b) x z = 0 ↔ x = paperR b z := by
  rw [← kB_paper, ← paperR_eq]
  exact randomized_contact_complete (1 - b) x z (by linarith) (by linarith) hx hz

/-! ## Corollaries 4.5 and 4.6 and Remark 4.7 -/

def threeQuarter : I := ⟨3 / 4, by norm_num⟩

theorem symm_threeQuarter : unitInterval.symm threeQuarter = quarter := by
  apply Subtype.ext
  rw [unitInterval.coe_symm_eq]
  norm_num [threeQuarter, quarter]

theorem paperA_threeQuarter : paperA threeQuarter = familyA quarter := by
  rw [paperA, symm_threeQuarter]

/-- Corollary 4.5: values of `A_{3/4}`. -/
theorem paperA_threeQuarter_values :
    eta (paperA threeQuarter) = -5 / 32 ∧ blestNu (paperA threeQuarter) = 7 / 128 := by
  rw [paperA_threeQuarter]
  exact quarter_values

/-- Corollary 4.5: `|ν - η| = 27/128` exactly for `A_{3/4}` and `A_{3/4}ᵀ`. -/
theorem paper_asymmetry_eq_iff (C : Copula 2) :
    |blestNu C - eta C| = 27 / 128 ↔ C = paperA threeQuarter ∨ C = (paperA threeQuarter).transpose := by
  rw [paperA_threeQuarter]
  exact asymmetry_eq_iff C

theorem paper_transposition_eq_iff (C : Copula 2) :
    |blestNu C - blestNu C.transpose| = 27 / 64 ↔
      C = paperA threeQuarter ∨ C = (paperA threeQuarter).transpose := by
  rw [paperA_threeQuarter]
  exact transposition_eq_iff C

/-- Corollary 4.6 for `n ≥ -7/8`: the maximizer is `A_wᵀ` with `w = ((1+n)/2)^{1/4}`. -/
theorem paper_nu_transpose_max_A (n : ℝ) (hn : n ∈ Icc (-7 / 8 : ℝ) 1) :
    ∃ w : I, (w : ℝ) = ((1 + n) / 2) ^ (1 / 4 : ℝ) ∧ (1 / 2 : ℝ) ≤ w ∧
      blestNu (paperA w).transpose = n ∧ blestNu (paperA w) = Lambda n ∧
      ∀ C : Copula 2, blestNu C = n → blestNu C.transpose = Lambda n →
        C = (paperA w).transpose := by
  obtain ⟨w0, hw0, hw0h, h1, h2, h3⟩ := nu_transpose_max_familyA n hn
  refine ⟨unitInterval.symm w0, by rw [unitInterval.coe_symm_eq, hw0]; ring,
    by rw [unitInterval.coe_symm_eq]; linarith, ?_, ?_, ?_⟩
  · rw [paperA_symm]; exact h1
  · rw [paperA_symm]; exact h2
  · rw [paperA_symm]; exact h3

/-- Corollary 4.6 for `n < -7/8`: the maximizer is `B_bᵀ` with `n_b = n`. -/
theorem paper_nu_transpose_max_B (n : ℝ) (hn : n ∈ Ioo (-1 : ℝ) (-7 / 8)) :
    ∃ b : I, ∃ hb : (b : ℝ) < 1 / 2, 0 < (b : ℝ) ∧ paperNB b = n ∧
      blestNu (paperB b hb.le).transpose = n ∧ blestNu (paperB b hb.le) = Lambda n ∧
      ∀ C : Copula 2, blestNu C = n → blestNu C.transpose = Lambda n →
        C = (paperB b hb.le).transpose := by
  obtain ⟨a, ha, ha1, hpa, h1, h2, h3⟩ := nu_transpose_max_familyB n hn
  have hb : ((unitInterval.symm a : I) : ℝ) < 1 / 2 := by
    rw [unitInterval.coe_symm_eq]; linarith
  have hB : paperB (unitInterval.symm a) hb.le = familyB a ha.le := paperB_symm a ha.le hb.le
  refine ⟨unitInterval.symm a, hb, by rw [unitInterval.coe_symm_eq]; linarith, ?_, ?_, ?_, ?_⟩
  · rw [unitInterval.coe_symm_eq, paperNB_eq, sub_sub_cancel, hpa]
  · rw [hB]; exact h1
  · rw [hB]; exact h2
  · rw [hB]; exact h3

/-- Corollary 4.6: the maximizers of `νᵀ` at given `ν > -1` are the transposes `A_wᵀ`
(`w ∈ [1/2,1]`) or `B_bᵀ` (`b ∈ (0,1/2)`), the minimizers the families themselves. -/
theorem paper_nu_transpose_extremizer_cases (C : Copula 2) (hn : -1 < blestNu C) :
    (blestNu C.transpose = Lambda (blestNu C) →
      (∃ w : I, (1 / 2 : ℝ) ≤ w ∧ C = (paperA w).transpose) ∨
        (∃ b : I, ∃ hb : (b : ℝ) < 1 / 2, 0 < (b : ℝ) ∧ C = (paperB b hb.le).transpose)) ∧
    (blestNu C.transpose = LambdaInv (blestNu C) →
      (∃ w : I, (1 / 2 : ℝ) ≤ w ∧ C = paperA w) ∨
        (∃ b : I, ∃ hb : (b : ℝ) < 1 / 2, 0 < (b : ℝ) ∧ C = paperB b hb.le)) := by
  constructor
  · intro hC
    rcases nu_transpose_max_cases C hn hC with ⟨w, hw, rfl⟩ | ⟨a, ha, ha1, rfl⟩
    · refine Or.inl ⟨unitInterval.symm w, by rw [unitInterval.coe_symm_eq]; linarith, ?_⟩
      rw [paperA_symm]
    · have hb : ((unitInterval.symm a : I) : ℝ) < 1 / 2 := by
        rw [unitInterval.coe_symm_eq]; linarith
      refine Or.inr ⟨unitInterval.symm a, hb, by rw [unitInterval.coe_symm_eq]; linarith, ?_⟩
      rw [paperB_symm a ha.le hb.le]
  · intro hC
    rcases nu_transpose_min_cases C hn hC with ⟨w, hw, rfl⟩ | ⟨a, ha, ha1, rfl⟩
    · refine Or.inl ⟨unitInterval.symm w, by rw [unitInterval.coe_symm_eq]; linarith, ?_⟩
      rw [paperA_symm]
    · have hb : ((unitInterval.symm a : I) : ℝ) < 1 / 2 := by
        rw [unitInterval.coe_symm_eq]; linarith
      refine Or.inr ⟨unitInterval.symm a, hb, by rw [unitInterval.coe_symm_eq]; linarith, ?_⟩
      rw [paperB_symm a ha.le hb.le]

/-- Remark 4.7(a): for `w ∈ (0,1/2)`, `A_w` lies strictly below the upper boundary. -/
theorem paperA_not_extremal (w : I) (hw0 : 0 < (w : ℝ)) (hw : (w : ℝ) < 1 / 2) :
    eta (paperA w) ∈ Ioo (-1 : ℝ) (-3 / 4) ∧
      blestNu (paperA w) < eta (paperA w) + etaGap (eta (paperA w)) :=
  familyA_not_extremal (unitInterval.symm w) (by rw [unitInterval.coe_symm_eq]; linarith)
    (by rw [unitInterval.coe_symm_eq]; linarith)

/-- Remark 4.7(b): the unique maximizer of `ρ - η` is `A_{3/4}^⊥`, the shuffle of `M` that
is countermonotone on `[0,3/4]` and comonotone on `[3/4,1]`; the minimizer is
`(A_{3/4}ᵀ)^⊥`, its survival copula. -/
theorem paper_rho_eta_extremizers :
    (paperA threeQuarter).reflect {1} = shuffleQuarter ∧
      (paperA threeQuarter).transpose.reflect {1} =
        ((paperA threeQuarter).reflect {1}).survivalCopula ∧
      (∀ C : Copula 2, C.spearmanRho - eta C = 27 / 128 → C = (paperA threeQuarter).reflect {1}) ∧
      (∀ C : Copula 2, C.spearmanRho - eta C = -27 / 128 →
        C = (paperA threeQuarter).transpose.reflect {1}) := by
  rw [paperA_threeQuarter]
  exact ⟨rho_eta_maximizer_shuffle, rho_eta_minimizer_survival, rho_eta_upper_unique,
    rho_eta_lower_unique⟩

/-! ## Values printed above the panels of Figures 2 and 3 -/

/-- Figure 2 (columns `D_{1/4}`, `D_{1/2}`, `D_{3/4}`) and Figure 3 (columns `B_{1/4}`,
`A_{1/2} = B_{1/2}`, `A_{7/8}`), each with the value in the bottom row, and the branch
probabilities `2/3` and `1/3` of `B_{1/4}`. The decimals printed for `B_{1/4}` and `A_{7/8}` are roundings
of these fractions. -/
theorem paper_figure_panel_values :
    ((paperD ⟨1 / 4, by norm_num⟩).spearmanRho = -7 / 8 ∧
      blestNu (paperD ⟨1 / 4, by norm_num⟩) = -51 / 64 ∧
      blestNu (paperD ⟨1 / 4, by norm_num⟩).survivalCopula = -61 / 64) ∧
    ((paperD ⟨1 / 2, by norm_num⟩).spearmanRho = 0 ∧
      blestNu (paperD ⟨1 / 2, by norm_num⟩) = 1 / 4 ∧
      blestNu (paperD ⟨1 / 2, by norm_num⟩).survivalCopula = -1 / 4) ∧
    ((paperD ⟨3 / 4, by norm_num⟩).spearmanRho = 7 / 8 ∧
      blestNu (paperD ⟨3 / 4, by norm_num⟩) = 61 / 64 ∧
      blestNu (paperD ⟨3 / 4, by norm_num⟩).survivalCopula = 51 / 64) ∧
    (eta (paperB ⟨1 / 4, by norm_num⟩ (by norm_num)) = -2257 / 2304 ∧
      blestNu (paperB ⟨1 / 4, by norm_num⟩ (by norm_num)) = -185 / 192 ∧
      blestNu (paperB ⟨1 / 4, by norm_num⟩ (by norm_num)).transpose = -1147 / 1152) ∧
    (eta (paperA ⟨1 / 2, by norm_num⟩) = -3 / 4 ∧
      blestNu (paperA ⟨1 / 2, by norm_num⟩) = -5 / 8 ∧
      blestNu (paperA ⟨1 / 2, by norm_num⟩).transpose = -7 / 8) ∧
    (eta (paperA ⟨7 / 8, by norm_num⟩) = 87 / 256 ∧
      blestNu (paperA ⟨7 / 8, by norm_num⟩) = 1039 / 2048 ∧
      blestNu (paperA ⟨7 / 8, by norm_num⟩).transpose = 353 / 2048) ∧
    (1 / (2 * (1 - (1 / 4 : ℝ))) = 2 / 3 ∧ (1 - 2 * (1 / 4 : ℝ)) / (2 * (1 - 1 / 4)) = 1 / 3) := by
  have hD (c : I) (r n : ℝ) (hr : (paperD c).spearmanRho = r) (hn : blestNu (paperD c) = n) :
      (paperD c).spearmanRho = r ∧ blestNu (paperD c) = n ∧
        blestNu (paperD c).survivalCopula = 2 * r - n :=
    ⟨hr, hn, by rw [nu_survival, hr, hn]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by norm_num⟩
  · have h := hD ⟨1 / 4, by norm_num⟩ (-7 / 8) (-51 / 64)
      (by rw [(paperD_values _).1]; norm_num) (by rw [(paperD_values _).2]; norm_num)
    norm_num at h ⊢
    exact h
  · have h := hD ⟨1 / 2, by norm_num⟩ 0 (1 / 4)
      (by rw [(paperD_values _).1]; norm_num) (by rw [(paperD_values _).2]; norm_num)
    norm_num at h ⊢
    exact h
  · have h := hD ⟨3 / 4, by norm_num⟩ (7 / 8) (61 / 64)
      (by rw [(paperD_values _).1]; norm_num) (by rw [(paperD_values _).2]; norm_num)
    norm_num at h ⊢
    exact h
  · refine ⟨?_, ?_, ?_⟩
    · rw [eta_paperB]; norm_num [paperEtaB]
    · rw [nu_paperB]; norm_num [paperNuB]
    · rw [nu_transpose_paperB]; norm_num [paperNB]
  · refine ⟨?_, ?_, ?_⟩
    · rw [eta_paperA]; norm_num
    · rw [nu_paperA]; norm_num
    · rw [nu_transpose_paperA]; norm_num
  · refine ⟨?_, ?_, ?_⟩
    · rw [eta_paperA]; norm_num
    · rw [nu_paperA]; norm_num
    · rw [nu_transpose_paperA]; norm_num

end

end Papers.Rockel2026ExactBlest

#assert_standard_axioms Papers.Rockel2026ExactBlest.symm_lt_symm_iff
#assert_standard_axioms Papers.Rockel2026ExactBlest.symm_half
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperA_symm
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_paperA
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_paperA
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_paperA
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperA_gap
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperA_zero
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperA_one
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_paperA_strictMono
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperA_eta_range
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperT_formula
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperA_graph_law
#assert_standard_axioms Papers.Rockel2026ExactBlest.symm_half_le
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperB_symm
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperEtaB_eq
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperNuB_eq
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperNB_eq
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperUpsB_eq
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_paperB
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_paperB
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_paperB
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperB_gap
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperB_half
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperB_zero
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperEtaB_strictMonoOn
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_paperEtaB
#assert_standard_axioms Papers.Rockel2026ExactBlest.deriv_paperEtaB_pos
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperEtaB_endpoints
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperEtaB_range
#assert_standard_axioms Papers.Rockel2026ExactBlest.cutB_paper
#assert_standard_axioms Papers.Rockel2026ExactBlest.kA_paper
#assert_standard_axioms Papers.Rockel2026ExactBlest.kB_paper
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperR_eq
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperB_graph_law
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperR_formula
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperB_conditional_formula
#assert_standard_axioms Papers.Rockel2026ExactBlest.one_sub_bijOn
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperNB_bijOn
#assert_standard_axioms Papers.Rockel2026ExactBlest.Lambda_paperNB
#assert_standard_axioms Papers.Rockel2026ExactBlest.paper_Lambda_junction
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_paperUps
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperUps_deriv_pos
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_etaGap_paper
#assert_standard_axioms Papers.Rockel2026ExactBlest.etaGap_paperEtaB
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperD_values
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperD_strictMono
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperD_parameter_exists_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperD_parameter_range
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperD_on_boundary
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperD_one
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperD_zero
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperD_half
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperZeta_formula
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperD_graph_law
#assert_standard_axioms Papers.Rockel2026ExactBlest.paper_rho_upper_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.paper_rho_lower_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.paper_nu_rho_max_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.paper_nu_rho_min_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.cube_root_spec
#assert_standard_axioms Papers.Rockel2026ExactBlest.paper_eta_graph_extremizers
#assert_standard_axioms Papers.Rockel2026ExactBlest.paper_eta_random_extremizers
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperPotentialsA_normalized
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_paperPhiA
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_paperPsiA
#assert_standard_axioms Papers.Rockel2026ExactBlest.paper_dualA
#assert_standard_axioms Papers.Rockel2026ExactBlest.paper_contactA
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperPotentialsB_normalized
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_paperPhiB
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_paperPsiB
#assert_standard_axioms Papers.Rockel2026ExactBlest.paper_dualB
#assert_standard_axioms Papers.Rockel2026ExactBlest.paper_contactB
#assert_standard_axioms Papers.Rockel2026ExactBlest.symm_threeQuarter
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperA_threeQuarter
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperA_threeQuarter_values
#assert_standard_axioms Papers.Rockel2026ExactBlest.paper_asymmetry_eq_iff
#assert_standard_axioms Papers.Rockel2026ExactBlest.paper_transposition_eq_iff
#assert_standard_axioms Papers.Rockel2026ExactBlest.paper_nu_transpose_max_A
#assert_standard_axioms Papers.Rockel2026ExactBlest.paper_nu_transpose_max_B
#assert_standard_axioms Papers.Rockel2026ExactBlest.paper_nu_transpose_extremizer_cases
#assert_standard_axioms Papers.Rockel2026ExactBlest.paperA_not_extremal
#assert_standard_axioms Papers.Rockel2026ExactBlest.paper_rho_eta_extremizers
#assert_standard_axioms Papers.Rockel2026ExactBlest.paper_figure_panel_values
