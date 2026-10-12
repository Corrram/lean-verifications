import Papers.Rockel2026ExactBlest.ArticleDocument

/-! Exact intermediate identities printed in the original article. These are
separate checks of the displayed factorizations, beyond the established results. -/
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
open Papers.Rockel2026XiBlest

namespace Papers.Rockel2026ExactBlest.ArticleOriginalProof
noncomputable section
set_option maxHeartbeats 4000000

/-- Both equalities in the article's definition of the symmetrized coefficient. -/
theorem eta_cdf_integral (C : Copula 2) :
    eta C = 12*(∫ v : I, ∫ u : I, (2-(u : ℝ)-(v : ℝ))*C.cdf ![u,v])-2 := by
  let f : I × I → ℝ := fun p => (1-(p.1 : ℝ))*C.cdf ![p.1,p.2]
  let g : I × I → ℝ := fun p => (1-(p.2 : ℝ))*C.cdf ![p.1,p.2]
  have hf : Integrable f ((volume : Measure I).prod volume) :=
    (show Continuous f by unfold f; fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hg : Integrable g ((volume : Measure I).prod volume) :=
    (show Continuous g by unfold g; fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have ht : blestNu C.transpose = 24*(∫ u : I, ∫ v : I, g (u,v))-2 := by
    rw [blest_integral_formula]
    simp only [Copula.cdf_transpose, g]
  have he : (fun p : I × I => (2-(p.1 : ℝ)-(p.2 : ℝ))*C.cdf ![p.1,p.2]) =
      f+g := by funext p; dsimp [f,g]; ring
  rw [eta, blest_integral_formula C, ht]
  change (24*(∫ v : I, ∫ u : I, f (u,v))-2 +
      (24*(∫ u : I, ∫ v : I, g (u,v))-2))/2 = _
  have hi : (∫ v : I, ∫ u : I, (2-(u : ℝ)-(v : ℝ))*C.cdf ![u,v]) =
      (∫ p, f p ∂((volume : Measure I).prod volume)) +
      (∫ p, g p ∂((volume : Measure I).prod volume)) := by
    calc
      _ = ∫ p, (f+g) p ∂((volume : Measure I).prod volume) := by
        simpa only [← he] using (integral_prod_symm _ (hf.add hg)).symm
      _ = _ := integral_add hf hg
  rw [← integral_prod_symm _ hf, ← integral_prod _ hg, hi]
  ring

/-- Lemma 2.1 in the reflected coordinates used by the article. -/
theorem coupling_nu_moment (C : Copula 2) :
    blestNu C = 12*(∫ y, (y 0 : ℝ)^2*(y 1 : ℝ) ∂C.survivalCopula.toMeasure)-2 := by
  simpa [cost] using support_moment_survival C 0

theorem coupling_rho_moment (C : Copula 2) :
    C.spearmanRho = 12*(∫ y, (y 0 : ℝ)*(y 1 : ℝ) ∂C.survivalCopula.toMeasure)-3 := by
  rw [← Copula.spearmanRho_survivalCopula C]
  rfl

theorem coupling_transpose_moment (C : Copula 2) :
    blestNu C.transpose = 12*(∫ y, (y 0 : ℝ)*(y 1 : ℝ)^2 ∂C.survivalCopula.toMeasure)-2 := by
  rw [coupling_nu_moment, ← Copula.transpose_survivalCopula,
    C.survivalCopula.integral_transpose _ (by fun_prop)]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem coupling_eta_moment (C : Copula 2) :
    eta C = 6*(∫ y, (y 0 : ℝ)*(y 1 : ℝ)*((y 0 : ℝ)+(y 1 : ℝ))
      ∂C.survivalCopula.toMeasure)-2 := by
  rw [eta, coupling_nu_moment, coupling_transpose_moment]
  have hf : (fun y : Fin 2 → I => (y 0 : ℝ)*(y 1 : ℝ)*((y 0 : ℝ)+(y 1 : ℝ))) =
      fun y => (y 0 : ℝ)^2*(y 1 : ℝ)+(y 0 : ℝ)*(y 1 : ℝ)^2 := by funext y; ring
  rw [hf, integral_add]
  · ring
  all_goals exact Copula.integrable_continuous_cube _ (by fun_prop)

theorem rho_support_moment (C : Copula 2) (lam : ℝ) :
    blestNu C-lam*C.spearmanRho =
      12*(∫ y, ((y 0 : ℝ)^2-lam*(y 0 : ℝ))*(y 1 : ℝ)
        ∂C.survivalCopula.toMeasure)-2+3*lam := by
  rw [coupling_nu_moment, coupling_rho_moment]
  simp_rw [sub_mul, mul_assoc lam]
  rw [integral_sub, integral_const_mul]
  · ring
  all_goals exact Copula.integrable_continuous_cube _ (by fun_prop)

def deltaA (w x z : ℝ) : ℝ :=
  paperPhiA w x + paperPsiA w z - cost ((3 - 2*w)/(2*w)) x z

def deltaB (b x z : ℝ) : ℝ :=
  paperPhiB b x + paperPsiB b z - cost (2*(1-b)/b) x z

/-- The paper's two branches, with its parameter rather than the library's complement. -/
theorem branch_sum (b x : ℝ) (hb1 : b ≠ 1) :
    (x+b-1)/(2*(1-b)) + (1-b-(1-2*b)*x)/(2*(1-b)) =
      2*x/(2*(1-b)/b) := by
  field_simp
  ring

theorem branch_derivatives (b x : ℝ) (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    ((x+b-1)/(2*(1-b))) * (2*x-2*(1-b)/b*((x+b-1)/(2*(1-b)))) =
    ((1-b-(1-2*b)*x)/(2*(1-b))) *
      (2*x-2*(1-b)/b*((1-b-(1-2*b)*x)/(2*(1-b)))) := by
  field_simp
  ring

theorem paper_graph_support (C : Copula 2) (w : I) (hw : (1/2 : ℝ) ≤ w) :
    (1+(3-2*(w : ℝ))/(2*w))*blestNu C - 2*((3-2*(w : ℝ))/(2*w))*eta C ≤
    (1+(3-2*(w : ℝ))/(2*w))*blestNu (paperA w) -
      2*((3-2*(w : ℝ))/(2*w))*eta (paperA w) := by
  have h := graph_support C (unitInterval.symm w)
    (by rw [unitInterval.coe_symm_eq]; linarith)
  simpa only [unitInterval.coe_symm_eq, kA_paper, paperA] using h

private theorem cost_derivative_x (k x z : ℝ) :
    HasDerivAt (fun t => cost k t z) (2*x*z-k*z^2) x := by
  convert (((hasDerivAt_id x).pow 2).mul_const z).sub
    ((hasDerivAt_id x).const_mul (k*z^2)) using 1
  · funext t; dsimp [cost]; ring
  · dsimp; ring

private theorem cost_derivative_z (k x z : ℝ) :
    HasDerivAt (fun t => cost k x t) (x^2-2*k*x*z) z := by
  convert ((hasDerivAt_id z).const_mul (x^2)).sub
    (((hasDerivAt_id z).pow 2).const_mul (k*x)) using 1
  · funext t; dsimp [cost]
  · dsimp; ring

/-- The displayed derivative on the third rectangle of Proposition 4.3. -/
theorem graph_derivative_00 (w x z : ℝ) (hw : w ≠ 0) (hx : x < 1-w) :
    HasDerivAt (fun t => deltaA w t z)
      ((x+z-1)*((3-2*w)*z-(3+2*w)*x+3-2*w)/(2*w)) x := by
  have h := ((hasDerivAt_paperPhiA w x (ne_of_lt hx)).add_const (paperPsiA w z)).sub
    (cost_derivative_x ((3-2*w)/(2*w)) x z)
  simp only [ite_eq_left hx.le] at h
  convert h using 1
  · rfl
  · field_simp; ring

theorem graph_derivative_00_nonpos (w x z : ℝ) (hw : 1/2 ≤ w) (hw1 : w ≤ 1)
    (hx : x ≤ 1-w) (hz0 : 0 ≤ z) (hz : z ≤ w) :
    (x+z-1)*((3-2*w)*z-(3+2*w)*x+3-2*w)/(2*w) ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg _ (by linarith)
  apply mul_nonpos_of_nonpos_of_nonneg (by linarith)
  nlinarith [mul_nonneg (show 0 ≤ 3-2*w by linarith) hz0,
    mul_nonneg (show 0 ≤ 3+2*w by linarith) (sub_nonneg.mpr hx),
    mul_nonneg (show 0 ≤ w by linarith) (show 0 ≤ 2*w-1 by linarith)]

/-- The displayed derivative along the edge x = 1-w. -/
theorem graph_edge_derivative_z (w z : ℝ) (hw : w ≠ 0) (hz : z < w) :
    HasDerivAt (fun t => deltaA w (1-w) t) (-(1-w)*z*(3*z-2*w)/w) z := by
  have h := ((hasDerivAt_paperPsiA w z (ne_of_lt hz)).const_add
    (paperPhiA w (1-w))).sub (cost_derivative_z ((3-2*w)/(2*w)) (1-w) z)
  simp only [ite_eq_left hz.le] at h
  convert h using 1
  · rfl
  · field_simp; ring

/-- The displayed derivative on the fourth rectangle of Proposition 4.3. -/
theorem graph_derivative_11 (w x z : ℝ) (hw : w ≠ 0) (hz : w < z) :
    HasDerivAt (fun t => deltaA w x t)
      ((x+z-1)*((3-w)*z-w*x-w)/w) z := by
  have h := ((hasDerivAt_paperPsiA w z (ne_of_gt hz)).const_add (paperPhiA w x)).sub
    (cost_derivative_z ((3-2*w)/(2*w)) x z)
  simp only [ite_eq_right (not_le.mpr hz)] at h
  convert h using 1
  · rfl
  · field_simp; ring

theorem graph_derivative_11_nonneg (w x z : ℝ) (hw : 1/2 ≤ w) (hw1 : w ≤ 1)
    (hx : 1-w ≤ x) (hx1 : x ≤ 1) (hz : w ≤ z) :
    0 ≤ (x+z-1)*((3-w)*z-w*x-w)/w := by
  apply div_nonneg _ (by linarith)
  apply mul_nonneg (by linarith)
  nlinarith [mul_nonneg (show 0 ≤ 3-w by linarith) (sub_nonneg.mpr hz),
    mul_nonneg (show 0 ≤ w by linarith) (show 0 ≤ 2-w-x by linarith)]

theorem graph_edge_derivative_x (w x : ℝ) (hw : w ≠ 0) (hx : 1-w < x) :
    HasDerivAt (fun t => deltaA w t w)
      ((1-x)*(2*w-1)*(3-2*w-3*x)/(2*w)) x := by
  have h := ((hasDerivAt_paperPhiA w x (ne_of_gt hx)).add_const (paperPsiA w w)).sub
    (cost_derivative_x ((3-2*w)/(2*w)) x w)
  simp only [ite_eq_right (not_le.mpr hx)] at h
  convert h using 1
  · rfl
  · field_simp; ring

/-- The exact x derivative printed for the two lower-left rectangles. -/
theorem random_derivative_low_x (b x z : ℝ) (hb0 : b ≠ 0) (hb1 : b ≠ 1)
    (hx : x < 1-b) :
    HasDerivAt (fun t => deltaB b t z)
      (-2*(1-x-z)*((1-b)*(1+z)-x)/b) x := by
  have h := ((hasDerivAt_paperPhiB b x hb1 (ne_of_lt hx)).add_const (paperPsiB b z)).sub
    (cost_derivative_x (2*(1-b)/b) x z)
  simp only [ite_eq_left hx.le] at h
  convert h using 1
  · rfl
  · field_simp; ring

theorem random_derivative_low_x_nonpos (b x z : ℝ) (hb0 : 0 < b) (hb : b < 1/2)
    (hx : x ≤ 1-b) (hz0 : 0 ≤ z) (hz : z ≤ b) :
    -2*(1-x-z)*((1-b)*(1+z)-x)/b ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg _ hb0.le
  apply mul_nonpos_of_nonpos_of_nonneg
  · nlinarith
  · nlinarith [mul_nonneg (show 0 ≤ 1-b by linarith) hz0]

private theorem random_cut_lt (b : ℝ) (hb0 : 0 < b) (hb : b < 1/2) :
    b/(2*(1-b)) < b := by
  apply (div_lt_iff₀ (show 0 < 2*(1-b) by linarith)).mpr
  nlinarith

theorem random_edge_derivative_0 (b z : ℝ) (hb0 : 0 < b) (hb : b < 1/2)
    (hz : z < b/(2*(1-b))) :
    HasDerivAt (fun t => deltaB b (1-b) t)
      (-4*(1-b)^2*z*((2-b)*z-b)/b) z := by
  have hzb : z < b := hz.trans (random_cut_lt b hb0 hb)
  have h := ((hasDerivAt_paperPsiB b z (ne_of_lt hz) (ne_of_lt hzb)).const_add
    (paperPhiB b (1-b))).sub (cost_derivative_z (2*(1-b)/b) (1-b) z)
  simp only [paperR, ite_eq_left hz.le] at h
  convert h using 1
  · rfl
  · field_simp; ring

theorem random_edge_derivative_1 (b z : ℝ) (hb0 : 0 < b) (hb : b < 1/2)
    (hzc : b/(2*(1-b)) < z) (hz : z < b) :
    HasDerivAt (fun t => deltaB b (1-b) t)
      (-4*(1-b)^2*(b-z)*((2-3*b)*z-b*(1-b))/(b*(1-2*b)^2)) z := by
  have h := ((hasDerivAt_paperPsiB b z (ne_of_gt hzc) (ne_of_lt hz)).const_add
    (paperPhiB b (1-b))).sub (cost_derivative_z (2*(1-b)/b) (1-b) z)
  simp only [paperR, ite_eq_right (not_le.mpr hzc), ite_eq_left hz.le] at h
  have hd : 1-2*b ≠ 0 := by linarith
  convert h using 1
  · rfl
  · field_simp (disch := nlinarith [sq_pos_of_ne_zero hd])
    ring

theorem random_derivative_high_x (b x z : ℝ) (hb0 : b ≠ 0) (hb1 : b ≠ 1)
    (hx : 1-b < x) :
    HasDerivAt (fun t => deltaB b t z)
      (-(x-2*(1-b)*z-(1-b))*((1-2*b)*x+2*(1-b)*z-(1-b))/(2*b*(1-b))) x := by
  have h := ((hasDerivAt_paperPhiB b x hb1 (ne_of_gt hx)).add_const (paperPsiB b z)).sub
    (cost_derivative_x (2*(1-b)/b) x z)
  simp only [ite_eq_right (not_le.mpr hx)] at h
  convert h using 1
  · rfl
  · field_simp; ring

theorem random_edge_derivative_2 (b z : ℝ) (hb0 : 0 < b) (hb : b < 1/2)
    (hz : b < z) :
    HasDerivAt (fun t => deltaB b (1-b) t)
      ((z-b)*((1-b)^2+(4-3*b)*z-1)/b) z := by
  have hzc := (random_cut_lt b hb0 hb).trans hz
  have h := ((hasDerivAt_paperPsiB b z (ne_of_gt hzc) (ne_of_gt hz)).const_add
    (paperPhiB b (1-b))).sub (cost_derivative_z (2*(1-b)/b) (1-b) z)
  simp only [paperR, ite_eq_right (not_le.mpr hzc), ite_eq_right (not_le.mpr hz)] at h
  convert h using 1
  · rfl
  · field_simp; ring

/-- Proposition 4.3, first rectangle: the exact printed factorization. -/
theorem graph_rectangle_10 (w x z : ℝ) (hw : w ≠ 0)
    (hx : 1-w ≤ x) (hz : z ≤ w) :
    deltaA w x z = (x+w-1-z)^2 * (1-w+(2*w-1)*x-2*(1-w)*z)/(2*w) := by
  have hd : 1 - (1-w) ≠ 0 := by simpa only [sub_sub_cancel] using hw
  unfold deltaA paperPhiA paperPsiA
  rw [phiA_upper_closed (1-w) x hx]
  rw [psiA, ite_eq_left (show z ≤ 1-(1-w) by linarith)]
  unfold phiA1 graphPhi psiA0 linearPsi cost kA
  field_simp [hw, hd]
  ring

/-- Proposition 4.3, second rectangle: the exact printed factorization. -/
theorem graph_rectangle_01 (w x z : ℝ) (hw : w ≠ 0)
    (hx : x ≤ 1-w) (hz : w ≤ z) :
    deltaA w x z = (x+z-1)^2 * ((6-2*w)*z-(3+2*w)*x+3-4*w)/(6*w) := by
  have hd : 1 - (1-w) ≠ 0 := by simpa only [sub_sub_cancel] using hw
  unfold deltaA paperPhiA paperPsiA
  rw [psiA_upper_closed (1-w) z (show 1-(1-w) ≤ z by linarith)]
  rw [phiA, ite_eq_left hx]
  unfold phiA0 antiPhi psiA1 psiA0 linearPsi cost kA
  field_simp [hw, hd]
  ring

/-- The positive second factor on the second rectangle, exactly as printed. -/
theorem graph_second_factor (w x z : ℝ) (hw : 1/2 ≤ w) (hw1 : w ≤ 1)
    (hx : x ≤ 1-w) (hz : w ≤ z) :
    3*w ≤ (6-2*w)*z-(3+2*w)*x+3-4*w := by
  nlinarith [mul_nonneg (show 0 ≤ 6-2*w by linarith) (sub_nonneg.mpr hz),
    mul_nonneg (show 0 ≤ 3+2*w by linarith) (sub_nonneg.mpr hx)]

theorem graph_first_factor (w x z : ℝ) (hw : 1/2 ≤ w)
    (hx : 1-w ≤ x) :
    2*(1-w)*(w-z) ≤ 1-w+(2*w-1)*x-2*(1-w)*z := by
  nlinarith [mul_nonneg (show 0 ≤ 2*w-1 by linarith) (sub_nonneg.mpr hx)]

theorem random_rectangle_10 (b x z : ℝ) (hb0 : 0 < b) (hb : b < 1/2)
    (hx : 1-b ≤ x) (hz : z ≤ b/(2*(1-b))) :
    deltaB b x z = (x-2*(1-b)*z-(1-b))^2 *
      (1-b^2-(1-2*b)*x-2*(1-b)*(2-b)*z)/(6*b*(1-b)) := by
  have h0 : 1-b ≠ 0 := by linarith
  have h1 : 1-b ≠ 1 := by linarith
  have hd : 1-(1-b) ≠ 0 := by simpa only [sub_sub_cancel] using hb0.ne'
  unfold deltaB paperPhiB paperPsiB
  rw [phiB_upper_closed (1-b) x hx]
  rw [psiB, ite_eq_left (show z ≤ cutB (1-b) by rwa [cutB_paper])]
  unfold phiB1 splitPhi psiB0 linearPsi cost kB
  field_simp [h0, h1, hd, hb0.ne']
  ring

theorem random_rectangle_11 (b x z : ℝ) (hb0 : 0 < b) (hb : b < 1/2)
    (hx : 1-b ≤ x) (hzc : b/(2*(1-b)) < z) (hz : z ≤ b) :
    deltaB b x z = ((1-2*b)*x+2*(1-b)*z-(1-b))^2 *
      ((1-b)*(1-3*b)-(1-2*b)*x+2*(1-b)*(2-3*b)*z)/
        (6*b*(1-b)*(1-2*b)^2) := by
  have h0 : 1-b ≠ 0 := by linarith
  have h1 : 1-b ≠ 1 := by linarith
  have h2 : 2*(1-b)-1 ≠ 0 := by linarith
  have h3 : 1-2*b ≠ 0 := by linarith
  have hd : 1-(1-b) ≠ 0 := by simpa only [sub_sub_cancel] using hb0.ne'
  unfold deltaB paperPhiB paperPsiB
  rw [phiB_upper_closed (1-b) x hx]
  rw [psiB, ite_eq_right (show ¬z ≤ cutB (1-b) by rw [cutB_paper]; linarith),
    ite_eq_left (show z ≤ 1-(1-b) by linarith)]
  rw [← kB_paper, slackB11 (1-b) x z h0 h1 h2]
  field_simp [h0, h1, h2, h3, hd, hb0.ne']
  ring

theorem random_rectangle_02 (b x z : ℝ) (hb0 : 0 < b) (hb : b < 1/2)
    (hx : x ≤ 1-b) (hz : b < z) :
    deltaB b x z = (x+z-1)^2*((4-3*b)*z-2*x+2-3*b)/(3*b) := by
  have h0 : 1-b ≠ 0 := by linarith
  have h1 : 1-b ≠ 1 := by linarith
  have h2 : 2*(1-b)-1 ≠ 0 := by linarith
  have hd : 1-(1-b) ≠ 0 := by simpa only [sub_sub_cancel] using hb0.ne'
  have hc : cutB (1-b) ≤ b := by
    rw [cutB_paper]
    apply (div_le_iff₀ (show 0 < 2*(1-b) by linarith)).mpr
    nlinarith
  unfold deltaB paperPhiB paperPsiB
  rw [phiB, ite_eq_left hx]
  rw [psiB, ite_eq_right (show ¬z ≤ cutB (1-b) by linarith),
    ite_eq_right (show ¬z ≤ 1-(1-b) by linarith)]
  unfold phiB0 antiPhi psiB2 psiB1 psiB0 linearPsi cutB cost kB
  field_simp [h0, h1, h2, hd, hb0.ne']
  ring

/-- Strict positivity of the factor in the printed second edge derivative. -/
theorem random_middle_factor_pos (b z : ℝ) (hb0 : 0 < b) (hb : b < 1/2)
    (hz : b/(2*(1-b)) ≤ z) : 0 < (2-3*b)*z-b*(1-b) := by
  have hd : 1-b ≠ 0 := by linarith
  have h1 : 0 < 1-b := by linarith
  have h2 : 0 < 1-2*b := by linarith
  have he : (2-3*b)*z-b*(1-b) =
      (2-3*b)*(z-b/(2*(1-b))) + b^2*(1-2*b)/(2*(1-b)) := by
    field_simp; ring
  rw [he]
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (by linarith) (sub_nonneg.mpr hz)) (by positivity)

theorem random_edge_derivative_1_nonpos (b z : ℝ) (hb0 : 0 < b) (hb : b < 1/2)
    (hzc : b/(2*(1-b)) ≤ z) (hz : z ≤ b) :
    -4*(1-b)^2*(b-z)*((2-3*b)*z-b*(1-b))/(b*(1-2*b)^2) ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (1-b)])
      (sub_nonneg.mpr hz)) (random_middle_factor_pos b z hb0 hb hzc).le

theorem random_last_linear_factors (b x z : ℝ) (hb0 : 0 < b) (hb : b < 1/2)
    (hx : 1-b ≤ x) (hx1 : x ≤ 1) (hz : b ≤ z) :
    x-2*(1-b)*z-(1-b) ≤ -b*(1-2*b) ∧
      0 ≤ (1-2*b)*x+2*(1-b)*z-(1-b) := by
  constructor
  · nlinarith [mul_nonneg (show 0 ≤ 1-b by linarith) (sub_nonneg.mpr hz)]
  · nlinarith [mul_nonneg (show 0 ≤ 1-2*b by linarith) (sub_nonneg.mpr hx),
      mul_nonneg (show 0 ≤ 1-b by linarith) (sub_nonneg.mpr hz)]

theorem random_derivative_high_x_nonneg (b x z : ℝ) (hb0 : 0 < b) (hb : b < 1/2)
    (hx : 1-b ≤ x) (hx1 : x ≤ 1) (hz : b ≤ z) :
    0 ≤ -(x-2*(1-b)*z-(1-b))*((1-2*b)*x+2*(1-b)*z-(1-b))/(2*b*(1-b)) := by
  obtain ⟨hm,hp⟩ := random_last_linear_factors b x z hb0 hb hx hx1 hz
  have h1 : 0 < 1-b := by linarith
  apply div_nonneg _ (by positivity)
  apply mul_nonneg _ hp
  nlinarith [mul_pos hb0 (show 0 < 1-2*b by linarith)]

theorem random_last_edge_factor (b z : ℝ) (hb0 : 0 < b) (hb : b < 1/2)
    (hz : b ≤ z) : 2*b*(1-b) ≤ (1-b)^2+(4-3*b)*z-1 := by
  nlinarith [mul_nonneg (show 0 ≤ 4-3*b by linarith) (sub_nonneg.mpr hz)]

theorem random_edge_derivative_2_nonneg (b z : ℝ) (hb0 : 0 < b) (hb : b < 1/2)
    (hz : b ≤ z) : 0 ≤ (z-b)*((1-b)^2+(4-3*b)*z-1)/b := by
  apply div_nonneg _ hb0.le
  apply mul_nonneg (sub_nonneg.mpr hz)
  have h := random_last_edge_factor b z hb0 hb hz
  nlinarith [mul_pos hb0 (show 0 < 1-b by linarith)]

theorem random_middle_anchor (b : ℝ) (hb0 : 0 < b) (hb : b < 1/2) :
    deltaB b (1-b) (b/(2*(1-b))) = b^2*(1-2*b)/(6*(1-b)) := by
  rw [random_rectangle_10 b (1-b) (b/(2*(1-b))) hb0 hb le_rfl le_rfl]
  have hd : 1-b ≠ 0 := by linarith
  field_simp; ring

#assert_lean_mirror_axioms graph_rectangle_10
#assert_lean_mirror_axioms coupling_nu_moment
#assert_lean_mirror_axioms coupling_rho_moment
#assert_lean_mirror_axioms coupling_transpose_moment
#assert_lean_mirror_axioms coupling_eta_moment
#assert_lean_mirror_axioms rho_support_moment
#assert_lean_mirror_axioms graph_rectangle_01
#assert_lean_mirror_axioms graph_second_factor
#assert_lean_mirror_axioms graph_first_factor
#assert_lean_mirror_axioms random_rectangle_10
#assert_lean_mirror_axioms random_rectangle_11
#assert_lean_mirror_axioms random_rectangle_02

end
end Papers.Rockel2026ExactBlest.ArticleOriginalProof
