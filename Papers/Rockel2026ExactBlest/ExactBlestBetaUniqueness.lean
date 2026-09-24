import Papers.Rockel2026ExactBlest.ExactBlestEtaUniqueness

/-! Beta-boundary equality cases for exact-blest-regions.tex.
Fermat's theorem applied to the already checked dual forces the shuffle graph. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval Topology
open Papers.Rockel2026XiBlest

namespace Papers.Rockel2026ExactBlest
noncomputable section
set_option maxHeartbeats 4000000

def betaRankReal (q x : ℝ) : ℝ :=
  paramPieces q (fun y => y) (fun y => y + (1 / 2 - q)) (fun y => y - (1 / 2 - q)) (fun y => y) x

theorem betaRankReal_mem (q : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2)) (x : I) :
    betaRankReal q x ∈ Icc (0 : ℝ) 1 := by
  unfold betaRankReal paramPieces
  split_ifs <;> constructor <;> linarith [x.property.1, x.property.2, hq.1, hq.2]

def betaRank (q : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2)) (x : I) : I :=
  ⟨betaRankReal q x, betaRankReal_mem q hq x⟩

theorem measurable_betaRank (q : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2)) :
    Measurable (betaRank q hq) := by
  apply Measurable.subtype_mk
  exact measurable_paramPieces q _ _ _ _ (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

theorem hasDerivAt_betaCubic (h c x : ℝ) :
    HasDerivAt (fun y : ℝ => 2 * y ^ 3 / 3 + h * y ^ 2 + c) (2 * x * (x + h)) x := by
  convert (((((hasDerivAt_id x).pow 3).const_mul 2).div_const 3).add
    (((hasDerivAt_id x).pow 2).const_mul h)).add_const c using 1
  · ext y; dsimp
  · dsimp; ring

theorem hasDerivAt_paramPhi (q x : ℝ) (hxq : x ≠ q) (hxh : x ≠ 1 / 2) (hxr : x ≠ 1 - q) :
    HasDerivAt (paramPhi q) (2 * x * betaRankReal q x) x := by
  by_cases h0 : x ≤ q
  · rw [betaRankReal, paramPieces, ite_eq_left h0]
    have hp := hasDerivAt_betaCubic 0 0 x
    simp only [zero_mul, add_zero] at hp
    apply hp.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (lt_of_le_of_ne h0 hxq)] with y hy
    change y < q at hy
    simp [paramPhi, paramPieces, hy.le, paramPhi0]
  · by_cases h1 : x ≤ 1 / 2
    · rw [betaRankReal, paramPieces, ite_eq_right h0, ite_eq_left h1]
      apply (hasDerivAt_betaCubic (1 / 2 - q) (q ^ 3 - q ^ 2 / 2) x).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds (lt_of_not_ge h0) (lt_of_le_of_ne h1 hxh)] with y hy
      simp only [paramPhi, paramPieces, ite_eq_right (not_le.mpr hy.1), ite_eq_left hy.2.le, paramPhi1]
      ring
    · by_cases h2 : x ≤ 1 - q
      · rw [betaRankReal, paramPieces, ite_eq_right h0, ite_eq_right h1, ite_eq_left h2]
        have hp := hasDerivAt_betaCubic (q - 1 / 2) (1 / 24 - q ^ 3 / 3) x
        have hd : 2 * x * (x + (q - 1 / 2)) = 2 * x * (x - (1 / 2 - q)) := by ring
        rw [hd] at hp
        apply hp.congr_of_eventuallyEq
        filter_upwards [Ioi_mem_nhds (lt_of_not_ge h0),
          Ioo_mem_nhds (lt_of_not_ge h1) (lt_of_le_of_ne h2 hxr)] with y hy0 hy
        change q < y at hy0
        simp only [paramPhi, paramPieces, ite_eq_right (not_le.mpr hy0),
          ite_eq_right (not_le.mpr hy.1), ite_eq_left hy.2.le, paramPhi2]
        ring
      · rw [betaRankReal, paramPieces, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2]
        have hp := hasDerivAt_betaCubic 0 (2 * q ^ 3 / 3 - 5 * q ^ 2 / 2 + 2 * q - 11 / 24) x
        simp only [zero_mul, add_zero] at hp
        apply hp.congr_of_eventuallyEq
        filter_upwards [Ioi_mem_nhds (lt_of_not_ge h0), Ioi_mem_nhds (lt_of_not_ge h1),
          Ioi_mem_nhds (lt_of_not_ge h2)] with y hy0 hy1 hy2
        simp only [Set.mem_Ioi] at hy0 hy1 hy2
        simp only [paramPhi, paramPieces, ite_eq_right (not_le.mpr hy0),
          ite_eq_right (not_le.mpr hy1), ite_eq_right (not_le.mpr hy2), paramPhi3]
        ring

def betaSlackReal (q x z : ℝ) : ℝ :=
  paramPhi q x + paramPsi q z -
    (x ^ 2 * z - 3 * (1 / 2 - q) ^ 2 * (if 1 / 2 < x ∧ 1 / 2 < z then 1 else 0))

/-- The median-quadrant indicator is locally constant off its vertical cut. -/
theorem hasDerivAt_betaIndicator (x z : ℝ) (hxh : x ≠ 1 / 2) :
    HasDerivAt (fun y : ℝ => if 1 / 2 < y ∧ 1 / 2 < z then (1 : ℝ) else 0) 0 x := by
  by_cases hx : 1 / 2 < x
  · apply (hasDerivAt_const x (if 1 / 2 < z then (1 : ℝ) else 0)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    change 1 / 2 < y at hy
    simp only [hy, true_and]
  · have hx' : x < 1 / 2 := lt_of_le_of_ne (le_of_not_gt hx) hxh
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx'] with y hy
    change y < 1 / 2 at hy
    simp only [not_lt.mpr hy.le, false_and, ite_false]

theorem beta_contact (q x z : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hx : x ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1)
    (hxq : x ≠ q) (hxh : x ≠ 1 / 2) (hxr : x ≠ 1 - q)
    (heq : betaSlackReal q x z = 0) : z = betaRankReal q x := by
  have hm : IsLocalMin (fun y => betaSlackReal q y z) x := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    change betaSlackReal q x z ≤ betaSlackReal q y z
    rw [heq]
    exact sub_nonneg.mpr (beta_param_dual q y z hq ⟨hy.1.le, hy.2.le⟩ hz)
  have hd : HasDerivAt (fun y => betaSlackReal q y z) (2 * x * betaRankReal q x - 2 * x * z) x := by
    convert ((hasDerivAt_paramPhi q x hxq hxh hxr).add_const (paramPsi q z)).sub
      ((((hasDerivAt_id x).pow 2).mul_const z).sub
        ((hasDerivAt_betaIndicator x z hxh).const_mul (3 * (1 / 2 - q) ^ 2))) using 1
    · ext y; dsimp [betaSlackReal]
    · dsimp; ring
  have he := hm.hasDerivAt_eq_zero hd
  have hp : 2 * x ≠ 0 := ne_of_gt (mul_pos (by norm_num) hx.1)
  have hh : 2 * x * (betaRankReal q x - z) = 0 := by nlinarith
  have hz0 := (mul_eq_zero.mp hh).resolve_left hp
  linarith

theorem beta_upper_graph (C : Copula 2) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hb : C.blomqvistBeta = 4 * q - 1) (hn : blestNu C = betaUpper C.blomqvistBeta) :
    ∀ᵐ x ∂C.survivalCopula.toMeasure, x 1 = betaRank q hq (x 0) := by
  let D := C.survivalCopula
  have hp : Integrable (fun x : Fin 2 → I => paramPhi q (x 0)) D.toMeasure :=
    integrable_paramPieces D 0 q _ _ _ _ (by unfold paramPhi0; fun_prop)
      (by unfold paramPhi1; fun_prop) (by unfold paramPhi2; fun_prop) (by unfold paramPhi3; fun_prop)
  have hs : Integrable (fun x : Fin 2 → I => paramPsi q (x 1)) D.toMeasure :=
    integrable_paramPieces D 1 q _ _ _ _ (by unfold paramPsi0; fun_prop)
      (by unfold paramPsi1; fun_prop) (by unfold paramPsi2; fun_prop) (by unfold paramPsi3; fun_prop)
  have hi : Integrable (fun x : Fin 2 → I =>
      (x 0 : ℝ) ^ 2 * (x 1 : ℝ) - 3 * (1 / 2 - q) ^ 2 * upperQuadrant x) D.toMeasure :=
    (Copula.integrable_continuous_cube _ (by fun_prop)).sub ((integrable_upperQuadrant D).const_mul _)
  let slack := fun x : Fin 2 → I => betaSlackReal q (x 0) (x 1)
  have hnon : 0 ≤ slack := fun x => sub_nonneg.mpr
    (beta_param_dual q (x 0) (x 1) hq (x 0).property (x 1).property)
  have hzero : (∫ x, slack x ∂D.toMeasure) = 0 := by
    change (∫ x, paramPhi q (x 0) + paramPsi q (x 1) -
      ((x 0 : ℝ) ^ 2 * (x 1 : ℝ) - 3 * (1 / 2 - q) ^ 2 * upperQuadrant x) ∂D.toMeasure) = 0
    have hsub := integral_sub (hp.add hs) hi
    simp only [Pi.add_apply] at hsub
    rw [hsub, integral_add hp hs,
      D.integral_eval 0 (fun u : I => paramPhi q u) (measurable_paramPieces q _ _ _ _
        (by unfold paramPhi0; fun_prop) (by unfold paramPhi1; fun_prop)
        (by unfold paramPhi2; fun_prop) (by unfold paramPhi3; fun_prop)),
      D.integral_eval 1 (fun u : I => paramPsi q u) (measurable_paramPieces q _ _ _ _
        (by unfold paramPsi0; fun_prop) (by unfold paramPsi1; fun_prop)
        (by unfold paramPsi2; fun_prop) (by unfold paramPsi3; fun_prop)),
      integral_paramPhi q hq, integral_paramPsi q hq,
      integral_sub (Copula.integrable_continuous_cube _ (by fun_prop))
        ((integrable_upperQuadrant D).const_mul _), integral_const_mul]
    have hm := support_moment_survival C 0
    norm_num [cost] at hm
    have hquad := beta_quadrant_formula D
    change C.survivalCopula.blomqvistBeta = 4 * (∫ x, upperQuadrant x ∂D.toMeasure) - 1 at hquad
    rw [Copula.blomqvistBeta_survivalCopula, hb] at hquad
    have hqv : (∫ x, upperQuadrant x ∂D.toMeasure) = q := by linarith
    rw [hqv]
    rw [hb] at hn
    unfold betaUpper at hn
    change blestNu C = 12 * (∫ x, (x 0 : ℝ) ^ 2 * (x 1 : ℝ) ∂D.toMeasure) - 2 at hm
    nlinarith
  have hae := (integral_eq_zero_iff_of_nonneg hnon ((hp.add hs).sub hi)).mp hzero
  filter_upwards [hae, ae_coord_ne D 0 0, ae_coord_ne D 0 1,
    ae_coord_ne D 0 q, ae_coord_ne D 0 (1 / 2), ae_coord_ne D 0 (1 - q)] with x hx hx0 hx1 hxq hxh hxr
  apply Subtype.ext
  exact beta_contact q (x 0) (x 1) hq
    ⟨lt_of_le_of_ne (x 0).property.1 (Ne.symm hx0), lt_of_le_of_ne (x 0).property.2 hx1⟩
    (x 1).property hxq hxh hxr hx

/-- The unique graph is forced at every beta, including both endpoint fibres. -/
theorem beta_upper_unique (C D : Copula 2) (hb : C.blomqvistBeta = D.blomqvistBeta)
    (hc : blestNu C = betaUpper C.blomqvistBeta) (hd : blestNu D = betaUpper D.blomqvistBeta) : C = D := by
  let q := (C.blomqvistBeta + 1) / 4
  have hq : q ∈ Icc (0 : ℝ) (1 / 2) := by
    dsimp [q]
    constructor <;> linarith [C.blomqvistBeta_mem_Icc.1, C.blomqvistBeta_mem_Icc.2]
  have hC : C.blomqvistBeta = 4 * q - 1 := by dsimp [q]; ring
  have hD : D.blomqvistBeta = 4 * q - 1 := hb.symm.trans hC
  have h := copula_eq_of_graph C.survivalCopula D.survivalCopula (betaRank q hq)
    (measurable_betaRank q hq) (beta_upper_graph C q hq hC hc) (beta_upper_graph D q hq hD hd)
  simpa only [Copula.survivalCopula_survivalCopula] using congrArg Copula.survivalCopula h

theorem beta_lower_unique (C D : Copula 2) (hb : C.blomqvistBeta = D.blomqvistBeta)
    (hc : blestNu C = betaLower C.blomqvistBeta) (hd : blestNu D = betaLower D.blomqvistBeta) : C = D := by
  apply Copula.reflect_injective {1}
  apply beta_upper_unique
  · simp only [Copula.blomqvistBeta_reflect_second, hb]
  · rw [blest_reflect_second, Copula.blomqvistBeta_reflect_second, hc]
    unfold betaUpper betaLower
    ring
  · rw [blest_reflect_second, Copula.blomqvistBeta_reflect_second, hd]
    unfold betaUpper betaLower
    ring

theorem beta_upper_exists_unique (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) :
    ∃! C : Copula 2, C.blomqvistBeta = b ∧ blestNu C = betaUpper b := by
  obtain ⟨C, hc, hn⟩ := beta_upper_attained b hb
  refine ⟨C, ⟨hc, hn⟩, ?_⟩
  intro D hd
  apply beta_upper_unique D C (hd.1.trans hc.symm)
  · rw [hd.1]; exact hd.2
  · rw [hc]; exact hn

theorem beta_lower_exists_unique (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) :
    ∃! C : Copula 2, C.blomqvistBeta = b ∧ blestNu C = betaLower b := by
  obtain ⟨C, hc, hn⟩ := beta_lower_attained b hb
  refine ⟨C, ⟨hc, hn⟩, ?_⟩
  intro D hd
  apply beta_lower_unique D C (hd.1.trans hc.symm)
  · rw [hd.1]; exact hd.2
  · rw [hc]; exact hn

theorem nu_beta_upper_parameter (C : Copula 2) (hc : blestNu C - C.blomqvistBeta = 8 / 9) :
    C.blomqvistBeta = -1 / 3 := by
  let b := C.blomqvistBeta
  have hu := beta_region_upper C
  have hid : 8 / 9 - (betaUpper b - b) = (3 * b + 1) ^ 2 * (11 - 3 * b) / 144 := by
    unfold betaUpper; ring
  have hpos : 0 < 11 - 3 * b := by dsimp [b]; linarith [C.blomqvistBeta_mem_Icc.2]
  have hprod : (3 * b + 1) ^ 2 * (11 - 3 * b) ≤ 0 := by dsimp [b] at hid ⊢; linarith
  have hz : (3 * b + 1) ^ 2 * (11 - 3 * b) = 0 :=
    le_antisymm hprod (mul_nonneg (sq_nonneg _) hpos.le)
  have hs := sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_right hpos.ne')
  dsimp [b] at hs
  linarith

theorem nu_beta_upper_unique (C : Copula 2) (hc : blestNu C - C.blomqvistBeta = 8 / 9) :
    C = betaWitness := by
  have hb := nu_beta_upper_parameter C hc
  apply beta_upper_unique C betaWitness (hb.trans betaWitness_values.2.symm)
  · rw [hb, betaUpper]; linarith
  · rw [betaWitness_values.1, betaWitness_values.2, betaUpper]; norm_num

theorem nu_beta_lower_unique (C : Copula 2) (hc : blestNu C - C.blomqvistBeta = -8 / 9) :
    C = betaWitness.reflect {1} := by
  have h : C.reflect {1} = betaWitness := by
    apply nu_beta_upper_unique
    rw [blest_reflect_second, Copula.blomqvistBeta_reflect_second]
    linarith
  simpa only [Copula.reflect_reflect] using congrArg (fun E : Copula 2 => E.reflect {1}) h

theorem nu_beta_eq_iff (C : Copula 2) :
    |blestNu C - C.blomqvistBeta| = 8 / 9 ↔ C = betaWitness ∨ C = betaWitness.reflect {1} := by
  constructor
  · intro h
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 8 / 9)).mp h with hp | hn
    · exact Or.inl (nu_beta_upper_unique C hp)
    · exact Or.inr (nu_beta_lower_unique C (by linarith))
  · rintro (rfl | rfl)
    · rw [betaWitness_values.1, betaWitness_values.2]; norm_num
    · rw [blest_reflect_second, Copula.blomqvistBeta_reflect_second,
        betaWitness_values.1, betaWitness_values.2]; norm_num

theorem beta_upper_rho_eq (C : Copula 2) (hc : blestNu C = betaUpper C.blomqvistBeta) :
    C.spearmanRho = blestNu C := by
  obtain ⟨D, hb, hn, hr⟩ := beta_upper_attained_joint C.blomqvistBeta C.blomqvistBeta_mem_Icc
  have he : C = D := beta_upper_unique C D hb.symm hc (by rw [hb]; exact hn)
  rw [he, hr, hn]

theorem beta_lower_rho_eq (C : Copula 2) (hc : blestNu C = betaLower C.blomqvistBeta) :
    C.spearmanRho = blestNu C := by
  obtain ⟨D, hb, hn, hr⟩ := beta_lower_attained_joint C.blomqvistBeta C.blomqvistBeta_mem_Icc
  have he : C = D := beta_lower_unique C D hb.symm hc (by rw [hb]; exact hn)
  rw [he, hr, hn]

theorem beta_upper_survival (C : Copula 2) (hc : blestNu C = betaUpper C.blomqvistBeta) :
    C.survivalCopula = C := by
  apply beta_upper_unique _ _ (Copula.blomqvistBeta_survivalCopula C) _ hc
  rw [nu_survival, Copula.blomqvistBeta_survivalCopula, beta_upper_rho_eq C hc, hc]
  ring

theorem beta_lower_survival (C : Copula 2) (hc : blestNu C = betaLower C.blomqvistBeta) :
    C.survivalCopula = C := by
  apply beta_lower_unique _ _ (Copula.blomqvistBeta_survivalCopula C) _ hc
  rw [nu_survival, Copula.blomqvistBeta_survivalCopula, beta_lower_rho_eq C hc, hc]
  ring

/-- The original and reflected-coordinate upper extremizer is the graph law of P_q.
The map representative may differ from the displayed P_q only at its cut points. -/
theorem beta_upper_graph_law (C : Copula 2) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hb : C.blomqvistBeta = 4 * q - 1) (hn : blestNu C = betaUpper C.blomqvistBeta) :
    C.toMeasure = (volume : Measure I).map (fun x => ![x, betaRank q hq x]) := by
  have hm : Measurable (fun x : I => ![x, betaRank q hq x]) := by
    have := measurable_betaRank q hq
    fun_prop
  rw [← C.map_eval 0, Measure.map_map hm (measurable_pi_apply 0)]
  have hg := beta_upper_graph C q hq hb hn
  rw [beta_upper_survival C hn] at hg
  have hv : (fun x : Fin 2 → I => ![x 0, betaRank q hq (x 0)]) =ᵐ[C.toMeasure] id := by
    filter_upwards [hg] with x hx
    funext i
    fin_cases i
    · rfl
    · exact hx.symm
  change C.toMeasure = C.toMeasure.map (fun x => ![x 0, betaRank q hq (x 0)])
  rw [Measure.map_congr hv, Measure.map_id]

def betaLowerRank (q : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2)) (x : I) : I :=
  unitInterval.symm (betaRank (1 / 2 - q) ⟨by linarith [hq.2], by linarith [hq.1]⟩ x)

/-- The lower shuffle is the second-coordinate reflection of P_(1/2-q). -/
theorem beta_lower_graph_law (C : Copula 2) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hb : C.blomqvistBeta = 4 * q - 1) (hn : blestNu C = betaLower C.blomqvistBeta) :
    C.toMeasure = (volume : Measure I).map (fun x => ![x, betaLowerRank q hq x]) := by
  have hq' : 1 / 2 - q ∈ Icc (0 : ℝ) (1 / 2) := ⟨by linarith [hq.2], by linarith [hq.1]⟩
  have hb' : (C.reflect {1}).blomqvistBeta = 4 * (1 / 2 - q) - 1 := by
    rw [Copula.blomqvistBeta_reflect_second, hb]; ring
  have hn' : blestNu (C.reflect {1}) = betaUpper (C.reflect {1}).blomqvistBeta := by
    rw [blest_reflect_second, Copula.blomqvistBeta_reflect_second, hn]
    unfold betaUpper betaLower
    ring
  have h := congrArg (fun μ : Measure (Fin 2 → I) => μ.map (Copula.reflectPoint {1}))
    (beta_upper_graph_law (C.reflect {1}) (1 / 2 - q) hq' hb' hn')
  rw [← Copula.toMeasure_reflect, Copula.reflect_reflect] at h
  have hm : Measurable (fun x : I => ![x, betaRank (1 / 2 - q) hq' x]) := by
    have := measurable_betaRank (1 / 2 - q) hq'
    fun_prop
  rw [Measure.map_map (Copula.measurable_reflectPoint {1}) hm] at h
  have he : Copula.reflectPoint {1} ∘ (fun x : I => ![x, betaRank (1 / 2 - q) hq' x]) =
      fun x : I => ![x, betaLowerRank q hq x] := by
    funext x i
    fin_cases i <;> simp [Copula.reflectPoint, betaLowerRank]
  rw [he] at h
  exact h

/-- Exact agreement with the paper's P_q off its finitely many breakpoints. -/
theorem betaRankReal_eq_paper (q x : ℝ) (hxq : x ≠ q) (hxh : x ≠ 1 / 2) :
    betaRankReal q x = if q ≤ x ∧ x < 1 / 2 then x + 1 / 2 - q
      else if 1 / 2 ≤ x ∧ x ≤ 1 - q then x - 1 / 2 + q else x := by
  unfold betaRankReal paramPieces
  split_ifs <;> grind

/-- The reflected shuffle agrees with the displayed N_q off the breakpoints. -/
theorem betaLowerRank_eq_paper (q : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2)) (x : I)
    (hxl : (x : ℝ) ≠ 1 / 2 - q) (hxh : (x : ℝ) ≠ 1 / 2) :
    (betaLowerRank q hq x : ℝ) =
      if 1 / 2 - q ≤ (x : ℝ) ∧ (x : ℝ) < 1 / 2 then 1 - (x : ℝ) - q
      else if 1 / 2 ≤ (x : ℝ) ∧ (x : ℝ) ≤ 1 / 2 + q then 1 - (x : ℝ) + q else 1 - (x : ℝ) := by
  change 1 - betaRankReal (1 / 2 - q) (x : ℝ) = _
  rw [betaRankReal_eq_paper _ _ hxl hxh]
  have he : 1 - (1 / 2 - q) = 1 / 2 + q := by ring
  rw [he]
  split_ifs <;> ring

#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_upper_rho_eq
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_lower_rho_eq
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_upper_survival
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_lower_survival
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_upper_graph_law
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_lower_graph_law
#assert_standard_axioms Papers.Rockel2026ExactBlest.betaRankReal_eq_paper
#assert_standard_axioms Papers.Rockel2026ExactBlest.betaLowerRank_eq_paper

#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_upper_graph
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_upper_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_lower_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_upper_exists_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_lower_exists_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_beta_upper_parameter
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_beta_upper_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_beta_lower_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_beta_eq_iff

#assert_standard_axioms Papers.Rockel2026ExactBlest.betaRankReal_mem
#assert_standard_axioms Papers.Rockel2026ExactBlest.measurable_betaRank
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_betaCubic
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_paramPhi
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_betaIndicator
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_contact

end
end Papers.Rockel2026ExactBlest
