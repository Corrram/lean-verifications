import Copula.Rank.Region.RhoGamma.Coverage

/-! Every positive supporting slope below one has a concrete glued certificate. -/

open scoped unitInterval
open ProbabilityTheory Copula.RankRegion

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

private theorem continuous_slope {X : Type*} [TopologicalSpace X] {s c : X → ℝ}
    (hs : Continuous s) (hc : Continuous c) (hpos : ∀ x, 0 < s x) :
    Continuous (fun x => RhoGamma.supportingSlope (s x) (c x)) := by
  have hA : Continuous (fun x => RhoGamma.splitRatio (s x) (c x)) := by
    unfold RhoGamma.splitRatio
    fun_prop
  have hd : ∀ x, 1 + RhoGamma.splitRatio (s x) (c x) ≠ 0 := by
    intro x
    unfold RhoGamma.splitRatio
    have hh := Real.sqrt_nonneg ((s x) ^ 2 + 2 * c x)
    linarith only [hh, hpos x]
  exact hs.mul (continuous_const.div (continuous_const.add hA) hd)

open RhoFootrule.UpperSpline

private noncomputable def contactSlope (N : ℕ) : ℝ :=
  RhoGamma.supportingSlope (1 / (N : ℝ)) (-(1 / (8 * (N : ℝ) ^ 2)))

private theorem left_zero (N : ℕ) (hN : 0 < N) :
    (RhoGamma.AuxiliaryCertificate.ofLeft (RhoFootrule.leftFamily N hN 0)).t = contactSlope N := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  dsimp [RhoGamma.AuxiliaryCertificate.t, RhoGamma.AuxiliaryCertificate.ofLeft,
    RhoFootrule.leftFamily, period, offset, contactSlope]
  norm_num
  congr 1 <;> field_simp
  all_goals norm_num

private theorem right_zero (N : ℕ) (hN : 0 < N) :
    (RhoGamma.AuxiliaryCertificate.ofRight (RhoFootrule.rightFamily N hN 0)).t = contactSlope (N + 1) := by
  have hn1 : (N : ℝ) + 1 ≠ 0 := by positivity
  dsimp [RhoGamma.AuxiliaryCertificate.t, RhoGamma.AuxiliaryCertificate.ofRight,
    RhoFootrule.rightFamily, period, offset, contactSlope]
  norm_num
  congr 1 <;> field_simp
  all_goals norm_num

private theorem middle_join (N : ℕ) (hN : 0 < N) :
    (RhoGamma.AuxiliaryCertificate.ofLeft (RhoFootrule.leftFamily N hN 1)).t =
      (RhoGamma.AuxiliaryCertificate.ofRight (RhoFootrule.rightFamily N hN 1)).t := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hn1 : (N : ℝ) + 1 ≠ 0 := by positivity
  dsimp [RhoGamma.AuxiliaryCertificate.t, RhoGamma.AuxiliaryCertificate.ofLeft,
    RhoGamma.AuxiliaryCertificate.ofRight, RhoFootrule.leftFamily, RhoFootrule.rightFamily, period, offset]
  norm_num

private theorem continuous_right (N : ℕ) (hN : 0 < N) :
    Continuous (fun u : I => (RhoGamma.AuxiliaryCertificate.ofRight (RhoFootrule.rightFamily N hN u)).t) := by
  apply continuous_slope
  · dsimp [RhoGamma.AuxiliaryCertificate.ofRight, RhoFootrule.rightFamily, period]; fun_prop
  · dsimp [RhoGamma.AuxiliaryCertificate.ofRight, RhoFootrule.rightFamily, offset]; fun_prop
  · intro u; exact (RhoFootrule.rightFamily N hN u).period_pos

private theorem continuous_left (N : ℕ) (hN : 0 < N) :
    Continuous (fun u : I => (RhoGamma.AuxiliaryCertificate.ofLeft (RhoFootrule.leftFamily N hN u)).t) := by
  apply continuous_slope
  · dsimp [RhoGamma.AuxiliaryCertificate.ofLeft, RhoFootrule.leftFamily, period]; fun_prop
  · dsimp [RhoGamma.AuxiliaryCertificate.ofLeft, RhoFootrule.leftFamily, offset]; fun_prop
  · intro u; exact (RhoFootrule.leftFamily N hN u).period_pos

private theorem between_contacts {t : ℝ} (N : ℕ) (hN : 0 < N)
    (hlo : contactSlope (N + 1) ≤ t) (hhi : t ≤ contactSlope N) :
    ∃ A : RhoGamma.AuxiliaryCertificate, A.t = t := by
  by_cases hm : t ≤ (RhoGamma.AuxiliaryCertificate.ofLeft (RhoFootrule.leftFamily N hN 1)).t
  · obtain ⟨u, hu⟩ := exists_unitInterval_eq (continuous_right N hN)
      (by simpa only [right_zero] using hlo) (by simpa only [middle_join] using hm)
    exact ⟨.ofRight (RhoFootrule.rightFamily N hN u), hu⟩
  · obtain ⟨u, hu⟩ := exists_unitInterval_eq
      ((continuous_left N hN).comp unitInterval.continuous_symm)
      (by simpa only [Function.comp_apply, unitInterval.symm_zero] using le_of_not_ge hm)
      (by simpa only [Function.comp_apply, unitInterval.symm_one, left_zero] using hhi)
    exact ⟨.ofLeft (RhoFootrule.leftFamily N hN (unitInterval.symm u)), hu⟩

private theorem halfShift_large {s : ℝ} (hs : 1 ≤ s) :
    s / (1 + s) ≤ RhoGamma.supportingSlope s (3 / 8 - s / 2) := by
  have hrad : 0 ≤ s ^ 2 + 2 * (3 / 8 - s / 2) := by nlinarith [sq_nonneg (s - 1)]
  have hr := Real.sq_sqrt hrad
  have hn := Real.sqrt_nonneg (s ^ 2 + 2 * (3 / 8 - s / 2))
  have hrle : Real.sqrt (s ^ 2 + 2 * (3 / 8 - s / 2)) ≤ s := by nlinarith
  unfold RhoGamma.supportingSlope RhoGamma.cornerLength RhoGamma.splitRatio
  rw [mul_one_div]
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

private theorem above_first_contact {t : ℝ} (ht : t < 1) (hlo : contactSlope 1 ≤ t) :
    ∃ A : RhoGamma.AuxiliaryCertificate, A.t = t := by
  let S : ℝ := 1 + 2 / (1 - t)
  have hd : 0 < 1 - t := by linarith
  have hS : 1 ≤ S := by
    have hh : 0 ≤ 2 / (1 - t) := by positivity
    dsimp [S]
    linarith
  have hbig : t < S / (1 + S) := by
    have he : (1 - t) * S = 1 - t + 2 := by dsimp [S]; field_simp
    apply (lt_div_iff₀ (by linarith : 0 < 1 + S)).mpr
    nlinarith
  let scale : I → ℝ := fun u => 1 + (S - 1) * u
  have hscale (u : I) : 1 ≤ scale u := by
    dsimp [scale]
    have hh := mul_nonneg (sub_nonneg.mpr hS) u.property.1
    linarith
  have hc : Continuous (fun u : I => RhoGamma.supportingSlope (scale u) (3 / 8 - scale u / 2)) :=
    continuous_slope (by dsimp [scale]; fun_prop) (by dsimp [scale]; fun_prop)
      (fun u => by linarith [hscale u])
  obtain ⟨u, hu⟩ := exists_unitInterval_eq hc
    (by simpa [scale, contactSlope] using (show RhoGamma.supportingSlope 1 (3 / 8 - 1 / 2) ≤ t by norm_num [contactSlope] at hlo ⊢; exact hlo))
    (by simpa [scale] using hbig.le.trans (halfShift_large hS))
  exact ⟨.halfShift (scale u) (hscale u), hu⟩

private theorem contactSlope_tendsto :
    Filter.Tendsto contactSlope Filter.atTop (nhds 0) := by
  have hA : ContinuousAt (fun r : ℝ => RhoGamma.splitRatio r (-(r ^ 2) / 8)) 0 := by
    unfold RhoGamma.splitRatio
    fun_prop
  have hd : 1 + RhoGamma.splitRatio 0 (-(0 ^ 2) / 8) ≠ 0 := by norm_num [RhoGamma.splitRatio]
  have hz : ContinuousAt (fun r : ℝ => RhoGamma.cornerLength r (-(r ^ 2) / 8)) 0 :=
    continuousAt_const.div (continuousAt_const.add hA) hd
  have hG : ContinuousAt (fun r : ℝ => RhoGamma.supportingSlope r (-(r ^ 2) / 8)) 0 :=
    continuousAt_id.mul hz
  have hh := hG.tendsto.comp (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have he (N : ℕ) : contactSlope N =
      RhoGamma.supportingSlope (1 / (N : ℝ)) (-((1 / (N : ℝ)) ^ 2) / 8) := by
    unfold contactSlope
    congr 1
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, one_mul]
    ring
  simp only [Function.comp_def] at hh
  simp_rw [← he] at hh
  simpa [RhoGamma.supportingSlope] using hh

private theorem through_contacts (N : ℕ) (hN : 0 < N) {t : ℝ}
    (ht : t < 1) (hlo : contactSlope N ≤ t) :
    ∃ A : RhoGamma.AuxiliaryCertificate, A.t = t := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hN0 : N = 0
    · subst N
      exact above_first_contact ht hlo
    · by_cases hhi : contactSlope N ≤ t
      · exact ih (by omega) hhi
      · exact between_contacts N (by omega) hlo (le_of_not_ge hhi)

/-- The glued certificates cover every nontrivial positive supporting slope. -/
theorem supporting_slope_covered {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ A : RhoGamma.AuxiliaryCertificate, A.t = t := by
  have he : ∀ᶠ N : ℕ in Filter.atTop, contactSlope N < t :=
    contactSlope_tendsto.eventually (gt_mem_nhds ht)
  obtain ⟨N, hNt, hN⟩ := (he.and (Filter.eventually_gt_atTop 0)).exists
  exact through_contacts N hN ht1 hNt.le

end Papers.AnsariRockelSteinmassl2026RhoGamma
