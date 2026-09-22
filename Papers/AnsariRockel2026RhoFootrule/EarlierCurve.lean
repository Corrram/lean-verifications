import Papers.AnsariRockel2026RhoFootrule.BoundaryFormula
import Copula.Rank.Mixture

open MeasureTheory ProbabilityTheory Set
open Copula.RankRegion
open scoped unitInterval

namespace Papers.AnsariRockel2026RhoFootrule

/-- The attained upper rho boundary is concave in footrule. -/
theorem upperRho_concave : ConcaveOn ℝ (Icc (-1/2 : ℝ) 1) upperRho := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  obtain ⟨C,hCx,hCr⟩ := upper_boundary_attained hx
  obtain ⟨D,hDy,hDr⟩ := upper_boundary_attained hy
  let t : I := ⟨a,ha,by linarith⟩
  have h := sharp_upper_bound (C.mix D t)
  rw [Copula.spearmanRho_mix,Copula.spearmanFootrule_mix,hCx,hDy,hCr,hDr] at h
  change a*upperRho x+(1-a)*upperRho y ≤ upperRho (a*x+(1-a)*y) at h
  simpa only [show 1-a=b by linarith,smul_eq_mul] using h

noncomputable def oldContact (N : ℕ) : ℝ := 1-3/(2*(N : ℝ))
noncomputable def oldCorner (N : ℕ) : ℝ := (2*(N : ℝ)^2+N-4)/(2*((N : ℝ)+1)^2)
noncomputable def oldCornerRho (N : ℕ) : ℝ :=
  (2*(N : ℝ)^5+6*(N : ℝ)^4+3*(N : ℝ)^3-7*(N : ℝ)^2-3*N+1)/(2*(N : ℝ)^2*((N : ℝ)+1)^3)
noncomputable def oldContactRho (N : ℕ) : ℝ := 1-3/(2*(N : ℝ)^2)
noncomputable def oldLeftLine (N : ℕ) (x : ℝ) : ℝ :=
  oldContactRho N+(oldCornerRho N-oldContactRho N)/(oldCorner N-oldContact N)*(x-oldContact N)
noncomputable def oldRightLine (N : ℕ) (x : ℝ) : ℝ :=
  oldCornerRho N+(oldContactRho (N+1)-oldCornerRho N)/(oldContact (N+1)-oldCorner N)*(x-oldCorner N)

theorem upperRho_oldContact (N : ℕ) (hN : 0 < N) : upperRho (oldContact N)=oldContactRho N := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let S : RhoFootrule.LeftData := ⟨N,hN,0,1/(2*(N : ℝ)),by norm_num,by positivity,by field_simp; ring⟩
  have h := upperRho_parameter (RhoFootrule.UpperParameter.left S)
  dsimp [RhoFootrule.UpperParameter.footrule,RhoFootrule.UpperParameter.rho,S] at h
  norm_num only [mul_zero,add_zero,zero_pow (by decide : (2 : ℕ)≠0),zero_pow (by decide : (3 : ℕ)≠0),sub_zero] at h
  unfold oldContact oldContactRho
  convert h using 1 <;> field_simp
  ring

noncomputable def oldCornerV (N : ℕ) : ℝ := 1/((N : ℝ)*((N : ℝ)+1)*Real.sqrt (2*((N : ℝ)+1)))

theorem oldCornerV_bounds (N : ℕ) (hN : 0 < N) :
    0 ≤ oldCornerV N ∧ ((N : ℝ)+1)*oldCornerV N ≤ 1/(2*(N : ℝ)) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs := Real.sq_sqrt (show 0 ≤ 2*((N : ℝ)+1) by positivity)
  have hs0 := Real.sqrt_nonneg (2*((N : ℝ)+1))
  have hs2 : 2 ≤ Real.sqrt (2*((N : ℝ)+1)) := by nlinarith
  have hsv : 0 < Real.sqrt (2*((N : ℝ)+1)) := by linarith
  unfold oldCornerV
  constructor
  · positivity
  · rw [← mul_div_assoc,le_div_iff₀ (by positivity : (0 : ℝ) < 2*(N : ℝ)),div_mul_eq_mul_div,
      div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ)*((N : ℝ)+1)*Real.sqrt (2*((N : ℝ)+1)))]
    nlinarith [mul_nonneg (show 0 ≤ (N : ℝ)*((N : ℝ)+1) by positivity) (sub_nonneg.mpr hs2)]

theorem oldCornerV_sq (N : ℕ) (hN : 0 < N) :
    oldCornerV N^2=1/(2*(N : ℝ)^2*((N : ℝ)+1)^3) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  unfold oldCornerV
  rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
  field_simp

noncomputable def oldCornerData (N : ℕ) (hN : 0 < N) : RhoFootrule.LeftData where
  N := N
  N_pos := hN
  v := oldCornerV N
  w := 1/(2*(N : ℝ))-((N : ℝ)+1)*oldCornerV N
  v_nonneg := (oldCornerV_bounds N hN).1
  w_nonneg := sub_nonneg.mpr (oldCornerV_bounds N hN).2
  normalized := by
    have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    field_simp
    ring

theorem oldCornerData_footrule (N : ℕ) (hN : 0 < N) :
    (RhoFootrule.UpperParameter.left (oldCornerData N hN)).footrule=oldCorner N := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  dsimp [RhoFootrule.UpperParameter.footrule,oldCornerData]
  rw [sub_add_cancel,oldCornerV_sq N hN]
  unfold oldCorner
  field_simp
  ring

theorem upperRho_oldCorner (N : ℕ) (hN : 0 < N) :
    upperRho (oldCorner N)=oldCornerRho N+
      (1-2*(N : ℝ)*((N : ℝ)+1)*oldCornerV N)/((N : ℝ)^2*((N : ℝ)+1)^3) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [← oldCornerData_footrule N hN,upperRho_parameter]
  dsimp [RhoFootrule.UpperParameter.rho,oldCornerData]
  rw [sub_add_cancel,pow_succ (oldCornerV N) 2,oldCornerV_sq N hN]
  unfold oldCornerRho
  field_simp
  ring

theorem oldCorner_strict_gap (N : ℕ) (hN : 2 ≤ N) : oldCornerRho N < upperRho (oldCorner N) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hs := Real.sq_sqrt (show 0 ≤ 2*((N : ℝ)+1) by positivity)
  have hs0 := Real.sqrt_nonneg (2*((N : ℝ)+1))
  have hs2 : 2 < Real.sqrt (2*((N : ℝ)+1)) := by nlinarith
  have hsv : 0 < Real.sqrt (2*((N : ℝ)+1)) := by linarith
  have he : 2*(N : ℝ)*((N : ℝ)+1)*oldCornerV N=2/Real.sqrt (2*((N : ℝ)+1)) := by
    unfold oldCornerV
    field_simp
  have hv : 2*(N : ℝ)*((N : ℝ)+1)*oldCornerV N < 1 := by
    rw [he,div_lt_one hsv]
    exact hs2
  rw [upperRho_oldCorner N (by omega)]
  exact lt_add_of_pos_right _ (div_pos (sub_pos.mpr hv) (by positivity))

theorem oldCorner_order (N : ℕ) (hN : 0 < N) : oldContact N < oldCorner N ∧ oldCorner N < oldContact (N+1) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h1 : oldCorner N-oldContact N=3/(2*(N : ℝ)*((N : ℝ)+1)^2) := by
    unfold oldCorner oldContact
    field_simp
    ring
  have h2 : oldContact (N+1)-oldCorner N=3/(2*((N : ℝ)+1)^2) := by
    unfold oldCorner oldContact
    push_cast
    field_simp
    ring
  constructor <;> apply sub_pos.mp
  · rw [h1]; positivity
  · rw [h2]; positivity

theorem oldContact_mem (N : ℕ) (hN : 0 < N) : oldContact N ∈ Icc (-1/2 : ℝ) 1 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  unfold oldContact
  have h := (div_le_iff₀ (show (0 : ℝ) < 2*(N : ℝ) by positivity)).mpr (show (3 : ℝ) ≤ (3/2)*(2*(N : ℝ)) by linarith)
  constructor <;> linarith [div_pos (show (0 : ℝ)<3 by norm_num) (show (0 : ℝ)<2*(N : ℝ) by positivity)]

theorem oldCorner_mem (N : ℕ) (hN : 0 < N) : oldCorner N ∈ Icc (-1/2 : ℝ) 1 :=
  ⟨(oldContact_mem N hN).1.trans (oldCorner_order N hN).1.le,
    (oldCorner_order N hN).2.le.trans (oldContact_mem (N+1) (by omega)).2⟩


private theorem upperRho_strict_chord (a b x A B : ℝ) (ha : a ∈ Icc (-1/2 : ℝ) 1)
    (hb : b ∈ Icc (-1/2 : ℝ) 1) (hab : a < b) (hx : x ∈ Icc a b)
    (hA : A ≤ upperRho a) (hB : B ≤ upperRho b)
    (hs : (A < upperRho a ∧ x < b) ∨ (B < upperRho b ∧ a < x)) :
    A+(B-A)/(b-a)*(x-a) < upperRho x := by
  let α := (b-x)/(b-a)
  let β := (x-a)/(b-a)
  have hd : 0 < b-a := sub_pos.mpr hab
  have hα : 0 ≤ α := div_nonneg (sub_nonneg.mpr hx.2) hd.le
  have hβ : 0 ≤ β := div_nonneg (sub_nonneg.mpr hx.1) hd.le
  have hsum : α+β=1 := by dsimp [α,β]; field_simp; ring
  have he : α*a+β*b=x := by dsimp [α,β]; field_simp; ring
  have hconc := upperRho_concave.2 ha hb hα hβ hsum
  simp only [smul_eq_mul,he] at hconc
  have hlt : α*A+β*B < α*upperRho a+β*upperRho b := by
    rcases hs with hs | hs
    · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hs.1 (div_pos (sub_pos.mpr hs.2) hd))
        (mul_le_mul_of_nonneg_left hB hβ)
    · exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hA hα)
        (mul_lt_mul_of_pos_left hs.1 (div_pos (sub_pos.mpr hs.2) hd))
  have heq : A+(B-A)/(b-a)*(x-a)=α*A+β*B := by dsimp [α,β]; field_simp; ring
  rw [heq]
  exact hlt.trans_le hconc

/-- Strict improvement on the first linear segment of every later contact interval. -/
theorem earlier_left_strict (N : ℕ) (hN : 2 ≤ N) (x : ℝ)
    (hx : x ∈ Ioc (oldContact N) (oldCorner N)) : oldLeftLine N x < upperRho x := by
  have hNp : 0 < N := by omega
  exact upperRho_strict_chord _ _ _ _ _ (oldContact_mem N hNp) (oldCorner_mem N hNp)
    (oldCorner_order N hNp).1 ⟨hx.1.le,hx.2⟩ (upperRho_oldContact N hNp).ge
    (oldCorner_strict_gap N hN).le (Or.inr ⟨oldCorner_strict_gap N hN,hx.1⟩)

/-- Strict improvement on the second linear segment of every later contact interval. -/
theorem earlier_right_strict (N : ℕ) (hN : 2 ≤ N) (x : ℝ)
    (hx : x ∈ Ico (oldCorner N) (oldContact (N+1))) : oldRightLine N x < upperRho x := by
  have hNp : 0 < N := by omega
  exact upperRho_strict_chord _ _ _ _ _ (oldCorner_mem N hNp) (oldContact_mem (N+1) (by omega))
    (oldCorner_order N hNp).2 ⟨hx.1,hx.2.le⟩ (oldCorner_strict_gap N hN).le
    (upperRho_oldContact (N+1) (by omega)).ge (Or.inl ⟨oldCorner_strict_gap N hN,hx.2⟩)


/-- First radical branch of the earlier curve, including both endpoints. -/
theorem earlier_first_radical (x : ℝ) (hx : x ∈ Icc (-1/2 : ℝ) (-1/8)) :
    upperRho x=2*x+1/2-Real.sqrt 3/9*(Real.sqrt (1+2*x))^3 := by
  let v := (Real.sqrt 3/6)*Real.sqrt (1+2*x)
  have h3 : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hz : (Real.sqrt (1+2*x))^2=1+2*x := Real.sq_sqrt (by linarith [hx.1])
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv2 : v^2=(1+2*x)/12 := by
    dsimp [v]
    rw [mul_pow,div_pow,h3,hz]
    ring
  have hv3 : 8*v^3=Real.sqrt 3/9*(Real.sqrt (1+2*x))^3 := by
    dsimp [v]
    rw [mul_pow,div_pow,pow_succ (Real.sqrt 3) 2,h3]
    ring
  have hv1 : v ≤ 1/4 := by nlinarith [hx.2]
  let S : RhoFootrule.LeftData := ⟨1,by omega,v,1/2-2*v,hv0,by linarith,by norm_num⟩
  have hf : (RhoFootrule.UpperParameter.left S).footrule=x := by
    dsimp [RhoFootrule.UpperParameter.footrule,S]
    norm_num
    nlinarith [hv2]
  have hr : (RhoFootrule.UpperParameter.left S).rho=2*x+1/2-Real.sqrt 3/9*(Real.sqrt (1+2*x))^3 := by
    dsimp [RhoFootrule.UpperParameter.rho,S]
    norm_num
    nlinarith [hv2,hv3]
  rw [← hf,upperRho_parameter,hr,hf]

/-- Second radical branch of the earlier curve, also sharp on the whole closed interval. -/
theorem earlier_second_radical (x : ℝ) (hx : x ∈ Icc (-1/8 : ℝ) (1/4)) :
    upperRho x=x+3/8-Real.sqrt 6/36*(Real.sqrt (1-4*x))^3 := by
  let v := (Real.sqrt 6/12)*Real.sqrt (1-4*x)
  have h6 : (Real.sqrt 6)^2=6 := Real.sq_sqrt (by norm_num)
  have hz : (Real.sqrt (1-4*x))^2=1-4*x := Real.sq_sqrt (by linarith [hx.2])
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv2 : v^2=(1-4*x)/24 := by
    dsimp [v]
    rw [mul_pow,div_pow,h6,hz]
    ring
  have hv3 : 8*v^3=Real.sqrt 6/36*(Real.sqrt (1-4*x))^3 := by
    dsimp [v]
    rw [mul_pow,div_pow,pow_succ (Real.sqrt 6) 2,h6]
    ring
  have hv1 : v ≤ 1/4 := by nlinarith [hx.1]
  let S : RhoFootrule.RightData := ⟨1,by omega,v,1/4-v,hv0,by linarith,by norm_num⟩
  have hf : (RhoFootrule.UpperParameter.right S).footrule=x := by
    dsimp [RhoFootrule.UpperParameter.footrule,S]
    norm_num
    nlinarith [hv2]
  have hr : (RhoFootrule.UpperParameter.right S).rho=x+3/8-Real.sqrt 6/36*(Real.sqrt (1-4*x))^3 := by
    dsimp [RhoFootrule.UpperParameter.rho,S]
    norm_num
    nlinarith [hv2,hv3]
  rw [← hf,upperRho_parameter,hr,hf]

theorem earlier_endpoint : upperRho 1=1 := upperRho_parameter RhoFootrule.UpperParameter.endpoint


theorem oldContactRho_eq_quadratic (N : ℕ) (hN : 0 < N) :
    oldContactRho N=1-(2/3)*(1-oldContact N)^2 := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  unfold oldContactRho oldContact
  field_simp
  ring

theorem earlier_contact (N : ℕ) (hN : 2 ≤ N) :
    upperRho (oldContact N)=oldLeftLine N (oldContact N) := by
  rw [upperRho_oldContact N (by omega)]
  simp [oldLeftLine]


end Papers.AnsariRockel2026RhoFootrule
