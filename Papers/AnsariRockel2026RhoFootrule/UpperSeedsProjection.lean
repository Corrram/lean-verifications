import Papers.AnsariRockel2026RhoFootrule.UpperSeedsCompact

/-! # The upper seed curves cover every first coordinate -/

open MeasureTheory ProbabilityTheory Verification Set
open scoped unitInterval

namespace Papers.AnsariRockel2026RhoFootrule

theorem upper_branch_covers_below_one (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1) :
    ∃ n : ℕ, ∃ a ∈ Icc (0 : ℝ) (1/2), (upperBranch n a).1 = x := by
  let q := 1-x
  have hq : 0 < q := by dsimp [q]; linarith [hx.2]
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [hx.1]
  let N := ⌊1/q⌋₊
  have hN : 1 ≤ N := (Nat.one_le_floor_iff _).mpr ((one_le_div hq).mpr hq1)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : (N : ℝ)*q ≤ 1 := (le_div_iff₀ hq).mp (Nat.floor_le (by positivity : 0 ≤ 1/q))
  have hU : 1 < ((N : ℝ)+1)*q := (div_lt_iff₀ hq).mp (Nat.lt_floor_add_one (1/q))
  have hc : 1-(N : ℝ)*q ∈ Icc (0 : ℝ) (1/2) := by
    constructor
    · linarith
    · nlinarith [mul_nonneg (sub_nonneg.mpr hNreal) hq.le]
  have hv := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1/2)
    (show ContinuousOn (fun a : ℝ => 2*a^2*(3-4*a)) (Icc 0 (1/2)) from (by fun_prop : Continuous _).continuousOn)
  norm_num only [zero_pow (by decide : 2 ≠ 0),mul_zero,zero_mul,sub_zero] at hv
  obtain ⟨a,ha,he⟩ := hv hc
  obtain ⟨n,hn⟩ : ∃ n, N=n+1 := ⟨N-1,by omega⟩
  refine ⟨n,a,ha,?_⟩
  change 1-(1-2*a^2*(3-4*a))/((n : ℝ)+1)=x
  have hn' : (N : ℝ)=(n : ℝ)+1 := by exact_mod_cast hn
  have hn0 : (n : ℝ)+1 ≠ 0 := by positivity
  rw [hn'] at he
  dsimp [q] at he
  field_simp
  nlinarith only [he]

/-- Every horizontal coordinate in [0,1] occurs in the unconvexified seed set. -/
theorem upper_seed_at_each_x (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ y : ℝ, (x,y) ∈ upperSeeds := by
  by_cases h : x=1
  · subst x; exact ⟨1,Or.inl rfl⟩
  obtain ⟨n,a,ha,he⟩ := upper_branch_covers_below_one x ⟨hx.1,lt_of_le_of_ne hx.2 h⟩
  refine ⟨(upperBranch n a).2,Or.inr (mem_iUnion.mpr ⟨n,a,ha,?_⟩)⟩
  exact Prod.ext he rfl

theorem directional_region_bounds {p : ℝ × ℝ} (hp : p ∈ directionalRegion) :
    p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨C,hx,hy⟩ := hp
  refine ⟨hx ▸ C.chatterjeeXi_mem_Icc,?_⟩
  have h0 : 0 ≤ copulaCorrelationRatio C := correlationRatio_nonneg C
  have h1 := (conditionalCopies C).spearmanRho_mem_Icc.2
  rw [(conditional_copies_coefficients C).2] at h1
  exact hy ▸ ⟨h0,h1⟩

/-- The projection claim in Proposition 2.10. -/
theorem upper_seeds_projection : Prod.fst '' upperSeeds = Icc (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact (directional_region_bounds (upper_seeds_attained hp)).1
  · intro hx
    obtain ⟨y,hy⟩ := upper_seed_at_each_x x hx
    exact ⟨(x,y),hy,rfl⟩

end Papers.AnsariRockel2026RhoFootrule
