import Verification.DecreasingRearrangement
import Mathlib.Analysis.Convex.Slope
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Schur order of functions: rearrangements versus convex tests

For measurable `f g : I → [0,1]`, the rearrangement form of the Schur order
`∫_0^x f* ≤ ∫_0^x g*` (all `x`) with equal integrals is equivalent to
`∫ φ(f) ≤ ∫ φ(g)` for all continuous `φ` convex on `[0,1]` (Hardy–Littlewood–Pólya).
-/

open MeasureTheory Set Filter
open scoped unitInterval Topology

namespace Verification

/-- Schur order of functions via decreasing rearrangements (Ansari–Rockel, Definition 2.2). -/
def RearrSchurLE (f g : I → ℝ) : Prop :=
  (∀ x : I, (∫ s in Iic x, decRearr f s)≤∫ s in Iic x, decRearr g s) ∧ (∫ u, f u)=∫ u, g u

/-- Schur order of functions via continuous convex tests. -/
def ConvexSchurLE (f g : I → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, Continuous φ → ConvexOn ℝ (Icc 0 1) φ → (∫ u, φ (f u))≤∫ u, φ (g u)

section Bounded

variable {f g : I → ℝ}

theorem integrable_of_unit (hf0 : ∀ u, 0≤f u) (hf : ∀ u, f u≤1) (hm : Measurable f)
    {φ : ℝ → ℝ} (hφ : Continuous φ) : Integrable (fun u => φ (f u)) := by
  obtain ⟨b,hb⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn hφ.continuousOn
  exact Integrable.of_bound (hφ.measurable.comp hm).aestronglyMeasurable b
    (Eventually.of_forall fun u => hb _ ⟨hf0 u,hf u⟩)

theorem hinge_continuous (c : ℝ) : Continuous (fun y : ℝ => max (y-c) 0) := by fun_prop

theorem hinge_convex (c : ℝ) : ConvexOn ℝ (Icc 0 1) (fun y : ℝ => max (y-c) 0) := by
  have h1 : ConvexOn ℝ univ (fun y : ℝ => y-c) := (convexOn_id convex_univ).sub (concaveOn_const _ convex_univ)
  exact (h1.sup (convexOn_const 0 convex_univ)).subset (subset_univ _) (convex_Icc 0 1)

theorem integral_hinge_decRearr (hf0 : ∀ u, 0≤f u) (hf : ∀ u, f u≤1) (hm : Measurable f) (c : ℝ) :
    (∫ s : I, max (decRearr f s-c) 0)=∫ u : I, max (f u-c) 0 :=
  integral_comp_decRearr hf0 hf hm (hinge_continuous c).measurable

/-- Partial integrals of an antitone rearrangement at its own level. -/
theorem integral_Iic_decRearr_eq (_hf0 : ∀ u, 0≤f u) (hf : ∀ u, f u≤1) (_hm : Measurable f) (x : I) :
    (∫ s in Iic x, decRearr f s)=decRearr f x*x+∫ s : I, max (decRearr f s-decRearr f x) 0 := by
  set c := decRearr f x
  have hr := decRearr_measurable hf
  have hi : Integrable (fun s : I => max (decRearr f s-c) 0) :=
    integrable_of_unit (fun s => decRearr_nonneg hf s.property.1) (fun s => decRearr_le_one hf s.property.1)
      hr (hinge_continuous c)
  rw [← integral_add_compl measurableSet_Iic hi,compl_Iic]
  have hz : (∫ s in Ioi x, max (decRearr f s-c) 0)=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro s hs
    have : decRearr f s≤c := decRearr_antitoneOn hf x.property.1 s.property.1 (le_of_lt hs)
    exact max_eq_right (by linarith)
  have hl : (∫ s in Iic x, max (decRearr f s-c) 0)=∫ s in Iic x, (decRearr f s-c) := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro s hs
    have : c≤decRearr f s := decRearr_antitoneOn hf s.property.1 x.property.1 hs
    exact max_eq_left (by linarith)
  have hri : IntegrableOn (fun s : I => decRearr f s) (Iic x) :=
    (integrable_of_unit (fun s => decRearr_nonneg hf s.property.1) (fun s => decRearr_le_one hf s.property.1)
      hr continuous_id).integrableOn
  rw [hz,add_zero,hl,integral_sub hri (integrable_const c).integrableOn]
  simp [measureReal_def,unitInterval.volume_Iic,ENNReal.toReal_ofReal x.property.1]
  ring

theorem integral_Iic_le_hinge {h : I → ℝ} (hi : Integrable h) (x : I) (c : ℝ) :
    (∫ s in Iic x, h s)≤c*x+∫ s : I, max (h s-c) 0 := by
  have hmax : Integrable (fun s => max (h s-c) 0) := (hi.sub (integrable_const c)).sup (integrable_zero _ _ _)
  calc (∫ s in Iic x, h s)≤∫ s in Iic x, (c+max (h s-c) 0) := by
        apply setIntegral_mono_on hi.integrableOn ((integrable_const c).add hmax).integrableOn measurableSet_Iic
        intro s _
        show h s ≤ c + max (h s - c) 0
        have := le_max_left (h s-c) 0
        linarith
    _ = c*x+∫ s in Iic x, max (h s-c) 0 := by
        rw [integral_add (integrable_const c).integrableOn hmax.integrableOn]
        simp [measureReal_def,unitInterval.volume_Iic,ENNReal.toReal_ofReal x.property.1]
        ring
    _ ≤ c*x+∫ s : I, max (h s-c) 0 := by
        apply add_le_add le_rfl
        exact setIntegral_le_integral hmax (Eventually.of_forall fun s => le_max_right _ _)

/-- Convex tests imply the rearrangement Schur order. -/
theorem rearrSchurLE_of_convex (hf0 : ∀ u, 0≤f u) (hf : ∀ u, f u≤1) (hfm : Measurable f)
    (hg0 : ∀ u, 0≤g u) (hg : ∀ u, g u≤1) (hgm : Measurable g) (h : ConvexSchurLE f g) :
    RearrSchurLE f g := by
  constructor
  · intro x
    set c := decRearr g x
    have hfi : Integrable (fun s : I => decRearr f s) :=
      integrable_of_unit (fun s => decRearr_nonneg hf s.property.1) (fun s => decRearr_le_one hf s.property.1)
        (decRearr_measurable hf) continuous_id
    calc (∫ s in Iic x, decRearr f s)≤c*x+∫ s : I, max (decRearr f s-c) 0 := integral_Iic_le_hinge hfi x c
      _ = c*x+∫ u : I, max (f u-c) 0 := by rw [integral_hinge_decRearr hf0 hf hfm]
      _ ≤ c*x+∫ u : I, max (g u-c) 0 := add_le_add le_rfl (h _ (hinge_continuous c) (hinge_convex c))
      _ = c*x+∫ s : I, max (decRearr g s-c) 0 := by rw [integral_hinge_decRearr hg0 hg hgm]
      _ = ∫ s in Iic x, decRearr g s := by rw [integral_Iic_decRearr_eq hg0 hg hgm x]
  · have h1 := h id continuous_id (convexOn_id (convex_Icc 0 1))
    have h2 := h (fun y => -y) continuous_neg ((concaveOn_id (convex_Icc 0 1)).neg)
    simp only [id, integral_neg] at h1 h2
    linarith

/-- The rearrangement Schur order implies all hinge comparisons. -/
theorem hinge_le_of_rearrSchurLE (hf0 : ∀ u, 0≤f u) (hf : ∀ u, f u≤1) (hfm : Measurable f)
    (hg0 : ∀ u, 0≤g u) (hg : ∀ u, g u≤1) (hgm : Measurable g) (h : RearrSchurLE f g) (c : ℝ) :
    (∫ u : I, max (f u-c) 0)≤∫ u : I, max (g u-c) 0 := by
  rcases lt_or_ge c 0 with hc|hc
  · have e1 : (fun u => max (f u-c) 0)=fun u => f u-c := by
      funext u; exact max_eq_left (by linarith [hf0 u])
    have e2 : (fun u => max (g u-c) 0)=fun u => g u-c := by
      funext u; exact max_eq_left (by linarith [hg0 u])
    have hfi := integrable_of_unit hf0 hf hfm continuous_id
    have hgi := integrable_of_unit hg0 hg hgm continuous_id
    simp only [id] at hfi hgi
    rw [e1,e2,integral_sub hfi (integrable_const c),integral_sub hgi (integrable_const c)]
    have := h.2
    linarith
  -- `c ≥ 0`: the positive part of `f* - c` lives on an initial segment
  set x0 : I := ⟨distFun f c,distFun_nonneg f c,distFun_le_one f c⟩
  have hri (k : I → ℝ) (hk0 : ∀ u, 0≤k u) (hk : ∀ u, k u≤1) (hkm : Measurable k) :
      Integrable (fun s : I => decRearr k s) :=
    integrable_of_unit (fun s => decRearr_nonneg hk s.property.1) (fun s => decRearr_le_one hk s.property.1)
      (decRearr_measurable hk) continuous_id
  have hkey : (∫ s : I, max (decRearr f s-c) 0)=(∫ s in Iic x0, decRearr f s)-c*x0 := by
    have hi : Integrable (fun s : I => max (decRearr f s-c) 0) :=
      ((hri f hf0 hf hfm).sub (integrable_const c)).sup (integrable_zero _ _ _)
    rw [← integral_add_compl measurableSet_Iic hi,compl_Iic]
    have hz : (∫ s in Ioi x0, max (decRearr f s-c) 0)=0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro s hs
      apply max_eq_right
      have : ¬ c<decRearr f s := by
        rw [lt_decRearr_iff hf hfm hc s.property.1]
        have hlt : (x0:ℝ)<s := Subtype.coe_lt_coe.mpr hs
        exact not_lt.mpr (le_of_lt hlt)
      linarith [not_lt.mp this]
    have hl : (∫ s in Iic x0, max (decRearr f s-c) 0)=∫ s in Iic x0, (decRearr f s-c) := by
      apply setIntegral_congr_ae measurableSet_Iic
      have hne : ∀ᵐ s : I, s≠x0 := by simp [ae_iff]
      filter_upwards [hne] with s hs hmem
      apply max_eq_left
      have hle : (s:ℝ)≤x0 := Subtype.coe_le_coe.mpr hmem
      have hlt : (s:ℝ)<distFun f c :=
        lt_of_le_of_ne hle (fun e => hs (Subtype.ext e))
      have := (lt_decRearr_iff hf hfm hc s.property.1).mpr hlt
      linarith
    rw [hz,add_zero,hl,integral_sub (hri f hf0 hf hfm).integrableOn (integrable_const c).integrableOn]
    simp [measureReal_def,unitInterval.volume_Iic,ENNReal.toReal_ofReal x0.property.1]
    ring
  rw [← integral_hinge_decRearr hf0 hf hfm,hkey,← integral_hinge_decRearr hg0 hg hgm]
  have := integral_Iic_le_hinge (hri g hg0 hg hgm) x0 c
  have := h.1 x0
  linarith

end Bounded

/-! ## Piecewise-linear convex interpolation -/

/-- Slope of the `k`-th cell of the uniform partition with `n` cells. -/
noncomputable def cellSlope (φ : ℝ → ℝ) (n k : ℕ) : ℝ := n*(φ ((k+1:ℕ)/n)-φ (k/n))

/-- Linear interpolation of `φ` at the nodes `k/n`, written with hinge functions. -/
noncomputable def hingeInterp (φ : ℝ → ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  φ 0+cellSlope φ n 0*y+∑ k ∈ Finset.Ico 1 n, (cellSlope φ n k-cellSlope φ n (k-1))*max (y-k/n) 0

theorem cellSlope_mono {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Icc 0 1) φ) {n k : ℕ} (hn : 0<n) (hk : k+1<n) :
    cellSlope φ n k≤cellSlope φ n (k+1) := by
  have hnr : (0:ℝ)<n := by exact_mod_cast hn
  have ha : (k:ℝ)/n∈Icc (0:ℝ) 1 := ⟨by positivity,(div_le_one hnr).mpr (by exact_mod_cast (by omega : k≤n))⟩
  have hb : ((k+1:ℕ):ℝ)/n∈Icc (0:ℝ) 1 :=
    ⟨by positivity,(div_le_one hnr).mpr (by exact_mod_cast (by omega : k+1≤n))⟩
  have hc : ((k+1+1:ℕ):ℝ)/n∈Icc (0:ℝ) 1 :=
    ⟨by positivity,(div_le_one hnr).mpr (by exact_mod_cast (by omega : k+1+1≤n))⟩
  have hab : (k:ℝ)/n<((k+1:ℕ):ℝ)/n := div_lt_div_of_pos_right (by push_cast; linarith) hnr
  have hbc : ((k+1:ℕ):ℝ)/n<((k+1+1:ℕ):ℝ)/n := div_lt_div_of_pos_right (by push_cast; linarith) hnr
  have hs := hφ.slope_mono_adjacent ha hc hab hbc
  unfold cellSlope
  have e1 : ((k+1:ℕ):ℝ)/n-k/n=1/n := by push_cast; field_simp; ring
  have e2 : ((k+1+1:ℕ):ℝ)/n-((k+1:ℕ):ℝ)/n=1/n := by push_cast; field_simp; ring
  rw [e1,e2,div_div_eq_mul_div,div_div_eq_mul_div,div_one,div_one] at hs
  linarith [hs]

/-- Algebraic telescoping identity for the hinge sum without the positive parts. -/
theorem hinge_telescope (φ : ℝ → ℝ) (n : ℕ) (hn : 0<n) (y : ℝ) (j : ℕ) :
    cellSlope φ n 0*y+∑ k ∈ Finset.Ico 1 (j+1), (cellSlope φ n k-cellSlope φ n (k-1))*(y-k/n)=
      cellSlope φ n j*(y-j/n)+(φ (j/n)-φ 0) := by
  have hnr : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_Ico_succ_top (by omega),← add_assoc,ih]
    simp only [Nat.add_sub_cancel]
    unfold cellSlope
    push_cast
    field_simp
    ring

theorem hingeInterp_cell (φ : ℝ → ℝ) {n j : ℕ} (hn : 0<n) (hj : j<n) {y : ℝ}
    (hy : y∈Icc ((j:ℝ)/n) ((j+1:ℕ)/n)) :
    hingeInterp φ n y=φ (j/n)+cellSlope φ n j*(y-j/n) := by
  have hnr : (0:ℝ)<n := by exact_mod_cast hn
  unfold hingeInterp
  -- terms beyond `j` vanish, terms up to `j` are linear
  have hsplit : Finset.Ico 1 n=Finset.Ico 1 (j+1)∪Finset.Ico (j+1) n :=
    (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
  rw [hsplit,Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive _ _ _)]
  have hhigh : ∑ k ∈ Finset.Ico (j+1) n, (cellSlope φ n k-cellSlope φ n (k-1))*max (y-k/n) 0=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    have : y≤k/n := le_trans hy.2 (div_le_div_of_nonneg_right (by exact_mod_cast hk.1) hnr.le)
    rw [max_eq_right (by linarith),mul_zero]
  have hlow : ∑ k ∈ Finset.Ico 1 (j+1), (cellSlope φ n k-cellSlope φ n (k-1))*max (y-k/n) 0=
      ∑ k ∈ Finset.Ico 1 (j+1), (cellSlope φ n k-cellSlope φ n (k-1))*(y-k/n) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Ico] at hk
    have : (k:ℝ)/n≤y := le_trans (div_le_div_of_nonneg_right (by exact_mod_cast (by omega : k≤j)) hnr.le) hy.1
    rw [max_eq_left (by linarith)]
  rw [hhigh,hlow,add_zero,add_assoc,hinge_telescope φ n hn y j]
  ring

/-- Integral comparison for the hinge interpolant. -/
theorem integral_hingeInterp_le {f g : I → ℝ} (hf0 : ∀ u, 0≤f u) (hf : ∀ u, f u≤1) (hfm : Measurable f)
    (hg0 : ∀ u, 0≤g u) (hg : ∀ u, g u≤1) (hgm : Measurable g)
    (hint : (∫ u, f u)=∫ u, g u) (hh : ∀ c, (∫ u : I, max (f u-c) 0)≤∫ u : I, max (g u-c) 0)
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Icc 0 1) φ) {n : ℕ} (hn : 0<n) :
    (∫ u, hingeInterp φ n (f u))≤∫ u, hingeInterp φ n (g u) := by
  have hcont (c : ℝ) : Continuous (fun y => max (y-c) 0) := hinge_continuous c
  have hI (k : I → ℝ) (hk0 : ∀ u, 0≤k u) (hk : ∀ u, k u≤1) (hkm : Measurable k) (c : ℝ) :
      Integrable (fun u => max (k u-c) 0) := integrable_of_unit hk0 hk hkm (hcont c)
  have hexp (k : I → ℝ) (hk0 : ∀ u, 0≤k u) (hk : ∀ u, k u≤1) (hkm : Measurable k) :
      (∫ u, hingeInterp φ n (k u))=φ 0+cellSlope φ n 0*(∫ u, k u)+
        ∑ i ∈ Finset.Ico 1 n, (cellSlope φ n i-cellSlope φ n (i-1))*∫ u, max (k u-i/n) 0 := by
    unfold hingeInterp
    have hki : Integrable (fun u => k u) := integrable_of_unit hk0 hk hkm continuous_id
    have hA : Integrable (fun u => φ 0+cellSlope φ n 0*k u) := (integrable_const _).add (hki.const_mul _)
    have hB : Integrable (fun u => ∑ i ∈ Finset.Ico 1 n,
        (cellSlope φ n i-cellSlope φ n (i-1))*max (k u-i/n) 0) :=
      integrable_finsetSum _ fun i _ => (hI k hk0 hk hkm _).const_mul _
    rw [integral_add hA hB,integral_add (integrable_const _) (hki.const_mul _),
      integral_finsetSum _ fun i _ => (hI k hk0 hk hkm _).const_mul _]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,integral_const_mul]
  rw [hexp f hf0 hf hfm,hexp g hg0 hg hgm,hint]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mem_Ico] at hi
  apply mul_le_mul_of_nonneg_left (hh _)
  have := cellSlope_mono hφ (k := i-1) hn (by omega)
  rw [show i-1+1=i by omega] at this
  linarith

/-- Uniform approximation of a continuous convex function by its hinge interpolants. -/
theorem hingeInterp_approx {φ : ℝ → ℝ} (hφc : Continuous φ) {ε : ℝ} (hε : 0<ε) :
    ∃ n : ℕ, 0<n ∧ ∀ y ∈ Icc (0:ℝ) 1, |hingeInterp φ n y-φ y|≤ε := by
  obtain ⟨δ,hδ,hδε⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc (a := (0:ℝ)) (b := 1)).uniformContinuousOn_of_continuous hφc.continuousOn) ε hε
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n+1,Nat.succ_pos n,?_⟩
  intro y hy
  set N : ℕ := n+1
  have hNr : (0:ℝ)<N := by positivity
  have hstep : 1/(N:ℝ)<δ := by simpa [N] using hn
  -- the cell index
  set j : ℕ := min (⌊y*N⌋₊) n
  have hjN : j<N := by simp only [j,N]; omega
  have hjl : (j:ℝ)/N≤y := by
    rw [div_le_iff₀ hNr]
    calc (j:ℝ)≤⌊y*N⌋₊ := by exact_mod_cast min_le_left _ _
      _ ≤ y*N := Nat.floor_le (by nlinarith [hy.1])
  have hju : y≤((j+1:ℕ):ℝ)/N := by
    rw [le_div_iff₀ hNr]
    by_cases hcase : ⌊y*N⌋₊≤n
    · have : j=⌊y*N⌋₊ := min_eq_left hcase
      rw [this]
      exact le_of_lt (by exact_mod_cast Nat.lt_floor_add_one (y*N))
    · have : j=n := min_eq_right (by omega)
      rw [this]
      have hN : (N:ℝ)=n+1 := by simp [N]
      push_cast
      rw [hN]
      nlinarith [hy.2]
  rw [hingeInterp_cell φ (Nat.succ_pos n) hjN ⟨hjl,hju⟩]
  set a : ℝ := (j:ℝ)/N
  set b : ℝ := ((j+1:ℕ):ℝ)/N
  have hba : b-a=1/N := by simp only [a,b]; push_cast; field_simp; ring
  have ha01 : a∈Icc (0:ℝ) 1 := ⟨by positivity,le_trans hjl hy.2⟩
  have hb01 : b∈Icc (0:ℝ) 1 := ⟨by positivity,(div_le_one hNr).mpr (by exact_mod_cast hjN)⟩
  have hdist (z : ℝ) (hz : z∈Icc a b) (hz01 : z∈Icc (0:ℝ) 1) : |φ z-φ y|≤ε := by
    have h1 : dist z y<δ := by
      rw [Real.dist_eq,abs_lt]
      constructor <;> linarith [hz.1,hz.2,hjl,hju]
    exact le_of_lt (by simpa [Real.dist_eq] using hδε z hz01 y hy h1)
  have hA := hdist a ⟨le_rfl,by linarith⟩ ha01
  have hB := hdist b ⟨by linarith,le_rfl⟩ hb01
  -- convex combination form
  set t : ℝ := (y-a)*N
  have ht0 : 0≤t := by simp only [t]; nlinarith
  have ht1 : t≤1 := by
    simp only [t]
    have : y-a≤1/N := by linarith
    calc (y-a)*N≤1/N*N := mul_le_mul_of_nonneg_right this hNr.le
      _ = 1 := by field_simp
  have hform : φ a+cellSlope φ N j*(y-a)-φ y=(1-t)*(φ a-φ y)+t*(φ b-φ y) := by
    simp only [cellSlope,t,a,b]
    ring
  rw [hform]
  calc |(1-t)*(φ a-φ y)+t*(φ b-φ y)|≤(1-t)*|φ a-φ y|+t*|φ b-φ y| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul,abs_mul,abs_of_nonneg (by linarith),abs_of_nonneg ht0]
    _ ≤ (1-t)*ε+t*ε := by gcongr
    _ = ε := by ring

/-- Majorization in the hinge form implies all continuous convex comparisons. -/
theorem convexSchurLE_of_hinge {f g : I → ℝ} (hf0 : ∀ u, 0≤f u) (hf : ∀ u, f u≤1) (hfm : Measurable f)
    (hg0 : ∀ u, 0≤g u) (hg : ∀ u, g u≤1) (hgm : Measurable g)
    (hint : (∫ u, f u)=∫ u, g u) (hh : ∀ c, (∫ u : I, max (f u-c) 0)≤∫ u : I, max (g u-c) 0) :
    ConvexSchurLE f g := by
  intro φ hφc hφ
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨n,hn,happ⟩ := hingeInterp_approx hφc (half_pos hε)
  have hL := integral_hingeInterp_le hf0 hf hfm hg0 hg hgm hint hh hφ hn
  have hLc : Continuous (hingeInterp φ n) := by
    unfold hingeInterp
    exact (continuous_const.add (continuous_const.mul continuous_id)).add
      (continuous_finsetSum _ fun k _ => continuous_const.mul (hinge_continuous _))
  have hcmp (k : I → ℝ) (hk0 : ∀ u, 0≤k u) (hk : ∀ u, k u≤1) (hkm : Measurable k) :
      |(∫ u, hingeInterp φ n (k u))-∫ u, φ (k u)|≤ε/2 := by
    rw [← integral_sub (integrable_of_unit hk0 hk hkm hLc) (integrable_of_unit hk0 hk hkm hφc)]
    calc |∫ u, (hingeInterp φ n (k u)-φ (k u))|≤∫ u, |hingeInterp φ n (k u)-φ (k u)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _u : I, ε/2 := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
          exact Eventually.of_forall fun u => happ _ ⟨hk0 u,hk u⟩
      _ = ε/2 := by simp
  have h1 := hcmp f hf0 hf hfm
  have h2 := hcmp g hg0 hg hgm
  rw [abs_le] at h1 h2
  linarith [h1.1,h2.2]

/-- Hardy–Littlewood–Pólya on the unit interval, for `[0,1]`-valued functions. -/
theorem rearrSchurLE_iff_convex {f g : I → ℝ} (hf0 : ∀ u, 0≤f u) (hf : ∀ u, f u≤1) (hfm : Measurable f)
    (hg0 : ∀ u, 0≤g u) (hg : ∀ u, g u≤1) (hgm : Measurable g) :
    RearrSchurLE f g ↔ ConvexSchurLE f g :=
  ⟨fun h => convexSchurLE_of_hinge hf0 hf hfm hg0 hg hgm h.2
      (hinge_le_of_rearrSchurLE hf0 hf hfm hg0 hg hgm h),
    rearrSchurLE_of_convex hf0 hf hfm hg0 hg hgm⟩

end Verification
