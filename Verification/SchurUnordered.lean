import Verification.ConditionalEnergy
import Copula.Order.Schur
import Copula.Rank.Region.XiBeta.SharpBound
import Copula.Families.Nelsen
import Copula.Families.Nelsen2Limits
import Copula.Families.PowerFamilyLimits

/-! # Families that are unordered in the Schur order

A parameter family starting at the lower Fréchet bound `W` and tending to `M` cannot be
Schur-monotone in either direction as soon as one member has median conditional energy
strictly below `1/2`: `W` and `M` both have energy `1/2`, and the median strip inequality
forces energy close to `1/2` near `M`.
-/

open MeasureTheory ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem countermonotonic_median_energy :
    (∫ u : I, countermonotonic.conditionalCDF u unitHalf ^ 2)=(1/2:ℝ) := by
  have hd : ∀ᵐ x ∂countermonotonic.toMeasure, x 1=unitInterval.symm (x 0) := by
    rw [toMeasure_countermonotonic]
    apply (ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2
    exact Eventually.of_forall fun _ => rfl
  have hh := countermonotonic.integral_conditionalCDF_of_function
    unitInterval.measurable_symm hd unitHalf (fun x => x^(2:ℕ))
  norm_num [unitHalf] at hh ⊢
  exact hh

/-- A copula with median energy below `1/2` is not Schur-above `W`. -/
theorem not_countermonotonic_schurLE (C : Copula 2)
    (hC : (∫ u : I, C.conditionalCDF u unitHalf ^ 2)<(1/2:ℝ)) :
    ¬ countermonotonic.SchurLE C := by
  intro h
  have hm := h unitHalf (fun x => x^2) (by fun_prop)
    ((convexOn_pow (𝕜 := ℝ) 2).subset (fun _ hx => hx.1) (convex_Icc 0 1))
  rw [countermonotonic_median_energy] at hm
  exact (not_le.mpr hC) hm

/-- Copulas converging to `M` at the median eventually are not Schur-below a copula with
median energy below `1/2`. -/
theorem not_schurLE_of_tendsto_comonotonic {α : Type*} {l : Filter α} [l.NeBot]
    (C : α → Copula 2) (D : Copula 2)
    (hC : Tendsto (fun a => (C a).cdf ![unitHalf,unitHalf]) l (𝓝 (1/2:ℝ)))
    (hD : (∫ u : I, D.conditionalCDF u unitHalf ^ 2)<(1/2:ℝ)) :
    ¬ ∀ a, (C a).SchurLE D := by
  intro h
  have hl : Tendsto (fun a => (2*(C a).cdf ![unitHalf,unitHalf]-(1/2:ℝ))^2)
      l (𝓝 (1/4:ℝ)) := by
    convert ((hC.const_mul 2).sub_const (1/2)).pow 2 using 1
    norm_num
  have hb (a : α) :
      (2*(C a).cdf ![unitHalf,unitHalf]-(1/2:ℝ))^2 ≤
        (∫ u : I, D.conditionalCDF u unitHalf ^ 2)-(1/4:ℝ) := by
    have hi := h a unitHalf (fun z => z^2) (by fun_prop)
      ((convexOn_pow (𝕜 := ℝ) 2).subset (fun _ hz => hz.1) (convex_Icc 0 1))
    have hs := RankRegion.XiBeta.median_strip_energy (C a) unitHalf
    norm_num [RankRegion.XiBeta.medianDisplacement,unitHalf] at hs hi ⊢
    linarith
  have hb' := le_of_tendsto hl (Eventually.of_forall hb)
  linarith

theorem comonotonic_median_cdf : (comonotonic 2).cdf ![unitHalf,unitHalf]=(1/2:ℝ) := by
  rw [cdf_comonotonic_two]; norm_num [unitHalf]

/-! ## Nelsen 2 -/

theorem nelsen2_two_section (v : I) (hv : (v:ℝ)=1/2) {u : ℝ} (hu : u∈Ioo (1/4:ℝ) 1) :
    cdfSection (nelsen2 2 (by norm_num)) v u=1-Real.sqrt ((1-u)^2+(1-(v:ℝ))^2) := by
  have hu0 : (⟨u,by linarith [hu.1],hu.2.le⟩ : I)≠0 := fun e => by
    have := congrArg Subtype.val e; simp at this; linarith [hu.1]
  have hv0 : v≠0 := fun e => by rw [e] at hv; norm_num at hv
  dsimp only [cdfSection]
  rw [projIcc_of_mem zero_le_one ⟨by linarith [hu.1],hu.2.le⟩,nelsen2_cdf_full]
  rw [ite_eq_right (by rintro (h|h); exacts [hu0 h,hv0 h])]
  simp only
  rw [show ((2:ℝ))⁻¹=1/2 by norm_num,← Real.sqrt_eq_rpow,Real.rpow_two,Real.rpow_two]
  apply max_eq_right
  rw [hv]
  have h1 : (1-u)^2<9/16 := by nlinarith [hu.1,hu.2]
  have : Real.sqrt ((1-u)^2+(1-1/2)^2)≤1 := by
    rw [Real.sqrt_le_one]
    nlinarith
  linarith

theorem nelsen2_two_median_energy_lt :
    (∫ u : I, (nelsen2 2 (by norm_num)).conditionalCDF u unitHalf ^ 2)<(1/2:ℝ) := by
  have hv : ((unitHalf:I):ℝ)=1/2 := rfl
  let g : I → ℝ := fun u => (1-(u:ℝ))/Real.sqrt ((1-(u:ℝ))^2+(1-1/2)^2)
  have hpos (x : ℝ) : 0<(1-x)^2+(1-1/2:ℝ)^2 := by positivity
  have hg : ContinuousAt g unitHalf := by
    apply ContinuousAt.div
    · fun_prop
    · exact (Real.continuous_sqrt.comp (by fun_prop)).continuousAt
    · exact (Real.sqrt_pos.mpr (hpos _)).ne'
  have hd : ∀ᶠ u in 𝓝 unitHalf, HasDerivAt (cdfSection (nelsen2 2 (by norm_num)) unitHalf) (g u) (u:ℝ) := by
    have hmem : ∀ᶠ u : I in 𝓝 unitHalf, (u:ℝ)∈Ioo (1/4:ℝ) 1 :=
      continuous_subtype_val.continuousAt (Ioo_mem_nhds (by norm_num [unitHalf]) (by norm_num [unitHalf]))
    filter_upwards [hmem] with u hu
    have hloc : cdfSection (nelsen2 2 (by norm_num)) unitHalf=ᶠ[𝓝 (u:ℝ)]
        fun x => 1-Real.sqrt ((1-x)^2+(1-1/2)^2) := by
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
      rw [nelsen2_two_section unitHalf hv hx,hv]
    apply HasDerivAt.congr_of_eventuallyEq _ hloc
    have hin : HasDerivAt (fun x : ℝ => (1-x)^2+(1-1/2:ℝ)^2) (2*(1-(u:ℝ))*(-1)) u := by
      have := ((hasDerivAt_id (u:ℝ)).const_sub 1).pow 2
      simpa using this.add_const ((1-1/2:ℝ)^2)
    have hs := (hin.sqrt (hpos _).ne').const_sub 1
    convert hs using 1
    have hq := Real.sqrt_pos.mpr (hpos (u:ℝ))
    simp only [g]
    field_simp
  have hval : g unitHalf=Real.sqrt (1/2) := by
    simp only [g,hv]
    rw [show (1-1/2:ℝ)^2+(1-1/2)^2=1/2 by norm_num]
    rw [div_eq_iff (Real.sqrt_pos.mpr (by norm_num)).ne']
    rw [← Real.sqrt_mul (by norm_num),show (1/2:ℝ)*(1/2)=(1/2)^2 by norm_num,Real.sqrt_sq (by norm_num)]
    norm_num
  have h0 : 0<g unitHalf := by rw [hval]; exact Real.sqrt_pos.mpr (by norm_num)
  have h1 : g unitHalf<1 := by
    rw [hval,Real.sqrt_lt' (by norm_num)]
    norm_num
  exact conditional_energy_lt_of_local_deriv _ unitHalf unitHalf g hg hd h0 h1

theorem nelsen2_not_schur_monotone :
    ¬ (∀ (θ η : ℝ) (hθ : 1≤θ) (hθη : θ≤η),
      (nelsen2 θ hθ).SchurLE (nelsen2 η (hθ.trans hθη))) := by
  intro h
  have hh := h 1 2 le_rfl (by norm_num)
  rw [nelsen2_one] at hh
  exact not_countermonotonic_schurLE _ nelsen2_two_median_energy_lt hh

theorem nelsen2_not_schur_antitone :
    ¬ (∀ (θ η : ℝ) (hθ : 1≤θ) (hθη : θ≤η),
      (nelsen2 η (hθ.trans hθη)).SchurLE (nelsen2 θ hθ)) := by
  intro h
  let θ : ℝ → ℝ := fun x => max 2 x
  have hθ (x : ℝ) : 1≤θ x := (by norm_num : (1:ℝ)≤2).trans (le_max_left _ _)
  have ht : Tendsto θ atTop atTop := tendsto_atTop_mono (fun x => le_max_right 2 x) tendsto_id
  have hc := tendsto_nelsen2_atTop θ hθ ht ![unitHalf,unitHalf]
  rw [comonotonic_median_cdf] at hc
  exact not_schurLE_of_tendsto_comonotonic (fun x => nelsen2 (θ x) (hθ x)) _ hc
    nelsen2_two_median_energy_lt (fun x => h 2 (θ x) (by norm_num) (le_max_left _ _))

/-! ## Genest–Ghoudi (Nelsen 15) -/

theorem genestGhoudi_two_section (v : I) (hv : (v:ℝ)=1/2) {u : ℝ} (hu : u∈Ioo (1/4:ℝ) 1) :
    cdfSection (genestGhoudi 2 (by norm_num)) v u=
      (1-Real.sqrt ((1-Real.sqrt u)^2+(1-Real.sqrt (v:ℝ))^2))^2 := by
  have hu0 : (⟨u,by linarith [hu.1],hu.2.le⟩ : I)≠0 := fun e => by
    have := congrArg Subtype.val e; simp at this; linarith [hu.1]
  have hv0 : v≠0 := fun e => by rw [e] at hv; norm_num at hv
  dsimp only [cdfSection]
  rw [projIcc_of_mem zero_le_one ⟨by linarith [hu.1],hu.2.le⟩,genestGhoudi_cdf_full]
  rw [ite_eq_right (by rintro (h|h); exacts [hu0 h,hv0 h])]
  simp only
  rw [show ((2:ℝ))⁻¹=1/2 by norm_num,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow,
    Real.rpow_two,Real.rpow_two,Real.rpow_two]
  congr 1
  apply max_eq_right
  rw [hv]
  have hs1 : Real.sqrt (1/2)≤1 := by rw [Real.sqrt_le_one]; norm_num
  have hs0 : 0≤Real.sqrt (1/2) := Real.sqrt_nonneg _
  have hu1 : Real.sqrt u≤1 := by rw [Real.sqrt_le_one]; linarith [hu.2]
  have hu2 : 1/2≤Real.sqrt u := by
    rw [Real.le_sqrt (by norm_num) (by linarith [hu.1])]
    linarith [hu.1]
  have hs2 : 1/2≤Real.sqrt (1/2) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have : Real.sqrt ((1-Real.sqrt u)^2+(1-Real.sqrt (1/2))^2)≤1 := by
    rw [Real.sqrt_le_one]
    have ha : (1-Real.sqrt u)^2≤1/4 := by nlinarith
    have hb : (1-Real.sqrt (1/2))^2≤1/4 := by nlinarith
    linarith
  linarith

theorem genestGhoudi_two_median_energy_lt :
    (∫ u : I, (genestGhoudi 2 (by norm_num)).conditionalCDF u unitHalf ^ 2)<(1/2:ℝ) := by
  have hv : ((unitHalf:I):ℝ)=1/2 := rfl
  set s : ℝ := Real.sqrt (1/2) with hs
  have hs0 : 0<s := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : s^2=1/2 := Real.sq_sqrt (by norm_num)
  have hs1 : s<1 := by nlinarith
  let S : ℝ → ℝ := fun x => (1-Real.sqrt x)^2+(1-s)^2
  have hSpos (x : ℝ) : 0<S x := by
    have : 0<(1-s)^2 := by nlinarith
    positivity
  let g : I → ℝ := fun u => 2*(1-Real.sqrt (S u))*((1-Real.sqrt (u:ℝ))/(2*Real.sqrt (u:ℝ)*Real.sqrt (S u)))
  have hg : ContinuousAt g unitHalf := by
    have hcS : Continuous (fun u : I => S u) := by simp only [S]; fun_prop
    have hsq : ContinuousAt (fun u : I => Real.sqrt (S u)) unitHalf :=
      (Real.continuous_sqrt.comp hcS).continuousAt
    have hsu : ContinuousAt (fun u : I => Real.sqrt (u:ℝ)) unitHalf :=
      (Real.continuous_sqrt.comp continuous_subtype_val).continuousAt
    apply ContinuousAt.mul
    · exact continuousAt_const.mul (continuousAt_const.sub hsq)
    · apply ContinuousAt.div (continuousAt_const.sub hsu) ((continuousAt_const.mul hsu).mul hsq)
      show 2*Real.sqrt ((unitHalf:I):ℝ)*Real.sqrt (S ((unitHalf:I):ℝ))≠0
      rw [hv]
      exact (mul_pos (mul_pos (by norm_num) hs0) (Real.sqrt_pos.mpr (hSpos _))).ne'
  have hd : ∀ᶠ u in 𝓝 unitHalf, HasDerivAt (cdfSection (genestGhoudi 2 (by norm_num)) unitHalf) (g u) (u:ℝ) := by
    have hmem : ∀ᶠ u : I in 𝓝 unitHalf, (u:ℝ)∈Ioo (1/4:ℝ) 1 :=
      continuous_subtype_val.continuousAt (Ioo_mem_nhds (by norm_num [unitHalf]) (by norm_num [unitHalf]))
    filter_upwards [hmem] with u hu
    have hloc : cdfSection (genestGhoudi 2 (by norm_num)) unitHalf=ᶠ[𝓝 (u:ℝ)]
        fun x => (1-Real.sqrt (S x))^2 := by
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
      rw [genestGhoudi_two_section unitHalf hv hx,hv]
    apply HasDerivAt.congr_of_eventuallyEq _ hloc
    have hu0 : 0<(u:ℝ) := by linarith [hu.1]
    have hsu := Real.sqrt_pos.mpr hu0
    have hr : HasDerivAt (fun x : ℝ => Real.sqrt x) (1/(2*Real.sqrt (u:ℝ))) u :=
      (hasDerivAt_id (u:ℝ)).sqrt hu0.ne' |>.congr_deriv (by simp)
    have hin : HasDerivAt S (2*(1-Real.sqrt (u:ℝ))*(-(1/(2*Real.sqrt (u:ℝ))))) u := by
      have := (hr.const_sub 1).pow 2
      simpa [S] using this.add_const ((1-s)^2)
    have hq := ((hin.sqrt (hSpos _).ne').const_sub 1).pow 2
    convert hq using 1
    have hSq := Real.sqrt_pos.mpr (hSpos (u:ℝ))
    simp only [g]
    field_simp
    ring
  -- evaluation at the median: `g(1/2)=2-√2`
  have hS : Real.sqrt (S (1/2))=Real.sqrt 2*(1-s) := by
    have hSv : S (1/2)=2*(1-s)^2 := by simp only [S,← hs]; ring
    rw [hSv,Real.sqrt_mul (by norm_num),Real.sqrt_sq (by linarith)]
  have h2s : Real.sqrt 2*s=1 := by
    rw [hs,← Real.sqrt_mul (by norm_num)]; norm_num
  have hval : g unitHalf=2-Real.sqrt 2 := by
    simp only [g,hv]
    rw [hS,← hs]
    have h1s : 0<1-s := by linarith
    have hr2 : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    field_simp
    nlinarith [h2s]
  have hr2 : Real.sqrt 2<2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hr1 : 1<Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h0 : 0<g unitHalf := by rw [hval]; linarith
  have h1 : g unitHalf<1 := by rw [hval]; linarith
  exact conditional_energy_lt_of_local_deriv _ unitHalf unitHalf g hg hd h0 h1

theorem genestGhoudi_not_schur_monotone :
    ¬ (∀ (θ η : ℝ) (hθ : 1≤θ) (hθη : θ≤η),
      (genestGhoudi θ hθ).SchurLE (genestGhoudi η (hθ.trans hθη))) := by
  intro h
  have hh := h 1 2 le_rfl (by norm_num)
  rw [genestGhoudi_one] at hh
  exact not_countermonotonic_schurLE _ genestGhoudi_two_median_energy_lt hh

theorem genestGhoudi_not_schur_antitone :
    ¬ (∀ (θ η : ℝ) (hθ : 1≤θ) (hθη : θ≤η),
      (genestGhoudi η (hθ.trans hθη)).SchurLE (genestGhoudi θ hθ)) := by
  intro h
  let θ : ℝ → ℝ := fun x => max 2 x
  have hθ (x : ℝ) : 1≤θ x := (by norm_num : (1:ℝ)≤2).trans (le_max_left _ _)
  have ht : Tendsto θ atTop atTop := tendsto_atTop_mono (fun x => le_max_right 2 x) tendsto_id
  have hc := tendsto_genestGhoudi_atTop θ hθ ht ![unitHalf,unitHalf]
  rw [comonotonic_median_cdf] at hc
  exact not_schurLE_of_tendsto_comonotonic (fun x => genestGhoudi (θ x) (hθ x)) _ hc
    genestGhoudi_two_median_energy_lt (fun x => h 2 (θ x) (by norm_num) (le_max_left _ _))

end Verification
