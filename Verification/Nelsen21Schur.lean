import Verification.ConditionalEnergy
import Verification.Nelsen21Limits
import Verification.Nelsen21Dependence
import Copula.Order.Schur
import Copula.Rank.Region.XiBeta.SharpBound

open MeasureTheory ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem n21CorePrime_neg {θ t : ℝ} (hθ : 0 < θ) (ht : t ∈ Ioo 0 1) :
    n21CorePrime θ t < 0 := by
  have hx : 0 < 1-t := by linarith [ht.2]
  have hb : 0 < 1-(1-t)^θ := sub_pos.mpr (Real.rpow_lt_one hx.le (by linarith [ht.1]) hθ)
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.rpow_pos_of_pos hx _))
    (Real.rpow_pos_of_pos hb _)

theorem n21CorePrime_strictMono {θ : ℝ} (hθ : 1 < θ) :
    StrictMonoOn (n21CorePrime θ) (Ioo 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · intro t ht
    exact (n21Core_deriv2 (by linarith) ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0:ℝ) 1 := interior_subset ht
    rw [(n21Core_deriv2 (by linarith : 0 < θ) ht').deriv]
    have hx : 0 < 1-t := by linarith [ht'.2]
    have hb : 0 < 1-(1-t)^θ := sub_pos.mpr (Real.rpow_lt_one hx.le (by linarith [ht'.1]) (by linarith))
    exact mul_pos (mul_pos (sub_pos.mpr hθ) (Real.rpow_pos_of_pos hx _)) (Real.rpow_pos_of_pos hb _)

theorem n21Core_interior {θ t : ℝ} (hθ : 0 < θ) (ht : t ∈ Ioo 0 1) :
    n21Core θ t ∈ Ioo (0:ℝ) 1 := by
  refine ⟨n21Core_pos hθ ⟨ht.1.le,ht.2⟩,?_⟩
  have hx : 0 < 1-t := by linarith [ht.2]
  have hb : 0 < 1-(1-t)^θ := sub_pos.mpr (Real.rpow_lt_one hx.le (by linarith [ht.1]) hθ)
  dsimp [n21Core]
  linarith [Real.rpow_pos_of_pos hb θ⁻¹]

theorem n21CorePrime_inverse {θ t : ℝ} (hθ : 0 < θ) (ht : t ∈ Ioo 0 1) :
    n21CorePrime θ (n21Core θ t) * n21CorePrime θ t = 1 := by
  have hh := (n21Core_deriv hθ (n21Core_interior hθ ht)).comp t (n21Core_deriv hθ ht)
  have he : (fun x => n21Core θ (n21Core θ x)) =ᶠ[𝓝 t] id := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact n21Core_involutive hθ ⟨hx.1.le,hx.2.le⟩
  exact (hh.congr_of_eventuallyEq he.symm).unique (hasDerivAt_id t)

theorem nelsen21_section_deriv {θ : ℝ} (hθ : 1 ≤ θ) (v : I) {u : ℝ}
    (hu : u ∈ Ioo 0 1) (hv : 0 < (v : ℝ))
    (hs : n21Core θ u + n21Core θ v ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (cdfSection (nelsen21 θ hθ) v)
      (n21CorePrime θ (n21Core θ u+n21Core θ v)*n21CorePrime θ u) u := by
  have hp : 0 < θ := by linarith
  have hh := (n21Core_deriv hp hs).comp u ((n21Core_deriv hp hu).add_const (n21Core θ v))
  apply hh.congr_of_eventuallyEq
  have hc := ((n21Core_continuous hp).continuousAt (x := u)).add_const (n21Core θ v)
  filter_upwards [Ioo_mem_nhds hu.1 hu.2, hc (Iio_mem_nhds hs.2)] with x hx hsum
  dsimp only [cdfSection, Function.comp_def]
  rw [projIcc_of_mem zero_le_one ⟨hx.1.le,hx.2.le⟩]
  have hx0 : (⟨x,⟨hx.1.le,hx.2.le⟩⟩ : I) ≠ 0 := by
    intro he; have := congrArg Subtype.val he; dsimp at this; linarith [hx.1]
  have hv0 : v ≠ 0 := by intro he; subst v; exact lt_irrefl 0 hv
  simp only [nelsen21,BivariateGenerator.cdf_copula,BivariateGenerator.cdf,
    Matrix.cons_val_zero,Matrix.cons_val_one,hx0,hv0,or_self,ite_false]
  change n21Psi θ (n21Core θ x+n21Core θ v) = _
  exact congrArg (n21Core θ) (min_eq_left hsum.le)

theorem nelsen21_two_median_energy_lt :
    (∫ u : I, (nelsen21 2 (by norm_num)).conditionalCDF u unitHalf ^ 2) < (1/2:ℝ) := by
  have ht : (1/2:ℝ) ∈ Ioo (0:ℝ) 1 := by norm_num
  have hp : 0 < (2:ℝ) := by norm_num
  have hq := n21Core_interior hp ht
  have hbound : n21Core 2 (1/2) ≤ (1/4:ℝ) := by
    have hh := n21Core_upper_bound (θ := 2) (by norm_num) ⟨ht.1.le,ht.2.le⟩
    norm_num [Real.rpow_two] at hh ⊢
    exact hh
  have hs : n21Core 2 (1/2)+n21Core 2 (1/2) ∈ Ioo (0:ℝ) 1 := by
    constructor <;> linarith [hq.1]
  let g : I → ℝ := fun u => n21CorePrime 2 (n21Core 2 u+n21Core 2 (1/2))*n21CorePrime 2 u
  have hg : ContinuousAt g unitHalf := by
    have hi := (n21Core_continuous hp).continuousAt.comp (continuous_subtype_val.continuousAt (x := unitHalf))
    exact (((n21Core_deriv2 hp hs).continuousAt.comp
      (f := fun u : I => n21Core 2 u+n21Core 2 (1/2)) (x := unitHalf) (hi.add_const _)).mul
      ((n21Core_deriv2 hp ht).continuousAt.comp (f := fun u : I => (u : ℝ))
        (x := unitHalf) continuous_subtype_val.continuousAt))
  have hd : ∀ᶠ u in 𝓝 unitHalf, HasDerivAt (cdfSection (nelsen21 2 (by norm_num)) unitHalf) (g u) (u : ℝ) := by
    have hi := (n21Core_continuous hp).continuousAt.comp (continuous_subtype_val.continuousAt (x := unitHalf))
    have hn := (hi.add_const (n21Core 2 (1/2))) (Ioo_mem_nhds hs.1 hs.2)
    filter_upwards [continuous_subtype_val.continuousAt (Ioo_mem_nhds ht.1 ht.2), hn] with u hu hsum
    exact nelsen21_section_deriv (by norm_num) unitHalf hu (by norm_num [unitHalf]) hsum
  have hn := n21CorePrime_neg hp ht
  have hns := n21CorePrime_neg hp hs
  have hm := n21CorePrime_strictMono (θ := 2) (by norm_num) hq hs (by linarith [hq.1])
  have he := n21CorePrime_inverse hp ht
  have h0 : 0 < g unitHalf := mul_pos_of_neg_of_neg hns hn
  have h1 : g unitHalf < 1 := by
    have hh := mul_lt_mul_of_neg_right hm hn
    change n21CorePrime 2 (n21Core 2 (1/2)+n21Core 2 (1/2))*n21CorePrime 2 (1/2) < 1
    linarith
  exact conditional_energy_lt_of_local_deriv _ unitHalf unitHalf g hg hd h0 h1

theorem nelsen21_not_schur_monotone :
    ¬ (∀ (θ η : ℝ) (hθ : 1 ≤ θ) (hθη : θ ≤ η),
      (nelsen21 θ hθ).SchurLE (nelsen21 η (hθ.trans hθη))) := by
  intro h
  have hh := h 1 2 (by norm_num) (by norm_num)
  rw [nelsen21_one] at hh
  have he : (∫ u : I, countermonotonic.conditionalCDF u unitHalf ^ 2) = (1/2:ℝ) := by
    have hd : ∀ᵐ x ∂countermonotonic.toMeasure, x 1 = unitInterval.symm (x 0) := by
      rw [toMeasure_countermonotonic]
      apply (ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2
      exact Eventually.of_forall fun _ => rfl
    have hh := countermonotonic.integral_conditionalCDF_of_function
      unitInterval.measurable_symm hd unitHalf (fun x => x^(2:ℕ))
    norm_num [unitHalf] at hh ⊢
    exact hh
  have hm := hh unitHalf (fun x => x^2) (by fun_prop)
    ((convexOn_pow (𝕜 := ℝ) 2).subset (fun _ hx => hx.1) (convex_Icc 0 1))
  rw [he] at hm
  exact (not_le.mpr nelsen21_two_median_energy_lt) hm

theorem nelsen21_not_schur_antitone :
    ¬ (∀ (θ η : ℝ) (hθ : 1 ≤ θ) (hθη : θ ≤ η),
      (nelsen21 η (hθ.trans hθη)).SchurLE (nelsen21 θ hθ)) := by
  intro h
  let θ : ℝ → ℝ := fun x => max 2 x
  have hθ (x : ℝ) : 1 ≤ θ x := (by norm_num : (1:ℝ) ≤ 2).trans (le_max_left _ _)
  have ht : Tendsto θ atTop atTop := tendsto_atTop_mono (fun x => le_max_right 2 x) tendsto_id
  have hc := nelsen21_tendsto_atTop θ hθ ht unitHalf unitHalf
  have he : (comonotonic 2).cdf ![unitHalf,unitHalf] = (1/2:ℝ) := by
    rw [cdf_comonotonic_two]; norm_num [unitHalf]
  rw [he] at hc
  have hl : Tendsto (fun x => (2*(nelsen21 (θ x) (hθ x)).cdf ![unitHalf,unitHalf]-(1/2:ℝ))^2)
      atTop (𝓝 (1/4:ℝ)) := by
    convert ((hc.const_mul 2).sub_const (1/2)).pow 2 using 1
    norm_num
  have hb (x : ℝ) :
      (2*(nelsen21 (θ x) (hθ x)).cdf ![unitHalf,unitHalf]-(1/2:ℝ))^2 ≤
        (∫ u : I, (nelsen21 2 (by norm_num)).conditionalCDF u unitHalf ^ 2)-(1/4:ℝ) := by
    have hm := h 2 (θ x) (by norm_num) (le_max_left _ _)
    have hi := hm unitHalf (fun z => z^2) (by fun_prop)
      ((convexOn_pow (𝕜 := ℝ) 2).subset (fun _ hz => hz.1) (convex_Icc 0 1))
    have hs := RankRegion.XiBeta.median_strip_energy (nelsen21 (θ x) (hθ x)) unitHalf
    norm_num [RankRegion.XiBeta.medianDisplacement,unitHalf] at hs hi ⊢
    linarith
  have hb' := le_of_tendsto hl (Eventually.of_forall hb)
  linarith [nelsen21_two_median_energy_lt]

end Verification
