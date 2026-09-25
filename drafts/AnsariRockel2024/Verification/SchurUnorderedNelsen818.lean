import Verification.SchurUnordered
import Verification.Nelsen18Limits
import Copula.Families.Nelsen8
import Copula.Families.Nelsen8Limits
import Copula.Families.Clayton
import Copula.Rank.ConditionalDerivative

/-! # Schur non-monotonicity for Nelsen 8 and Nelsen 18

Nelsen 8 starts at `W` and tends to Clayton(1); an exact conditional energy computation at
`θ=5`, threshold `1/4`, and the strip inequality for the Clayton(1) limit exclude a
decreasing Schur order. Nelsen 18 tends to `M`; its `θ=2` member has median energy below
`1/2`, which excludes a decreasing Schur order.
-/

open MeasureTheory ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

/-! ## Nelsen 8 -/

theorem nelsen8_two_section {u : ℝ} (hu : u∈Ioo (1/4:ℝ) 1) :
    cdfSection (nelsen8 2 (by norm_num)) unitHalf u=(5*u-1)/(7+u) := by
  dsimp only [cdfSection]
  rw [projIcc_of_mem zero_le_one ⟨by linarith [hu.1],hu.2.le⟩,nelsen8_cdf_full]
  simp only [unitHalf]
  have hd : (0:ℝ)<7+u := by linarith [hu.1]
  have he : ((2:ℝ)^2*u*(1/2)-(1-u)*(1-1/2))/(2^2-(2-1)^2*(1-u)*(1-1/2))=(5*u-1)/(7+u) := by
    field_simp
    ring
  rw [he]
  exact max_eq_right (div_nonneg (by linarith [hu.1]) hd.le)

theorem nelsen8_two_median_energy_lt :
    (∫ u : I, (nelsen8 2 (by norm_num)).conditionalCDF u unitHalf ^ 2)<(1/2:ℝ) := by
  let g : I → ℝ := fun u => 36/(7+(u:ℝ))^2
  have hg : ContinuousAt g unitHalf := by
    apply ContinuousAt.div continuousAt_const (by fun_prop)
    simp only [unitHalf]; norm_num
  have hd : ∀ᶠ u in 𝓝 unitHalf, HasDerivAt (cdfSection (nelsen8 2 (by norm_num)) unitHalf) (g u) (u:ℝ) := by
    have hmem : ∀ᶠ u : I in 𝓝 unitHalf, (u:ℝ)∈Ioo (1/4:ℝ) 1 :=
      continuous_subtype_val.continuousAt (Ioo_mem_nhds (by norm_num [unitHalf]) (by norm_num [unitHalf]))
    filter_upwards [hmem] with u hu
    have hloc : cdfSection (nelsen8 2 (by norm_num)) unitHalf=ᶠ[𝓝 (u:ℝ)] fun x => (5*x-1)/(7+x) := by
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
      exact nelsen8_two_section hx
    apply HasDerivAt.congr_of_eventuallyEq _ hloc
    have hn : (7+(u:ℝ))≠0 := by linarith [hu.1]
    have h := (((hasDerivAt_id (u:ℝ)).const_mul 5).sub_const 1).div
      ((hasDerivAt_id (u:ℝ)).const_add 7) hn
    convert h using 1
    simp only [g,id]
    field_simp
    ring
  have h0 : 0<g unitHalf := by simp only [g,unitHalf]; norm_num
  have h1 : g unitHalf<1 := by simp only [g,unitHalf]; norm_num
  exact conditional_energy_lt_of_local_deriv _ unitHalf unitHalf g hg hd h0 h1

theorem nelsen8_not_schur_monotone :
    ¬ (∀ (θ η : ℝ) (hθ : 1≤θ) (hθη : θ≤η),
      (nelsen8 θ hθ).SchurLE (nelsen8 η (hθ.trans hθη))) := by
  intro h
  have hh := h 1 2 le_rfl (by norm_num)
  rw [nelsen8_one] at hh
  exact not_countermonotonic_schurLE _ nelsen8_two_median_energy_lt hh

/-- The quarter point. -/
noncomputable def unitQuarter : I := ⟨1/4,by norm_num,by norm_num⟩

theorem nelsen8_five_section {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    cdfSection (nelsen8 5 (by norm_num)) unitQuarter u=max 0 ((7*u-3/4)/(13+12*u)) := by
  dsimp only [cdfSection]
  rw [projIcc_of_mem zero_le_one hu,nelsen8_cdf_full]
  simp only [unitQuarter]
  have hd : (0:ℝ)<13+12*u := by linarith [hu.1]
  congr 1
  field_simp
  ring

theorem nelsen8_five_deriv {u : ℝ} (hu : u∈Ioo (0:ℝ) 1) (hu3 : u≠3/28) :
    deriv (cdfSection (nelsen8 5 (by norm_num)) unitQuarter) u=
      if u<3/28 then 0 else 100/(13+12*u)^2 := by
  rcases lt_or_gt_of_ne hu3 with hl|hr
  · rw [if_pos hl]
    apply HasDerivAt.deriv
    apply (hasDerivAt_const u (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hu.1 hl] with x hx
    rw [nelsen8_five_section ⟨hx.1.le,by linarith [hx.2]⟩]
    apply max_eq_left
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hx.2]) (by linarith [hx.1])
  · rw [if_neg (not_lt.mpr hr.le)]
    apply HasDerivAt.deriv
    have hloc : cdfSection (nelsen8 5 (by norm_num)) unitQuarter=ᶠ[𝓝 u]
        fun x => (7*x-3/4)/(13+12*x) := by
      filter_upwards [Ioo_mem_nhds hr hu.2] with x hx
      rw [nelsen8_five_section ⟨by linarith [hx.1],hx.2.le⟩]
      exact max_eq_right (div_nonneg (by linarith [hx.1]) (by linarith [hx.1]))
    apply HasDerivAt.congr_of_eventuallyEq _ hloc
    have hn : (13+12*u)≠0 := by linarith [hu.1]
    have h := (((hasDerivAt_id u).const_mul 7).sub_const (3/4)).div
      (((hasDerivAt_id u).const_mul 12).const_add 13) hn
    convert h using 1
    simp only [id]
    field_simp
    ring

theorem nelsen8_five_quarter_energy :
    (∫ u : I, (nelsen8 5 (by norm_num)).conditionalCDF u unitQuarter ^ 2)=279/3600 := by
  set C := nelsen8 5 (by norm_num)
  let h : ℝ → ℝ := fun u => if u<3/28 then 0 else 10000/(13+12*u)^4
  have hae : (fun u : I => C.conditionalCDF u unitQuarter ^ 2)=ᵐ[volume]
      fun u : I => h (projIcc 0 1 zero_le_one (u:ℝ)) := by
    have h0 : ∀ᵐ u : I, u≠0 := by simp [ae_iff]
    have h1 : ∀ᵐ u : I, u≠1 := by simp [ae_iff]
    have hq : ∀ᵐ u : I, u≠⟨3/28,by norm_num,by norm_num⟩ := by simp [ae_iff]
    filter_upwards [conditionalCDF_eq_deriv C unitQuarter,h0,h1,hq] with u hu hu0 hu1 hq
    rw [hu,projIcc_val]
    have hu0' : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (fun e => hu0 (Subtype.ext e.symm))
    have hu1' : (u:ℝ)<1 := lt_of_le_of_ne u.property.2 (fun e => hu1 (Subtype.ext e))
    have hq' : (u:ℝ)≠3/28 := fun e => hq (Subtype.ext e)
    rw [nelsen8_five_deriv ⟨hu0',hu1'⟩ hq']
    simp only [h]
    split_ifs
    · norm_num
    · rw [div_pow]; norm_num
  rw [integral_congr_ae hae]
  have hI := integral_Iic_unit_eq_interval (fun u : I => h (projIcc 0 1 zero_le_one (u:ℝ))) 1
  simp only [Iic_top,Measure.restrict_univ,Set.Icc.coe_one,projIcc_val] at hI
  rw [show (Iic (1:I))=univ from Iic_top] at hI
  rw [Measure.restrict_univ] at hI
  rw [hI]
  have hproj : ∀ t ∈ uIcc (0:ℝ) 1, h (projIcc 0 1 zero_le_one t)=h t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    rw [projIcc_of_mem zero_le_one ht]
  rw [intervalIntegral.integral_congr hproj]
  -- split at the kink
  have hc : ContinuousOn (fun u : ℝ => 10000/(13+12*u)^4) (uIcc (3/28) 1) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    have : 0<13+12*x := by linarith [hx.1]
    positivity
  have hleft : IntervalIntegrable h volume 0 (3/28) := by
    apply (intervalIntegrable_const (c := (0:ℝ))).congr
    filter_upwards [Measure.ae_ne volume (3/28:ℝ)] with x hx
    intro hmem
    rw [uIoc_of_le (by norm_num)] at hmem
    simp only [h]
    rw [if_pos (lt_of_le_of_ne hmem.2 hx)]
  have hright : IntervalIntegrable h volume (3/28) 1 := by
    apply (hc.intervalIntegrable).congr
    filter_upwards [] with x
    intro hmem
    rw [uIoc_of_le (by norm_num)] at hmem
    simp only [h]
    rw [if_neg (not_lt.mpr hmem.1.le)]
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  have hz : (∫ x in (0:ℝ)..(3/28), h x)=0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0:ℝ)) (by
      filter_upwards [Measure.ae_ne volume (3/28:ℝ)] with x hx
      intro hmem
      rw [uIoc_of_le (by norm_num)] at hmem
      simp only [h]
      rw [if_pos (lt_of_le_of_ne hmem.2 hx)])]
    simp
  have hr : (∫ x in (3/28:ℝ)..1, h x)=∫ x in (3/28:ℝ)..1, 10000/(13+12*x)^4 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with x
    intro hmem
    rw [uIoc_of_le (by norm_num)] at hmem
    simp only [h]
    rw [if_neg (not_lt.mpr hmem.1.le)]
  rw [hz,hr,zero_add]
  have hF : ∀ x ∈ uIcc (3/28:ℝ) 1, HasDerivAt (fun x : ℝ => -(10000/36)/(13+12*x)^3)
      (10000/(13+12*x)^4) x := by
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    have hp : 0<13+12*x := by linarith [hx.1]
    have hd := (((hasDerivAt_id x).const_mul 12).const_add 13).pow 3
    have h2 := (hd.inv (by positivity)).const_mul (-(10000/36))
    convert h2 using 1
    · funext y; simp [div_eq_mul_inv]
    · simp only [id]
      field_simp
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hc.intervalIntegrable)]
  norm_num

theorem clayton_one_half_quarter :
    (clayton 2 1 (by norm_num)).cdf ![unitHalf,unitQuarter]=(1/5:ℝ) := by
  rw [cdf_clayton_one_two (by norm_num [unitHalf]) (by norm_num [unitQuarter])]
  norm_num [unitHalf,unitQuarter]

theorem nelsen8_not_schur_antitone :
    ¬ (∀ (θ η : ℝ) (hθ : 1≤θ) (hθη : θ≤η),
      (nelsen8 η (hθ.trans hθη)).SchurLE (nelsen8 θ hθ)) := by
  intro h
  let θ : ℝ → ℝ := fun x => max 5 x
  have hθ (x : ℝ) : 1≤θ x := (by norm_num : (1:ℝ)≤5).trans (le_max_left _ _)
  have ht : Tendsto θ atTop atTop := tendsto_atTop_mono (fun x => le_max_right 5 x) tendsto_id
  have hc := tendsto_nelsen8_atTop θ hθ ht ![unitHalf,unitQuarter]
  rw [clayton_one_half_quarter] at hc
  have hl : Tendsto (fun x => (2*(nelsen8 (θ x) (hθ x)).cdf ![unitHalf,unitQuarter]-(1/4:ℝ))^2)
      atTop (𝓝 ((3/20:ℝ)^2)) := by
    convert ((hc.const_mul 2).sub_const (1/4)).pow 2 using 2
    norm_num
  have hb (x : ℝ) :
      (2*(nelsen8 (θ x) (hθ x)).cdf ![unitHalf,unitQuarter]-(1/4:ℝ))^2 ≤ 279/3600-1/16 := by
    have hm := h 5 (θ x) (by norm_num) (le_max_left _ _)
    have hi := hm unitQuarter (fun z => z^2) (by fun_prop)
      ((convexOn_pow (𝕜 := ℝ) 2).subset (fun _ hz => hz.1) (convex_Icc 0 1))
    have hs := RankRegion.XiBeta.median_strip_energy (nelsen8 (θ x) (hθ x)) unitQuarter
    rw [nelsen8_five_quarter_energy] at hi
    norm_num [RankRegion.XiBeta.medianDisplacement,unitQuarter] at hs hi ⊢
    linarith
  have hb' := le_of_tendsto hl (Eventually.of_forall hb)
  norm_num at hb'

/-! ## Nelsen 18 -/

theorem nelsen18_two_section {u : ℝ} (hu : u∈Ioo (1/4:ℝ) (3/4)) :
    cdfSection (nelsen18 2 le_rfl) unitHalf u=
      1+2/Real.log (Real.exp (2/(u-1))+Real.exp (-4)) := by
  dsimp only [cdfSection]
  have hu1 : (⟨u,by linarith [hu.1],by linarith [hu.2]⟩ : I)<1 := by
    rw [← Subtype.coe_lt_coe]; simp only [Set.Icc.coe_one]; linarith [hu.2]
  rw [projIcc_of_mem zero_le_one ⟨by linarith [hu.1],by linarith [hu.2]⟩,
    nelsen18_cdf_of_lt_one 2 le_rfl _ _ hu1 (by
      rw [← Subtype.coe_lt_coe]; simp only [Set.Icc.coe_one,unitHalf]; norm_num)]
  simp only [unitHalf]
  rw [show (2:ℝ)/(1/2-1)=-4 by norm_num]
  apply max_eq_right
  -- `log s ≤ -2` since `s ≤ 2 e^{-4} ≤ e^{-2}`
  have hs0 : 0<Real.exp (2/(u-1))+Real.exp (-4) := by positivity
  have hs : Real.exp (2/(u-1))+Real.exp (-4)≤Real.exp (-2) := by
    have h1 : 2/(u-1)≤-4 := by
      rw [div_le_iff_of_neg (by linarith [hu.2])]
      linarith [hu.2]
    have h2 : Real.exp (2/(u-1))≤Real.exp (-4) := Real.exp_le_exp.mpr h1
    have h3 : 2*Real.exp (-4)≤Real.exp (-2) := by
      have : Real.exp (-2)=Real.exp (-4)*Real.exp 2 := by rw [← Real.exp_add]; norm_num
      rw [this]
      have : (2:ℝ)≤Real.exp 2 := by
        have := Real.add_one_le_exp (2:ℝ); linarith
      nlinarith [Real.exp_pos (-4)]
    linarith
  have hl : Real.log (Real.exp (2/(u-1))+Real.exp (-4))≤-2 := by
    rw [← Real.log_exp (-2)]
    exact Real.log_le_log hs0 hs
  have hneg : Real.log (Real.exp (2/(u-1))+Real.exp (-4))<0 := by linarith
  have : -1≤2/Real.log (Real.exp (2/(u-1))+Real.exp (-4)) := by
    rw [le_div_iff_of_neg hneg]
    linarith
  linarith

theorem nelsen18_two_median_energy_lt :
    (∫ u : I, (nelsen18 2 le_rfl).conditionalCDF u unitHalf ^ 2)<(1/2:ℝ) := by
  let s : ℝ → ℝ := fun x => Real.exp (2/(x-1))+Real.exp (-4)
  let g : I → ℝ := fun u => 4*Real.exp (2/((u:ℝ)-1))/(((u:ℝ)-1)^2*s u*Real.log (s u)^2)
  have hspos (x : ℝ) : 0<s x := by simp only [s]; positivity
  have hlogne (x : ℝ) (hx : x∈Ioo (1/4:ℝ) (3/4)) : Real.log (s x)≠0 := by
    apply (Real.log_neg (hspos x) _).ne
    have h1 : 2/(x-1)≤-4 := by
      rw [div_le_iff_of_neg (by linarith [hx.2])]
      linarith [hx.2]
    have h2 : Real.exp (2/(x-1))≤Real.exp (-4) := Real.exp_le_exp.mpr h1
    have h3 : Real.exp (-4)<1/2 := by
      have h4 : Real.exp (-4)*Real.exp 4=1 := by rw [← Real.exp_add]; norm_num
      have h5 : (2:ℝ)<Real.exp 4 := by have := Real.add_one_le_exp (4:ℝ); linarith
      nlinarith [Real.exp_pos (-4)]
    simp only [s]; linarith
  have hmid : ((unitHalf:I):ℝ)∈Ioo (1/4:ℝ) (3/4) := by norm_num [unitHalf]
  have hsc (x : ℝ) (hx : x≠1) : ContinuousAt s x := by
    simp only [s]
    apply ContinuousAt.add _ continuousAt_const
    apply Real.continuous_exp.continuousAt.comp
    exact continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hx)
  have hg : ContinuousAt g unitHalf := by
    have h1 : ((unitHalf:I):ℝ)≠1 := by norm_num [unitHalf]
    have hs' : ContinuousAt (fun u : I => s u) unitHalf :=
      (hsc _ h1).comp continuous_subtype_val.continuousAt
    have he : ContinuousAt (fun u : I => Real.exp (2/((u:ℝ)-1))) unitHalf :=
      Real.continuous_exp.continuousAt.comp (continuousAt_const.div
        (continuous_subtype_val.continuousAt.sub continuousAt_const) (sub_ne_zero.mpr h1))
    have hl : ContinuousAt (fun u : I => Real.log (s u)) unitHalf :=
      (Real.continuousAt_log (hspos _).ne').comp hs'
    apply ContinuousAt.div (continuousAt_const.mul he)
      (((continuous_subtype_val.continuousAt.sub continuousAt_const).pow 2).mul hs' |>.mul (hl.pow 2))
    have := hlogne _ hmid
    have := hspos ((unitHalf:I):ℝ)
    have : ((unitHalf:I):ℝ)-1≠0 := sub_ne_zero.mpr h1
    positivity
  have hd : ∀ᶠ u in 𝓝 unitHalf, HasDerivAt (cdfSection (nelsen18 2 le_rfl) unitHalf) (g u) (u:ℝ) := by
    have hmem : ∀ᶠ u : I in 𝓝 unitHalf, (u:ℝ)∈Ioo (1/4:ℝ) (3/4) :=
      continuous_subtype_val.continuousAt (Ioo_mem_nhds hmid.1 hmid.2)
    filter_upwards [hmem] with u hu
    have hloc : cdfSection (nelsen18 2 le_rfl) unitHalf=ᶠ[𝓝 (u:ℝ)] fun x => 1+2/Real.log (s x) := by
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
      exact nelsen18_two_section hx
    apply HasDerivAt.congr_of_eventuallyEq _ hloc
    have hx1 : (u:ℝ)-1≠0 := by linarith [hu.2]
    have hq : HasDerivAt (fun x : ℝ => 2/(x-1)) (-2/((u:ℝ)-1)^2) u := by
      have := ((hasDerivAt_id (u:ℝ)).sub_const 1).inv hx1
      convert this.const_mul 2 using 1
      · funext x; simp [div_eq_mul_inv]
      · simp only [id]; field_simp
    have hS : HasDerivAt s (Real.exp (2/((u:ℝ)-1))*(-2/((u:ℝ)-1)^2)) u := by
      simpa [s] using (hq.exp).add_const (Real.exp (-4))
    have hL := hS.log (hspos _).ne'
    have hD := (hL.inv (hlogne _ hu)).const_mul 2
    convert hD.const_add 1 using 1
    · funext x; simp [div_eq_mul_inv]
    · simp only [g]
      have := hspos (u:ℝ)
      have := hlogne _ hu
      field_simp
      ring
  have hval : g unitHalf=8/(Real.log 2-4)^2 := by
    simp only [g,s]
    norm_num [unitHalf]
    have hl : Real.log (Real.exp (-4)+Real.exp (-4))=Real.log 2-4 := by
      rw [← two_mul,Real.log_mul (by norm_num) (Real.exp_pos _).ne',Real.log_exp]; ring
    rw [hl]
    have hne : Real.log 2-4≠0 := by
      have := Real.log_two_lt_d9; linarith
    field_simp
    ring
  have hl2 : Real.log 2<1 := by have := Real.log_two_lt_d9; linarith
  have hl0 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h0 : 0<g unitHalf := by
    rw [hval]; have : (Real.log 2-4)^2>0 := by nlinarith
    positivity
  have h1 : g unitHalf<1 := by
    rw [hval,div_lt_one (by nlinarith)]
    nlinarith
  exact conditional_energy_lt_of_local_deriv _ unitHalf unitHalf g hg hd h0 h1

theorem nelsen18_not_schur_antitone :
    ¬ (∀ (θ η : ℝ) (hθ : 2≤θ) (hθη : θ≤η),
      (nelsen18 η (hθ.trans hθη)).SchurLE (nelsen18 θ hθ)) := by
  intro h
  let θ : ℝ → ℝ := fun x => max 2 x
  have hθ (x : ℝ) : 2≤θ x := le_max_left _ _
  have ht : Tendsto θ atTop atTop := tendsto_atTop_mono (fun x => le_max_right 2 x) tendsto_id
  have hc := nelsen18_tendsto_atTop θ hθ ht unitHalf unitHalf
  rw [comonotonic_median_cdf] at hc
  exact not_schurLE_of_tendsto_comonotonic (fun x => nelsen18 (θ x) (hθ x)) _ hc
    nelsen18_two_median_energy_lt (fun x => h 2 (θ x) le_rfl (le_max_left _ _))

end Verification
