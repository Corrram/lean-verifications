import Verification.LaplaceRadialAnalysis

open ProbabilityTheory MeasureTheory Real Set Filter
open scoped ENNReal

namespace Verification

theorem laplaceRadialDensity_pos (q : ℝ) : 0<laplaceRadialDensity q := by
  rw [laplaceRadialDensity,setLIntegral_pos_iff (by fun_prop)]
  have he : Function.support (fun t : ℝ => ENNReal.ofReal
      (t⁻¹*Real.exp (-t-q/(2*t)))) ∩ Ioi 0=Ioi 0 := by
    ext t
    constructor
    · exact fun h => h.2
    · intro ht
      refine ⟨?_,ht⟩
      apply ne_of_gt
      apply ENNReal.ofReal_pos.mpr
      exact mul_pos (inv_pos.mpr ht) (Real.exp_pos _)
  rw [he]
  simp

theorem studentQuadratic_pos {r : ℝ} (hr : r∈Ioo (-1) 1)
    {p : ℝ×ℝ} (hp : p≠(0,0)) : 0<studentQuadratic r p := by
  have hd : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  unfold studentQuadratic
  by_cases hx : p.1=0
  · have hy : p.2≠0 := by intro h; apply hp; exact Prod.ext hx h
    simpa only [hx,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,sub_zero,zero_add] using
      div_pos (sq_pos_of_ne_zero hy) hd
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (div_nonneg (sq_nonneg _) hd.le)

/-- A strict TP2 violation with all four evaluation points away from the singular origin. -/
theorem laplace_radial_tp2_witness {r : ℝ} (hr : r∈Ioo (-1) 1) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧
      laplaceRadialDensity (studentQuadratic r (-1,0))*
        laplaceRadialDensity (studentQuadratic r (t,1)) <
      laplaceRadialDensity (studentQuadratic r (-1,1))*
        laplaceRadialDensity (studentQuadratic r (t,0)) := by
  have hp (y : ℝ) : 0<studentQuadratic r (-1,y) :=
    studentQuadratic_pos hr (by intro h; have := congrArg Prod.fst h; norm_num at this)
  have h01 : 0<studentQuadratic r (0,1) :=
    studentQuadratic_pos hr (by norm_num)
  have hc1 : Tendsto (fun t : ℝ => laplaceRadialDensity (studentQuadratic r (t,1)))
      (nhds 0) (nhds (laplaceRadialDensity (studentQuadratic r (0,1)))) :=
    (laplaceRadialDensity_continuousAt h01).tendsto.comp ((show Continuous (fun t : ℝ => studentQuadratic r (t,1)) by
      unfold studentQuadratic
      fun_prop).continuousAt.tendsto)
  have hc0 : Tendsto (fun t : ℝ => laplaceRadialDensity (studentQuadratic r (t,0)))
      (nhds 0) (nhds ∞) := by
    apply laplaceRadialDensity_tendsto_zero.comp
    convert (show Continuous (fun t : ℝ => studentQuadratic r (t,0)) by
      unfold studentQuadratic; fun_prop).continuousAt.tendsto using 1
    simp [studentQuadratic]
  have hleft := ENNReal.Tendsto.mul
    (tendsto_const_nhds (x := laplaceRadialDensity (studentQuadratic r (-1,0))))
    (Or.inl (laplaceRadialDensity_pos _).ne') hc1
    (Or.inl (laplaceRadialDensity_pos _).ne')
  have hright := ENNReal.Tendsto.mul
    (tendsto_const_nhds (x := laplaceRadialDensity (studentQuadratic r (-1,1))))
    (Or.inl (laplaceRadialDensity_pos _).ne') hc0 (Or.inl ENNReal.top_ne_zero)
  rw [ENNReal.mul_top (laplaceRadialDensity_pos _).ne'] at hright
  have hlt := hleft.eventually_lt hright (lt_top_iff_ne_top.mpr
    (ENNReal.mul_ne_top (laplaceRadialDensity_ne_top (hp 0)) (laplaceRadialDensity_ne_top h01)))
  have hwithin := hlt.filter_mono (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  obtain ⟨t,⟨ht,hpos⟩,hsmall⟩ := (hwithin.and
    (self_mem_nhdsWithin : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), t∈Ioi 0) |>.and
    ((eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨t,hpos,hsmall,ht⟩

theorem laplace_joint_density_tp2_witness {r : ℝ} (hr : r∈Ioo (-1) 1) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧
      gaussianScaleMixtureJointDensity r (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt (-1,0)*
        gaussianScaleMixtureJointDensity r (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt (t,1) <
      gaussianScaleMixtureJointDensity r (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt (-1,1)*
        gaussianScaleMixtureJointDensity r (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt (t,0) := by
  obtain ⟨t,ht,hsmall,h⟩ := laplace_radial_tp2_witness hr
  refine ⟨t,ht,hsmall,?_⟩
  simp only [laplace_joint_density_evaluation hr]
  let c := ENNReal.ofReal ((2*Real.pi*Real.sqrt (1-r^2))⁻¹)
  have hc : c≠0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    have : 0<1-r^2 := by nlinarith [hr.1,hr.2]
    positivity
  have hcfin : c≠∞ := ENNReal.ofReal_ne_top
  have hh := ENNReal.mul_lt_mul_left (mul_ne_zero hc hc)
    (ENNReal.mul_ne_top hcfin hcfin) h
  simpa only [c,mul_assoc,mul_left_comm,mul_comm] using hh

end Verification
