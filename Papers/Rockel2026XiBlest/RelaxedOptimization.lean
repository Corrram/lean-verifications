import Papers.Rockel2026XiBlest.Derivatives
import Mathlib.MeasureTheory.Function.L2Space

/-! # Optimization over the full relaxed class of measurable kernels -/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.Rockel2026XiBlest

/-- Coordinates are (response threshold, conditioning rank); no monotonicity is assumed. -/
structure AdmissibleKernel (h : I × I → ℝ) : Prop where
  measurable : AEStronglyMeasurable h volume
  box : ∀ᵐ p, h p ∈ Icc (0 : ℝ) 1
  marginal : ∀ᵐ v : I, (∫ u : I,h (v,u))=(v : ℝ)

noncomputable def kernelXi (h : I × I → ℝ) : ℝ := 6*(∫ p,h p^2)-2
noncomputable def kernelNu (h : I × I → ℝ) : ℝ := 12*(∫ p,(1-(p.2 : ℝ))^2*h p)-2
noncomputable def extremalKernel (b : ℝ) (hb : 0 ≤ b) (p : I × I) : ℝ :=
  quadraticKernel b hb p.1 p.2

theorem AdmissibleKernel.memLp {h : I × I → ℝ} (hh : AdmissibleKernel h) : MemLp h 2 volume := by
  apply MemLp.of_bound hh.measurable 1
  filter_upwards [hh.box] with p hp
  simpa only [Real.norm_eq_abs,abs_of_nonneg hp.1] using hp.2

theorem extremalKernel_admissible (b : ℝ) (hb : 0 ≤ b) :
    AdmissibleKernel (extremalKernel b hb) := by
  constructor
  · exact ((extremal_kernel_measurable b hb).comp (measurable_snd.prodMk measurable_fst)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p => unitClamp_mem _
  · exact Filter.Eventually.of_forall fun v => quadraticIntercept_mean b hb v

private theorem weight_top : MemLp (fun p : I × I => (1-(p.2 : ℝ))^2) ⊤ volume := by
  apply MemLp.of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    nlinarith [p.2.property.1,p.2.property.2]

private theorem intercept_top (b : ℝ) (hb : 0 ≤ b) :
    MemLp (fun p : I × I => quadraticIntercept b hb p.1) ⊤ volume := by
  apply MemLp.of_bound ((quadraticIntercept_monotone b hb).measurable.comp measurable_fst).aestronglyMeasurable (b+1)
  exact Filter.Eventually.of_forall fun p => by
    change |quadraticIntercept b hb p.1| ≤ b+1
    exact abs_le.mpr ⟨by linarith [(quadraticIntercept_mem b hb p.1).1],by linarith [(quadraticIntercept_mem b hb p.1).2]⟩

theorem relaxed_distance_bound (h : I × I → ℝ) (hh : AdmissibleKernel h)
    (b : ℝ) (hb : 0 ≤ b) :
    6*(∫ p,(h p-extremalKernel b hb p)^2) ≤
      kernelXi h-kernelXi (extremalKernel b hb)-b*(kernelNu h-kernelNu (extremalKernel b hb)) := by
  let g := extremalKernel b hb
  have hg := extremalKernel_admissible b hb
  have hhi := hh.memLp.integrable (by norm_num)
  have hgi := hg.memLp.integrable (by norm_num)
  have hhw : Integrable (fun p : I × I => (1-(p.2 : ℝ))^2*h p) := hhi.mul_of_top_right weight_top
  have hgw : Integrable (fun p : I × I => (1-(p.2 : ℝ))^2*g p) := hgi.mul_of_top_right weight_top
  have hn : Integrable (fun p : I × I => quadraticIntercept b hb p.1*(h p-g p)) :=
    (hhi.sub hgi).mul_of_top_right (intercept_top b hb)
  have hnzero : (∫ p : I × I,quadraticIntercept b hb p.1*(h p-g p))=0 := by
    change (∫ p : I × I,quadraticIntercept b hb p.1*(h p-g p) ∂(volume : Measure I).prod volume)=0
    rw [integral_prod _ hn]
    apply integral_eq_zero_of_ae
    filter_upwards [hh.marginal,hg.marginal,hhi.prod_right_ae,hgi.prod_right_ae] with v hv hgv hiv higv
    rw [integral_const_mul,integral_sub hiv higv,hv,hgv,sub_self,mul_zero]
    rfl
  have hleft := (hh.memLp.sub hg.memLp).integrable_sq
  have hA : Integrable (fun p : I × I => h p^2-2*b*((1-(p.2 : ℝ))^2*h p)) :=
    hh.memLp.integrable_sq.sub (hhw.const_mul (2*b))
  have hB : Integrable (fun p : I × I => g p^2-2*b*((1-(p.2 : ℝ))^2*g p)) :=
    hg.memLp.integrable_sq.sub (hgw.const_mul (2*b))
  have hAB : Integrable (fun p : I × I => (h p^2-2*b*((1-(p.2 : ℝ))^2*h p))-
      (g p^2-2*b*((1-(p.2 : ℝ))^2*g p))) := hA.sub hB
  have hright := hAB.add (hn.const_mul (-2))
  have hineq := integral_mono_ae hleft hright (by
    filter_upwards [hh.box] with p hp
    simpa only [g,extremalKernel,quadraticKernel,Pi.add_apply,Pi.sub_apply,mul_assoc] using
      blest_quadratic_certificate (quadraticIntercept b hb p.1) b (p.2 : ℝ) (h p) hp)
  simp only [Pi.add_apply,Pi.sub_apply] at hineq
  rw [integral_add hAB (hn.const_mul (-2)),integral_sub hA hB,
    integral_sub hh.memLp.integrable_sq (hhw.const_mul (2*b)),
    integral_sub hg.memLp.integrable_sq (hgw.const_mul (2*b)),
    integral_const_mul,integral_const_mul,integral_const_mul,hnzero] at hineq
  unfold kernelXi kernelNu
  dsimp only [g] at hineq ⊢
  linarith

theorem relaxed_maximal (h : I × I → ℝ) (hh : AdmissibleKernel h)
    (b : ℝ) (hb : 0 < b) (hx : kernelXi h ≤ kernelXi (extremalKernel b hb.le)) :
    kernelNu h ≤ kernelNu (extremalKernel b hb.le) := by
  have hi := relaxed_distance_bound h hh b hb.le
  have hn : 0 ≤ ∫ p,(h p-extremalKernel b hb.le p)^2 := integral_nonneg fun p => sq_nonneg _
  nlinarith

theorem relaxed_maximal_eq_iff (h : I × I → ℝ) (hh : AdmissibleKernel h)
    (b : ℝ) (hb : 0 < b) (hx : kernelXi h ≤ kernelXi (extremalKernel b hb.le)) :
    kernelNu h=kernelNu (extremalKernel b hb.le) ↔ h=ᵐ[volume] extremalKernel b hb.le := by
  constructor
  · intro he
    have hi := relaxed_distance_bound h hh b hb.le
    have hz : (∫ p,(h p-extremalKernel b hb.le p)^2)=0 := by
      have hn : 0 ≤ ∫ p,(h p-extremalKernel b hb.le p)^2 := integral_nonneg fun p => sq_nonneg _
      rw [he,sub_self,mul_zero,sub_zero] at hi
      linarith
    have hae := (integral_eq_zero_iff_of_nonneg (fun p => sq_nonneg _)
      (hh.memLp.sub (extremalKernel_admissible b hb.le).memLp).integrable_sq).mp hz
    filter_upwards [hae] with p hp
    simpa only [Pi.zero_apply,Pi.sub_apply,sq_eq_zero_iff,sub_eq_zero] using hp
  · intro he
    unfold kernelNu
    congr 2
    exact integral_congr_ae (he.mono fun p hp => by dsimp only; rw [hp])

theorem extremalKernel_coefficients (b : ℝ) (hb : 0 ≤ b) :
    kernelXi (extremalKernel b hb)=(extremalCopula b hb).chatterjeeXi ∧
    kernelNu (extremalKernel b hb)=blestNu (extremalCopula b hb) := by
  have hg := extremalKernel_admissible b hb
  constructor
  · unfold kernelXi Copula.chatterjeeXi
    congr 2
    change (∫ p : I × I,extremalKernel b hb p^2 ∂(volume : Measure I).prod volume)=_
    rw [integral_prod _ hg.memLp.integrable_sq]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v => integral_congr_ae
      ((quadraticBand_conditionalCDF b hb v).mono fun u hu => by
        change quadraticKernel b hb v u^2=(quadraticBand b hb).conditionalCDF u v^2
        dsimp only at hu
        rw [hu]; rfl)
  · rw [blest_conditional_formula]
    unfold kernelNu
    congr 2
    change (∫ p : I × I,(1-(p.2 : ℝ))^2*extremalKernel b hb p ∂(volume : Measure I).prod volume)=_
    have hi : Integrable (fun p : I × I => (1-(p.2 : ℝ))^2*extremalKernel b hb p) :=
      (hg.memLp.integrable (by norm_num)).mul_of_top_right weight_top
    rw [integral_prod _ hi]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v => integral_congr_ae
      ((quadraticBand_conditionalCDF b hb v).mono fun u hu => by
        change (1-(u : ℝ))^2*quadraticKernel b hb v u=
          (1-(u : ℝ))^2*(quadraticBand b hb).conditionalCDF u v
        dsimp only at hu
        rw [hu]; rfl)

/-- Theorem 3.4 for arbitrary admissible L2 representatives, with uniqueness almost everywhere. -/
theorem relaxed_solution (c : ℝ) (hc : c ∈ Ioo 0 1) :
    ∃! b : Ioi (0 : ℝ), kernelXi (extremalKernel b b.property.le)=c ∧
      ∀ h : I × I → ℝ, AdmissibleKernel h → kernelXi h ≤ c →
        kernelNu h ≤ kernelNu (extremalKernel b b.property.le) ∧
        (kernelNu h=kernelNu (extremalKernel b b.property.le) ↔
          h=ᵐ[volume] extremalKernel b b.property.le) := by
  obtain ⟨b,hb,hunique⟩ := extremal_parameter_unique c hc
  have he : kernelXi (extremalKernel b b.property.le)=c :=
    (extremalKernel_coefficients b b.property.le).1.trans hb
  refine ⟨b,⟨he,?_⟩,?_⟩
  · intro h hh hx
    have hx' := hx.trans_eq he.symm
    exact ⟨relaxed_maximal h hh b b.property hx',relaxed_maximal_eq_iff h hh b b.property hx'⟩
  · intro d hd
    exact hunique d ((extremalKernel_coefficients d d.property.le).1.symm.trans hd.1)

end Papers.Rockel2026XiBlest
