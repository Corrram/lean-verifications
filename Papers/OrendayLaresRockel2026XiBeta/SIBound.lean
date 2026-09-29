import Papers.OrendayLaresRockel2026XiBeta.SIBoundAux
import Papers.OrendayLaresRockel2026XiBeta.RightSection
import Copula.UnitInterval

/-! # Lemma 5.1 (iii): the maximal completion maximizes `ξ` among SI copulas with the same
median section

For a stochastically increasing copula `C` with median section `A`, `ξ(C) ≤ ξ(Q_A)`, with
equality iff `C = Q_A`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

theorem integrable_of_abs_le_one {f : I → ℝ} (hf : Measurable f) (hb : ∀ u, |f u| ≤ 1) :
    Integrable f := by
  refine (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun u => by simpa [Real.norm_eq_abs] using hb u)

section lemma51

variable (C : Copula 2) (hC : C.IsSI) (s : MedianSection)
  (hs : ∀ u : I, s.A u = C.cdf ![u, Copula.unitHalf])

include hC hs

/-- For each threshold `v`: the conditional CDF of `C` has an antitone version `g` and
`∫ (k - g)² ≤ ∫ k² - ∫ h²`. -/
theorem kernel_sq_gap (v : I) :
    ∃ g : I → ℝ, Antitone g ∧ (∀ u, g u ∈ Icc (0 : ℝ) 1) ∧
      (fun u => C.conditionalCDF u v) =ᵐ[volume] g ∧
      (∫ u : I, (s.kernelCDF v u - g u) ^ 2) ≤
        (∫ u : I, s.kernelCDF v u ^ 2) - ∫ u : I, C.conditionalCDF u v ^ 2 := by
  obtain ⟨g, hg, hb, he⟩ := Verification.conditionalCDF_antitone_version C hC v
  refine ⟨g, hg, hb, he, ?_⟩
  set k := s.kernelCDF v with hk
  have hkm : Measurable k := s.measurable_kernelCDF v
  have hkb : ∀ u, k u ∈ Icc (0 : ℝ) 1 := s.kernelCDF_mem v
  have hgm : Measurable g := hg.measurable
  have hki : Integrable k := s.integrable_kernelCDF v
  have hgi : Integrable g := Verification.integrable_unit_bounded hgm hb
  have hfm : Measurable (fun u => k u - g u) := hkm.sub hgm
  have hfb : ∀ u, |k u - g u| ≤ 1 := fun u => by
    rw [abs_le]; constructor <;> linarith [(hkb u).1, (hkb u).2, (hb u).1, (hb u).2]
  have hpart : ∀ u : I, 0 ≤ ∫ t in Iic u, (k t - g t) := by
    intro u
    rw [integral_sub hki.integrableOn hgi.integrableOn]
    have h1 : ∫ t in Iic u, k t = s.completion.cdf ![u, v] := by
      rw [hk, s.integral_kernelCDF_Iic, s.cdf_completion]
    have h2 : ∫ t in Iic u, g t = C.cdf ![u, v] := by
      rw [C.cdf_eq_integral_conditionalCDF]
      exact (integral_congr_ae (ae_restrict_of_ae he)).symm
    rw [h1, h2]
    linarith [s.cdf_le_completion C (fun u => (hs u).symm) u v]
  have hA := integral_antitone_mul_nonneg hg hb hfm hfb hpart
  have hsq : ∀ u, k u ^ 2 - g u ^ 2 = (k u - g u) ^ 2 + 2 * (g u * (k u - g u)) := fun u => by ring
  have hk2 : Integrable (fun u => k u ^ 2) :=
    integrable_of_abs_le_one (hkm.pow_const 2) (fun u => by
      rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [(hkb u).1, (hkb u).2])
  have hg2 : Integrable (fun u => g u ^ 2) :=
    integrable_of_abs_le_one (hgm.pow_const 2) (fun u => by
      rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [(hb u).1, (hb u).2])
  have hf2 : Integrable (fun u => (k u - g u) ^ 2) :=
    integrable_of_abs_le_one (hfm.pow_const 2) (fun u => by
      rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [hfb u, abs_nonneg (k u - g u), sq_abs (k u - g u)])
  have hgf : Integrable (fun u => g u * (k u - g u)) :=
    integrable_of_abs_le_one (hgm.mul hfm) (fun u => by
      rw [abs_mul]
      nlinarith [hfb u, abs_nonneg (k u - g u), abs_nonneg (g u), abs_of_nonneg (hb u).1,
        (hb u).2])
  have hint : (∫ u, k u ^ 2) - ∫ u, g u ^ 2 =
      (∫ u, (k u - g u) ^ 2) + 2 * ∫ u, g u * (k u - g u) := by
    rw [← integral_sub hk2 hg2, ← integral_const_mul, ← integral_add hf2 (hgf.const_mul 2)]
    exact integral_congr_ae (Filter.Eventually.of_forall hsq)
  have hcond : (∫ u : I, C.conditionalCDF u v ^ 2) = ∫ u, g u ^ 2 :=
    integral_congr_ae (he.fun_comp (fun x : ℝ => x ^ 2))
  rw [hcond]
  linarith

/-- **Lemma 5.1 (iii)**: `ξ(C) ≤ ξ(Q_A)`, with equality iff `C = Q_A`. -/
theorem xi_le_completion : C.chatterjeeXi ≤ s.completion.chatterjeeXi := by
  choose g hgA hgb hge hgle using kernel_sq_gap C hC s hs
  have hnon : ∀ v : I, 0 ≤ ∫ u : I, (s.kernelCDF v u - g v u) ^ 2 :=
    fun v => integral_nonneg (fun u => sq_nonneg _)
  have hdiff : ∀ v : I, (∫ u : I, C.conditionalCDF u v ^ 2) ≤ ∫ u : I, s.kernelCDF v u ^ 2 :=
    fun v => by linarith [hgle v, hnon v]
  have := integral_mono C.integrable_integral_conditionalCDF_sq
    s.integrable_integral_kernelCDF_sq hdiff
  rw [s.xi_completion_eq]
  unfold Copula.chatterjeeXi
  linarith

theorem eq_completion_of_xi_eq (hxi : C.chatterjeeXi = s.completion.chatterjeeXi) :
    C = s.completion := by
  choose g hgA hgb hge hgle using kernel_sq_gap C hC s hs
  have hnon : ∀ v : I, 0 ≤ ∫ u : I, (s.kernelCDF v u - g v u) ^ 2 :=
    fun v => integral_nonneg (fun u => sq_nonneg _)
  have hdiff : ∀ v : I, 0 ≤ (∫ u : I, s.kernelCDF v u ^ 2) -
      ∫ u : I, C.conditionalCDF u v ^ 2 := fun v => by linarith [hgle v, hnon v]
  have hFi := s.integrable_integral_kernelCDF_sq.sub C.integrable_integral_conditionalCDF_sq
  have hint : ∫ v : I, ((∫ u : I, s.kernelCDF v u ^ 2) - ∫ u : I, C.conditionalCDF u v ^ 2) = 0 := by
    rw [integral_sub s.integrable_integral_kernelCDF_sq C.integrable_integral_conditionalCDF_sq]
    rw [s.xi_completion_eq] at hxi
    unfold Copula.chatterjeeXi at hxi
    linarith
  have hz := (integral_eq_zero_iff_of_nonneg hdiff hFi).1 hint
  have hgood : ∀ᵐ v : I, ∀ u : I, C.cdf ![u, v] = s.completion.cdf ![u, v] := by
    filter_upwards [hz] with v hv u
    have hD : ∫ w : I, (s.kernelCDF v w - g v w) ^ 2 = 0 :=
      le_antisymm (by have := hgle v; simp only [Pi.zero_apply] at hv; linarith) (hnon v)
    have hkm : Measurable (s.kernelCDF v) := s.measurable_kernelCDF v
    have hfi : Integrable (fun w => (s.kernelCDF v w - g v w) ^ 2) :=
      integrable_of_abs_le_one (((hkm.sub (hgA v).measurable)).pow_const 2) (fun w => by
        have h1 := s.kernelCDF_mem v w
        have h2 := hgb v w
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith [h1.1, h1.2, h2.1, h2.2])
    have hae := (integral_eq_zero_iff_of_nonneg (fun w => sq_nonneg _) hfi).1 hD
    have hae' : s.kernelCDF v =ᵐ[volume] g v := by
      filter_upwards [hae] with w hw
      have : (s.kernelCDF v w - g v w) ^ 2 = 0 := hw
      have := pow_eq_zero_iff (two_ne_zero) |>.1 this
      linarith
    rw [C.cdf_eq_integral_conditionalCDF, s.cdf_completion_eq_integral]
    exact (integral_congr_ae (ae_restrict_of_ae (hge v))).trans
      (integral_congr_ae (ae_restrict_of_ae hae'.symm))
  apply Copula.ext_cdf_two
  intro u v
  have hcC : Continuous fun v : I => C.cdf ![u, v] :=
    C.continuous_cdf.comp (by fun_prop)
  have hcQ : Continuous fun v : I => s.completion.cdf ![u, v] :=
    s.completion.continuous_cdf.comp (by fun_prop)
  have := (Continuous.ae_eq_iff_eq (volume : Measure I) hcC hcQ).1
    (by filter_upwards [hgood] with v hv using hv u)
  exact congrFun this v

end lemma51

end Papers.OrendayLaresRockel2026XiBeta
