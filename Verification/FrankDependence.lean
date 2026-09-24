import Verification.FrankTails
import Copula.Dependence.ConditionalMonotonicity
import Mathlib.Analysis.Convex.Deriv
import Copula.Dependence.Singular
import Copula.Dependence.DensityTotalPositivity

open ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace Verification

noncomputable def frankSection (θ a b x : ℝ) : ℝ :=
  -Real.log (a+b*Real.exp (-θ*x))/θ

theorem frankSection_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a+b)
    (θ x : ℝ) : 0 < a+b*Real.exp (-θ*x) := by
  rcases eq_or_lt_of_le hb with h | h
  · have hz : b = 0 := h.symm
    simp only [hz, zero_mul, add_zero]
    linarith
  · positivity

theorem frankSection_deriv {θ a b : ℝ} (hθ : θ ≠ 0)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a+b) (x : ℝ) :
    HasDerivAt (frankSection θ a b)
      (b*Real.exp (-θ*x)/(a+b*Real.exp (-θ*x))) x := by
  have he := ((hasDerivAt_id x).const_mul (-θ)).exp
  have hh := ((he.const_mul b).const_add a).log (ne_of_gt (frankSection_pos ha hb hab θ x))
  convert hh.neg.div_const θ using 1
  · rfl
  · dsimp
    field_simp

theorem frankSection_concave {θ a b : ℝ} (hθ : 0 < θ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a+b) :
    ConcaveOn ℝ univ (frankSection θ a b) := by
  have hd := frankSection_deriv hθ.ne' ha hb hab
  have hf : Differentiable ℝ (frankSection θ a b) := fun x => (hd x).differentiableAt
  apply Antitone.concaveOn_univ_of_deriv hf
  intro x y hxy
  rw [(hd x).deriv, (hd y).deriv]
  apply (div_le_div_iff₀ (frankSection_pos ha hb hab θ y)
    (frankSection_pos ha hb hab θ x)).mpr
  have he : Real.exp (-θ*y) ≤ Real.exp (-θ*x) := Real.exp_le_exp.mpr (by nlinarith)
  have hm := mul_nonneg (mul_nonneg ha hb) (sub_nonneg.mpr he)
  nlinarith

noncomputable def frankA (θ : ℝ) (v : I) : ℝ :=
  (Real.exp (-θ*(v:ℝ))-Real.exp (-θ))/(1-Real.exp (-θ))

noncomputable def frankB (θ : ℝ) (v : I) : ℝ :=
  (1-Real.exp (-θ*(v:ℝ)))/(1-Real.exp (-θ))

theorem frankAB {θ : ℝ} (hθ : 0 < θ) (v : I) :
    0 ≤ frankA θ v ∧ 0 ≤ frankB θ v ∧ frankA θ v+frankB θ v = 1 := by
  have hd : 0 < 1-Real.exp (-θ) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hθ))
  have he : Real.exp (-θ) ≤ Real.exp (-θ*(v:ℝ)) := Real.exp_le_exp.mpr (by nlinarith [v.property.2])
  have he' : Real.exp (-θ*(v:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [v.property.1])
  refine ⟨div_nonneg (sub_nonneg.mpr he) hd.le, div_nonneg (sub_nonneg.mpr he') hd.le, ?_⟩
  dsimp [frankA, frankB]
  rw [← add_div]
  have hn : Real.exp (-θ*(v:ℝ))-Real.exp (-θ)+(1-Real.exp (-θ*(v:ℝ))) = 1-Real.exp (-θ) := by ring
  rw [hn, div_self hd.ne']

theorem frank_cdf_section (θ : ℝ) (hθ : 0 < θ) (u v : I) :
    (frank θ hθ).cdf ![u,v] = frankSection θ (frankA θ v) (frankB θ v) u := by
  rw [frank_cdf_full]
  have hab := frankAB hθ v
  by_cases hu : u = 0
  · subst u
    simp [frankSection, hab.2.2]
  by_cases hv : v = 0
  · subst v
    have hd : 1-Real.exp (-θ) ≠ 0 := ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hθ)))
    simp [frankSection, frankA, frankB, hd]
  simp only [hu, hv, or_self, ite_false]
  unfold frankSection
  congr 2
  congr 1
  dsimp [frankA, frankB]
  have hd : 1-Real.exp (-θ) ≠ 0 := ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hθ)))
  field_simp
  ring

theorem frank_positive_isSI (θ : ℝ) (hθ : 0 < θ) : (frank θ hθ).IsSI := by
  intro a b c v hab hbc
  rcases eq_or_lt_of_le hab with he | hab'
  · subst b; simp
  rcases eq_or_lt_of_le hbc with he | hbc'
  · subst c; simp
  have hp := frankAB hθ v
  have hc := (frankSection_concave hθ hp.1 hp.2.1 (by rw [hp.2.2]; norm_num)).neg
  have hs := hc.secant_mono_aux1 (mem_univ (a:ℝ)) (mem_univ (c:ℝ))
    (show (a:ℝ) < b from hab') (show (b:ℝ) < c from hbc')
  simp only [frank_cdf_section]
  dsimp at hs
  nlinarith [hs]

theorem frank_positive_isCI (θ : ℝ) (hθ : 0 < θ) : (frank θ hθ).IsCI :=
  (isArchimedean_frank θ hθ).isCI_iff.mpr (frank_positive_isSI θ hθ)

theorem frank_negative_transpose (θ : ℝ) (hθ : θ < 0) :
    (frankNegative θ hθ).transpose = frankNegative θ hθ := by
  apply Copula.cdf_injective
  funext x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx, cdf_transpose, frankNegative_cdf_source, frankNegative_cdf_source]
  rw [mul_comm (Real.exp (-θ*(x 1:ℝ))-1)]

theorem frank_negative_isCD (θ : ℝ) (hθ : θ < 0) : (frankNegative θ hθ).IsCD := by
  have hs : (frankNegative θ hθ).IsSD :=
    (isSD_reflect_second_iff _).mpr (frank_positive_isSI (-θ) (neg_pos.mpr hθ))
  exact ⟨hs, by rw [frank_negative_transpose]; exact hs⟩

theorem frank_positive_ne_independence (θ : ℝ) (hθ : 0 < θ) :
    frank θ hθ ≠ independence 2 := by
  intro heq
  let v : I := ⟨1/2, by norm_num, by norm_num⟩
  have hp := frankAB hθ v
  have hd := (frankSection_deriv hθ.ne' hp.1 hp.2.1
    (by rw [hp.2.2]; norm_num) 0).hasDerivWithinAt (s := Icc (0:ℝ) 1)
  have he (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      frankSection θ (frankA θ v) (frankB θ v) x = x*(1/2) := by
    have hh := frank_cdf_section θ hθ (⟨x,hx⟩:I) v
    rw [heq] at hh
    simpa [cdf_independence, v, Fin.prod_univ_two] using hh.symm
  have hl := ((hasDerivAt_id (0:ℝ)).mul_const (1/2:ℝ)).hasDerivWithinAt
    (s := Icc (0:ℝ) 1)
  have hd' := hl.congr_of_mem he (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1)
  have hu := uniqueDiffOn_Icc_zero_one 0 (by norm_num)
  have hv := (hd.derivWithin hu).symm.trans (hd'.derivWithin hu)
  have hb : frankB θ v = 1/2 := by simpa [hp.2.2] using hv
  have hq0 : 0 < Real.exp (-θ/2) := Real.exp_pos _
  have hq1 : Real.exp (-θ/2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he2 : Real.exp (-θ) = Real.exp (-θ/2)^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hden : 0 < 1-Real.exp (-θ) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  change (1-Real.exp (-θ*(1/2)))/(1-Real.exp (-θ)) = 1/2 at hb
  have hm := (div_eq_iff hden.ne').mp hb
  rw [he2] at hm
  have hh : -θ*(1/2) = -θ/2 := by ring
  rw [hh] at hm
  nlinarith [sq_pos_of_pos (sub_pos.mpr hq1)]

theorem frank_positive_not_cd (θ : ℝ) (hθ : 0 < θ) : ¬(frank θ hθ).IsCD := by
  intro hc
  exact frank_positive_ne_independence θ hθ ((isPQD_and_isNQD_iff _).mp
    ⟨(frank_positive_isCI θ hθ).isPQD, hc.isNQD⟩)

theorem frank_negative_not_ci (θ : ℝ) (hθ : θ < 0) : ¬(frankNegative θ hθ).IsCI := by
  intro hc
  have hn : (frank (-θ) (neg_pos.mpr hθ)).IsSD :=
    (isSI_reflect_second_iff _).mp hc.isSI
  exact frank_positive_ne_independence (-θ) (neg_pos.mpr hθ)
    ((isPQD_and_isNQD_iff _).mp
      ⟨(frank_positive_isCI (-θ) (neg_pos.mpr hθ)).isPQD, hn.isNQD⟩)

theorem frank_positive_not_nqd (θ : ℝ) (hθ : 0 < θ) : ¬(frank θ hθ).IsNQD := by
  intro hn
  exact frank_positive_ne_independence θ hθ
    ((isPQD_and_isNQD_iff _).mp ⟨(frank_positive_isCI θ hθ).isPQD, hn⟩)

theorem frank_negative_not_pqd (θ : ℝ) (hθ : θ < 0) : ¬(frankNegative θ hθ).IsPQD := by
  intro hp
  apply frank_positive_not_nqd (-θ) (neg_pos.mpr hθ)
  intro u v
  have hh := hp u (unitInterval.symm v)
  simp only [frankNegative, cdf_reflect_second, unitInterval.symm_symm,
    unitInterval.coe_symm_eq] at hh
  nlinarith

theorem frank_negative_not_density_tp2 (θ : ℝ) (hθ : θ < 0) :
    ¬(frankNegative θ hθ).HasMTP2Density := by
  intro hm
  exact frank_negative_not_pqd θ hθ (hasMTP2Density_isPQD _ hm)

end Verification
