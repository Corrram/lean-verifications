import Verification.PlackettAnalytic
import Copula.Independence
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

theorem plackettF_symm (θ u v : ℝ) : plackettF θ u v = plackettF θ v u := by
  have hA : plackettA θ u v = plackettA θ v u := by unfold plackettA; ring
  have hD : plackettD θ u v = plackettD θ v u := by unfold plackettD; rw [hA]; ring
  unfold plackettF
  rw [hA,hD]

theorem plackettF_zero {θ v : ℝ} (hθ : 0 < θ) (hv : v ∈ Icc 0 1) :
    plackettF θ 0 v = 0 := by
  have hA : 0 ≤ 1+(θ-1)*v := by
    have hh := mul_nonneg hθ.le hv.1
    nlinarith [hv.2]
  simp only [plackettF,plackettD,plackettA,zero_add,mul_zero,zero_mul,sub_zero]
  rw [Real.sqrt_sq hA,sub_self,zero_div]

theorem plackettF_one {θ v : ℝ} (hθ : 0 < θ) (hne : θ ≠ 1) (hv : v ∈ Icc 0 1) :
    plackettF θ 1 v = v := by
  have hn : 0 ≤ θ-(θ-1)*v := by
    nlinarith [mul_nonneg hθ.le (sub_nonneg.mpr hv.2),hv.1]
  have he : plackettD θ 1 v = (θ-(θ-1)*v)^2 := by unfold plackettD plackettA; ring
  rw [plackettF,he,Real.sqrt_sq hn]
  unfold plackettA
  field_simp [sub_ne_zero.mpr hne]
  ring

theorem plackettP_monotone {θ u : ℝ} (hθ : 0 < θ) (hu : u ∈ Icc 0 1) :
    MonotoneOn (plackettP θ u) (Icc 0 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
  · intro v hv
    exact (plackettP_deriv (plackettD_pos hθ hu hv)).continuousAt.continuousWithinAt
  · intro v hv
    exact (plackettP_deriv (plackettD_pos hθ hu (interior_subset hv))).hasDerivWithinAt
  · intro v hv
    exact plackettDensity_nonneg hθ hu (interior_subset hv)

theorem plackettF_rectangle {θ : ℝ} (hθ : 0 < θ) (hne : θ ≠ 1)
    (a b c d : I) (hab : a ≤ b) (hcd : c ≤ d) :
    0 ≤ plackettF θ b d-plackettF θ a d-plackettF θ b c+plackettF θ a c := by
  have hd (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun x => plackettF θ x d-plackettF θ x c)
        (plackettP θ u d-plackettP θ u c) u :=
    (plackettF_deriv hne (plackettD_pos hθ hu d.property)).sub
      (plackettF_deriv hne (plackettD_pos hθ hu c.property))
  have hm : MonotoneOn (fun u => plackettF θ u d-plackettF θ u c) (Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    · intro u hu; exact (hd u hu).continuousAt.continuousWithinAt
    · intro u hu; exact (hd u (interior_subset hu)).hasDerivWithinAt
    · intro u hu
      exact sub_nonneg.mpr (plackettP_monotone hθ (interior_subset hu) c.property d.property hcd)
  have hh := hm a.property b.property hab
  linarith

theorem plackett_isClassical {θ : ℝ} (hθ : 0 < θ) (hne : θ ≠ 1) :
    IsClassical (fun u : Fin 2 → I => plackettF θ (u 0) (u 1)) := by
  apply IsClassical.ofBivariate (fun u v : I => plackettF θ u v)
  · intro v; exact plackettF_zero hθ v.property
  · intro u; rw [plackettF_symm]; exact plackettF_zero hθ u.property
  · intro v; exact plackettF_one hθ hne v.property
  · intro u; rw [plackettF_symm]; exact plackettF_one hθ hne u.property
  · exact plackettF_rectangle hθ hne

noncomputable def plackett (θ : ℝ) (hθ : 0 < θ) : Copula 2 :=
  if h : θ = 1 then independence 2 else ofClassical _ (plackett_isClassical hθ h)

theorem plackett_one : plackett 1 (by norm_num) = independence 2 := by simp [plackett]

theorem plackett_cdf {θ : ℝ} (hθ : 0 < θ) (hne : θ ≠ 1) (u v : I) :
    (plackett θ hθ).cdf ![u,v] =
      (1+(θ-1)*((u:ℝ)+(v:ℝ))-Real.sqrt ((1+(θ-1)*((u:ℝ)+(v:ℝ)))^2-
        4*θ*(θ-1)*(u:ℝ)*(v:ℝ)))/(2*(θ-1)) := by
  simp only [plackett,hne,dite_false,cdf_ofClassical]
  rfl

end Verification
