import Verification.Plackett
import Copula.Countermonotonic
import Copula.Comonotonic
import Copula.Rank.Integration

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem plackett_den_pos {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    0 < plackettA θ u v+Real.sqrt (plackettD θ u v) := by
  have hs := Real.sq_sqrt (plackettD_pos hθ u.property v.property).le
  have hp := Real.sqrt_pos.mpr (plackettD_pos hθ u.property v.property)
  by_cases ht : 1 ≤ θ
  · have ha : 0 ≤ plackettA θ u v := by
      unfold plackettA
      have hh := mul_nonneg (sub_nonneg.mpr ht) (add_nonneg u.property.1 v.property.1)
      linarith
    linarith
  by_cases hu : (u:ℝ)=0
  · have ha : 0 < plackettA θ u v := by
      unfold plackettA; rw [hu,zero_add]
      nlinarith [mul_nonneg (show 0 ≤ 1-θ by linarith) (sub_nonneg.mpr v.property.2)]
    linarith
  by_cases hv : (v:ℝ)=0
  · have ha : 0 < plackettA θ u v := by
      unfold plackettA; rw [hv,add_zero]
      nlinarith [mul_nonneg (show 0 ≤ 1-θ by linarith) (sub_nonneg.mpr u.property.2)]
    linarith
  have hn : 0 < 4*θ*(1-θ)*(u:ℝ)*(v:ℝ) :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hθ) (by linarith))
      (lt_of_le_of_ne u.property.1 (Ne.symm hu))) (lt_of_le_of_ne v.property.1 (Ne.symm hv))
  change (Real.sqrt (plackettD θ u v))^2 = (plackettA θ u v)^2-4*θ*(θ-1)*(u:ℝ)*(v:ℝ) at hs
  nlinarith

theorem plackett_cdf_rationalized {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    (plackett θ hθ).cdf ![u,v] =
      2*θ*(u:ℝ)*(v:ℝ)/(plackettA θ u v+Real.sqrt (plackettD θ u v)) := by
  by_cases he : θ=1
  · subst θ; rw [plackett_one]
    simp [cdf_independence,Fin.prod_univ_two,plackettA,plackettD]
    ring
  rw [plackett_cdf hθ he]
  change plackettF θ u v = _
  unfold plackettF
  have hs := Real.sq_sqrt (plackettD_pos hθ u.property v.property).le
  field_simp [sub_ne_zero.mpr he,(plackett_den_pos hθ u v).ne']
  change (Real.sqrt (plackettD θ u v))^2 = (plackettA θ u v)^2-4*θ*(θ-1)*(u:ℝ)*(v:ℝ) at hs
  nlinarith [hs]

theorem plackett_tendsto_parameter {A : Type*} {l : Filter A} (θ : A → ℝ)
    (hθ : ∀ a, 0 < θ a) {η : ℝ} (hη : 0 < η) (ht : Tendsto θ l (𝓝 η)) (u v : I) :
    Tendsto (fun a => (plackett (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((plackett η hη).cdf ![u,v])) := by
  simp only [plackett_cdf_rationalized]
  apply Tendsto.div
  · exact (((tendsto_const_nhds.mul ht).mul_const (u:ℝ)).mul_const (v:ℝ))
  · have hc : Continuous (fun x : ℝ => plackettA x u v+Real.sqrt (plackettD x u v)) := by
      unfold plackettD plackettA; fun_prop
    exact hc.continuousAt.tendsto.comp ht
  · exact (plackett_den_pos hη u v).ne'

theorem plackettF_zero_parameter (u v : I) : plackettF 0 u v = countermonotonic.cdf ![u,v] := by
  rw [cdf_countermonotonic]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  have hd : plackettD 0 u v = (1-(u:ℝ)-(v:ℝ))^2 := by
    unfold plackettD plackettA; ring
  rw [plackettF,hd,Real.sqrt_sq_eq_abs]
  unfold plackettA
  by_cases hh : (u:ℝ)+(v:ℝ) ≤ 1
  · rw [abs_of_nonneg (by linarith),max_eq_left (by linarith)]
    ring
  · rw [abs_of_nonpos (by linarith),max_eq_right (by linarith)]
    ring

theorem plackett_tendsto_zero {A : Type*} {l : Filter A} (θ : A → ℝ)
    (hθ : ∀ a, 0 < θ a) (ht : Tendsto θ l (𝓝 0)) (u v : I) :
    Tendsto (fun a => (plackett (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 (countermonotonic.cdf ![u,v])) := by
  have hc : ContinuousAt (fun x : ℝ => plackettF x u v) 0 := by
    unfold plackettF
    apply ContinuousAt.div
    · unfold plackettD plackettA; fun_prop
    · fun_prop
    · norm_num
  have hh := hc.tendsto.comp ht
  rw [plackettF_zero_parameter] at hh
  apply hh.congr'
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with a ha
  exact (plackett_cdf (hθ a) (ne_of_lt ha) u v).symm

noncomputable def plackettNormalized (u v x : ℝ) : ℝ :=
  (x+u+v-Real.sqrt ((x+u+v)^2-4*(1+x)*u*v))/2

theorem plackett_cdf_normalized {θ : ℝ} (hθ : 1 < θ) (u v : I) :
    (plackett θ (by linarith)).cdf ![u,v] = plackettNormalized u v (θ-1)⁻¹ := by
  rw [plackett_cdf (by linarith) hθ.ne']
  change plackettF θ u v = _
  have hp : 0 < θ-1 := sub_pos.mpr hθ
  have hd : plackettD θ u v = (θ-1)^2 *
      (((θ-1)⁻¹+(u:ℝ)+(v:ℝ))^2-4*(1+(θ-1)⁻¹)*(u:ℝ)*(v:ℝ)) := by
    unfold plackettD plackettA
    field_simp
    ring
  unfold plackettF plackettNormalized
  rw [hd,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hp.le]
  unfold plackettA
  field_simp
  ring

theorem plackett_tendsto_atTop {A : Type*} {l : Filter A} (θ : A → ℝ)
    (hθ : ∀ a, 0 < θ a) (ht : Tendsto θ l atTop) (u v : I) :
    Tendsto (fun a => (plackett (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((comonotonic 2).cdf ![u,v])) := by
  have hp : Tendsto (fun a => θ a-1) l atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [ht.eventually (eventually_ge_atTop (b+1))] with a ha
    linarith
  have hi := tendsto_inv_atTop_zero.comp hp
  have hc : Continuous (plackettNormalized u v) := by unfold plackettNormalized; fun_prop
  have hh := hc.continuousAt.tendsto.comp hi
  have he : plackettNormalized u v 0 = (comonotonic 2).cdf ![u,v] := by
    rw [cdf_comonotonic_two]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    unfold plackettNormalized
    have hd : (0+(u:ℝ)+(v:ℝ))^2-4*(1+0)*(u:ℝ)*(v:ℝ) = ((u:ℝ)-(v:ℝ))^2 := by ring
    rw [hd,Real.sqrt_sq_eq_abs]
    by_cases huv : (u:ℝ) ≤ (v:ℝ)
    · rw [min_eq_left huv,abs_of_nonpos (sub_nonpos.mpr huv)]; ring
    · rw [min_eq_right (le_of_not_ge huv),abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge huv))]; ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [ht.eventually (eventually_gt_atTop 1)] with a ha
  exact (plackett_cdf_normalized ha u v).symm

end Verification
