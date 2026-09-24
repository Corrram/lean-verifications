import Copula.Families.GumbelLimits
import Copula.Families.MarshallOlkin
import Copula.Dependence.Gumbel
import Verification.GumbelDensity
import Copula.TailDependence.ExtremeValue
import Copula.TailDependence.Examples

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem tawn_tendsto_atTop {A : Type*} {l : Filter A} (θ : A → ℝ)
    (hθ : ∀ a, 1 ≤ θ a) (ht : Tendsto θ l atTop) (α β : I) (u : Fin 2 → I) :
    Tendsto (fun a => (tawn (θ a) (hθ a) α β).cdf u) l
      (𝓝 ((marshallOlkin α β).cdf u)) := by
  simp only [tawn,marshallOlkin,commonShock,cdf_maxProduct]
  exact (tendsto_gumbel_atTop θ hθ ht _).mul_const _

theorem tawn_lowerOrthant_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hθη : θ ≤ η) (α β : I) :
    (tawn θ hθ α β).LowerOrthantLE (tawn η (hθ.trans hθη) α β) := by
  intro u
  simp only [tawn,cdf_maxProduct]
  exact mul_le_mul_of_nonneg_right (lowerOrthantLE_gumbel hθ (hθ.trans hθη) hθη _)
    ((independence 2).cdf_nonneg _)

theorem tawn_tendsto_parameter {A : Type*} {l : Filter A} (θ : A → ℝ)
    (hθ : ∀ a, 1 ≤ θ a) {η : ℝ} (hη : 1 ≤ η) (ht : Tendsto θ l (𝓝 η)) (α β u v : I) :
    Tendsto (fun a => (tawn (θ a) (hθ a) α β).cdf ![u,v]) l
      (𝓝 ((tawn η hη α β).cdf ![u,v])) := by
  by_cases hu : u = 0
  · subst u; simp only [cdf_two_zero_left]; exact tendsto_const_nhds
  by_cases hv : v = 0
  · subst v
    have he (C : Copula 2) : C.cdf ![u,0] = 0 := C.cdf_eq_zero_of_coord_eq_zero _ 1 (by simp)
    simp only [he]; exact tendsto_const_nhds
  have hp : 0 < η := by linarith
  have hc : ContinuousAt (fun x : ℝ =>
      (u:ℝ)^(1-(α:ℝ))*(v:ℝ)^(1-(β:ℝ))*
        Real.exp (-(((α:ℝ)*(-Real.log u))^x+((β:ℝ)*(-Real.log v))^x)^x⁻¹)) η := by
    have hx : ContinuousAt (fun x : ℝ => ((α:ℝ)*(-Real.log u))^x+((β:ℝ)*(-Real.log v))^x) η :=
      (continuousAt_const.rpow continuousAt_id (Or.inr hp)).add
        (continuousAt_const.rpow continuousAt_id (Or.inr hp))
    exact continuousAt_const.mul (Real.continuous_exp.continuousAt.comp
      ((hx.rpow (continuousAt_id.inv₀ hp.ne') (Or.inr (inv_pos.mpr hp))).neg))
  simpa only [tawn_cdf_positive _ _ α β u v hu hv,Function.comp_def] using hc.tendsto.comp ht

theorem tawn_one_one_density_tp2 (θ : ℝ) (hθ : 1 ≤ θ) :
    (tawn θ hθ 1 1).HasMTP2Density := by
  rw [tawn_one_one]
  exact gumbel_hasMTP2Density hθ

theorem tawn_one_one_not_independence {θ : ℝ} (hθ : 1 < θ) :
    tawn θ hθ.le 1 1 ≠ independence 2 := by
  intro he
  rw [tawn_one_one] at he
  have hh := hasUpperTailDependence_gumbel θ hθ.le
  rw [he] at hh
  let : NeBot (𝓝[>] (0:I)) := tailFilter_neBot
  have hz := tendsto_nhds_unique hh hasUpperTailDependence_independence
  have hp : (2:ℝ)^θ⁻¹ < 2 := by
    have hi : θ⁻¹ < 1 := (inv_lt_one₀ (by linarith : 0 < θ)).mpr hθ
    have hpow := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) hi
    simpa only [Real.rpow_one] using hpow
  linarith

theorem tawn_printed_tp2_exclusion_false :
    ¬ (∀ (θ : ℝ) (hθ : 1 ≤ θ) (α β : I), tawn θ hθ α β ≠ independence 2 →
      ¬ (tawn θ hθ α β).HasMTP2Density) := by
  intro h
  exact h 2 (by norm_num) 1 1 (tawn_one_one_not_independence (by norm_num))
    (tawn_one_one_density_tp2 2 (by norm_num))

end Verification
