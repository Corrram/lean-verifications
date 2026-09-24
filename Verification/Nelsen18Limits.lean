import Verification.Nelsen18
import Copula.Diagonal

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem nelsen18_tendsto_parameter {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 2 ≤ θ a) {η : ℝ} (hη : 2 ≤ η) (ht : Tendsto θ l (𝓝 η)) (u v : I) :
    Tendsto (fun a => (nelsen18 (θ a) (hθ a)).cdf ![u,v]) l (𝓝 ((nelsen18 η hη).cdf ![u,v])) := by
  by_cases hu : u = 1
  · subst u; simp only [cdf_two_one_left]; exact tendsto_const_nhds
  by_cases hv : v = 1
  · subst v; simp only [cdf_two_one_right]; exact tendsto_const_nhds
  have hu' : u < 1 := lt_of_le_of_ne u.property.2 hu
  have hv' : v < 1 := lt_of_le_of_ne v.property.2 hv
  have hs : ContinuousAt (fun x : ℝ => Real.exp (x/((u:ℝ)-1))+Real.exp (x/((v:ℝ)-1))) η := by fun_prop
  have hp : 0 < Real.exp (η/((u:ℝ)-1))+Real.exp (η/((v:ℝ)-1)) := add_pos (Real.exp_pos _) (Real.exp_pos _)
  have hb : Real.exp (η/((u:ℝ)-1))+Real.exp (η/((v:ℝ)-1)) < 1 := by
    simpa only [n18Inv,hu,hv,ite_false] using n18_sum_lt_one hη u v
  have hl := hs.log hp.ne'
  have hn := (Real.log_neg hp hb).ne
  have hc : ContinuousAt (fun x : ℝ => max 0 (1+x/Real.log (Real.exp (x/((u:ℝ)-1))+Real.exp (x/((v:ℝ)-1))))) η :=
    continuousAt_const.max (continuousAt_const.add (continuousAt_id.div hl hn))
  simpa only [nelsen18_cdf_of_lt_one _ _ u v hu' hv',Function.comp_def] using hc.tendsto.comp ht

theorem n18_diagonal_normalized (θ : ℝ) (hθ : 2 ≤ θ) (t : I) (ht : t < 1) :
    (nelsen18 θ hθ).diagonal t = max 0 (1+1/(Real.log 2/θ+1/((t:ℝ)-1))) := by
  have hp : θ ≠ 0 := by linarith
  rw [Copula.diagonal,nelsen18_cdf_of_lt_one θ hθ t t ht ht,← two_mul,
    Real.log_mul (by norm_num) (Real.exp_pos _).ne',Real.log_exp]
  have he : (Real.log 2+θ/((t:ℝ)-1))/θ = Real.log 2/θ+1/((t:ℝ)-1) := by
    rw [add_div,div_right_comm θ ((t:ℝ)-1) θ,div_self hp]
  rw [← he,one_div_div]

theorem nelsen18_diagonal_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 2 ≤ θ a) (ht : Tendsto θ l atTop) (t : I) :
    Tendsto (fun a => (nelsen18 (θ a) (hθ a)).diagonal t) l (𝓝 (t:ℝ)) := by
  by_cases h1 : t = 1
  · subst t; simp only [Copula.diagonal,cdf_two_one_left]; exact tendsto_const_nhds
  have ht1 : t < 1 := lt_of_le_of_ne t.property.2 h1
  have hn : (t:ℝ)-1 ≠ 0 := sub_ne_zero.mpr (by simpa using h1)
  have hi := tendsto_inv_atTop_zero.comp ht
  have hd : Tendsto (fun a => Real.log 2/θ a+1/((t:ℝ)-1)) l (𝓝 (1/((t:ℝ)-1))) := by
    simpa only [Function.comp_def,zero_add,mul_zero,← div_eq_mul_inv] using (hi.const_mul (Real.log 2)).add_const (1/((t:ℝ)-1))
  have hc := (tendsto_const_nhds (x := (1:ℝ))).div hd (one_div_ne_zero hn)
  have hg := (tendsto_const_nhds (x := (0:ℝ))).max (hc.const_add 1)
  have he : max 0 (1+1/(1/((t:ℝ)-1))) = (t:ℝ) := by
    rw [one_div_one_div,add_sub_cancel,max_eq_right t.property.1]
  rw [he] at hg
  simpa only [n18_diagonal_normalized _ _ t ht1,Pi.div_apply] using hg

theorem nelsen18_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 2 ≤ θ a) (ht : Tendsto θ l atTop) (u v : I) :
    Tendsto (fun a => (nelsen18 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((comonotonic 2).cdf ![u,v])) := by
  have he : (comonotonic 2).cdf ![u,v] = (min u v:ℝ) := by rw [cdf_comonotonic_two]; rfl
  rw [he]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (nelsen18_diagonal_tendsto_atTop θ hθ ht (min u v)) tendsto_const_nhds
  · exact Eventually.of_forall fun a => (nelsen18 (θ a) (hθ a)).monotone_cdf (by
      intro i; fin_cases i
      · exact min_le_left u v
      · exact min_le_right u v)
  · exact Eventually.of_forall fun a => le_min ((nelsen18 (θ a) (hθ a)).cdf_le_coord ![u,v] 0)
      ((nelsen18 (θ a) (hθ a)).cdf_le_coord ![u,v] 1)

end Verification
