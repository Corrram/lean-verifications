import Verification.ScaleMixtureContinuity

open ProbabilityTheory MeasureTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem copula_cdf_limit_of_moving_point {ι : Type*} {l : Filter ι}
    (C : ι→Copula 2) (v : ι→Fin 2→I) (u : Fin 2→I) {L : ℝ}
    (hv : ∀ j, Tendsto (fun i => (v i j:ℝ)) l (nhds (u j:ℝ)))
    (h : Tendsto (fun i => (C i).cdf (v i)) l (nhds L)) :
    Tendsto (fun i => (C i).cdf u) l (nhds L) := by
  apply h.congr_dist
  have h0 := ((hv 0).sub_const (u 0:ℝ)).abs
  have h1 := ((hv 1).sub_const (u 1:ℝ)).abs
  have hz := h0.add h1
  simp only [sub_self,abs_zero,add_zero] at hz
  apply squeeze_zero (fun _ => dist_nonneg) _ hz
  intro i
  simpa only [Real.dist_eq,Fin.sum_univ_two] using (C i).abs_cdf_sub_le_sum_abs (v i) u

end Verification
