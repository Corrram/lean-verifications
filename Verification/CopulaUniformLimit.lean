import Copula.CDF.Continuity
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.Ascoli

open ProbabilityTheory Filter
open scoped unitInterval Topology

namespace Verification

theorem copula_cdf_uniform_limit_of_pointwise {ι : Type*} {l : Filter ι} {d : ℕ}
    (C : ι→Copula d) (F : (Fin d→I)→ℝ)
    (h : ∀ u,Tendsto (fun i => (C i).cdf u) l (nhds (F u))) :
    TendstoUniformly (fun i => (C i).cdf) F l := by
  have hm : Tendsto (fun x : ℝ => (d:ℝ)*x) (nhds 0) (nhds 0) := by
    simpa only [id_eq,mul_zero] using (continuous_id.tendsto (0:ℝ)).const_mul (d:ℝ)
  have he : Equicontinuous (fun i => (C i).cdf) :=
    Metric.equicontinuous_of_continuity_modulus (fun x : ℝ => (d:ℝ)*x) hm _
      (fun x y i => (C i).lipschitzWith_cdf.dist_le_mul x y)
  have hp := (he.tendsto_uniformFun_iff_pi l F).mpr (tendsto_pi_nhds.mpr h)
  exact UniformFun.tendsto_iff_tendstoUniformly.mp hp

end Verification
