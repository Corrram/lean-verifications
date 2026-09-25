import Verification.CopulaUniformLimit
import Papers.AnsariRockel2024.JoeExtremeValueOrders

open ProbabilityTheory Filter Copula
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem galambos_limit_independence_uniform {ι : Type*} {l : Filter ι}
    (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l (nhds 0)) :
    TendstoUniformly (fun i => (Verification.galambos (δ i) (hδ i)).cdf) (independence 2).cdf l :=
  Verification.copula_cdf_uniform_limit_of_pointwise _ _ (galambos_limit_independence δ hδ hd)

theorem galambos_limit_comonotonic_uniform {ι : Type*} {l : Filter ι}
    (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l atTop) :
    TendstoUniformly (fun i => (Verification.galambos (δ i) (hδ i)).cdf) (comonotonic 2).cdf l :=
  Verification.copula_cdf_uniform_limit_of_pointwise _ _ (galambos_limit_comonotonic δ hδ hd)

theorem joeExtremeValue_limit_independence_uniform {ι : Type*} {l : Filter ι}
    (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l (nhds 0)) (α β : I) :
    TendstoUniformly (fun i => (Verification.joeExtremeValue (δ i) (hδ i) α β).cdf)
      (independence 2).cdf l :=
  Verification.copula_cdf_uniform_limit_of_pointwise _ _ (joeExtremeValue_limit_independence δ hδ hd α β)

theorem joeExtremeValue_limit_marshallOlkin_uniform {ι : Type*} {l : Filter ι}
    (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l atTop) (α β : I) :
    TendstoUniformly (fun i => (Verification.joeExtremeValue (δ i) (hδ i) α β).cdf)
      (marshallOlkin α β).cdf l :=
  Verification.copula_cdf_uniform_limit_of_pointwise _ _ (joeExtremeValue_limit_marshallOlkin δ hδ hd α β)

end Papers.AnsariRockel2024
