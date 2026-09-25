import Verification.GalambosConstruction

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem galambos_cdf_full (δ : ℝ) (hδ : 0<δ) (u : Fin 2→I) :
    (Verification.galambos δ hδ).cdf u=
      if u 0=0 ∨ u 1=0 then 0
      else if u 0=1 then (u 1:ℝ)
      else if u 1=1 then (u 0:ℝ)
      else (u 0:ℝ)*(u 1:ℝ)*Real.exp
        (((-Real.log (u 0:ℝ))^(-δ)+(-Real.log (u 1:ℝ))^(-δ))^(-1/δ)) := by
  rw [Verification.galambos_cdf]
  rfl

theorem galambos_cdf_interior (δ : ℝ) (hδ : 0<δ) (u v : I)
    (hu : (u:ℝ)∈Ioo (0:ℝ) 1) (hv : (v:ℝ)∈Ioo (0:ℝ) 1) :
    (Verification.galambos δ hδ).cdf ![u,v]=(u:ℝ)*(v:ℝ)*Real.exp
      (((-Real.log (u:ℝ))^(-δ)+(-Real.log (v:ℝ))^(-δ))^(-1/δ)) := by
  rw [galambos_cdf_full]
  have hu0 : u≠0 := fun h => hu.1.ne' (congrArg Subtype.val h)
  have hv0 : v≠0 := fun h => hv.1.ne' (congrArg Subtype.val h)
  have hu1 : u≠1 := fun h => hu.2.ne (congrArg Subtype.val h)
  have hv1 : v≠1 := fun h => hv.2.ne (congrArg Subtype.val h)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,hu0,hv0,hu1,hv1,
    or_self,ite_false]

theorem galambos_survivalClayton_maxima_limit (δ : ℝ) (hδ : 0<δ) (u : Fin 2→I) :
    Tendsto (fun n => (Verification.normalizedMaxima (clayton 2 δ hδ).survivalCopula n).cdf u)
      atTop (nhds ((Verification.galambos δ hδ).cdf u)) := by
  rw [Verification.galambos_cdf]
  exact Verification.galambos_maxima_limit δ hδ u

end Papers.AnsariRockel2024
