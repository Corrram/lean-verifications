import Verification.InteriorRectangleMeasure
import Verification.CubeFubini

open ProbabilityTheory MeasureTheory Set
open Copula
open scoped unitInterval

namespace Verification

/-- Identify an interior mixed derivative with a copula density. The density
may be unbounded near the boundary and may be assigned arbitrary nonnegative
values there. All differentiability and continuity assumptions are interior. -/
theorem copula_density_of_interior_derivatives (C : Copula 2) (f F P : ℝ → ℝ → ℝ)
    (hfn : ∀ u v : I, 0 ≤ f u v)
    (hfc : ∀ u v : ℝ, u ∈ Ioo 0 1 → v ∈ Ioo 0 1 →
      ContinuousAt (Function.uncurry f) (u,v))
    (hPc : ∀ u v : ℝ, u ∈ Ioo 0 1 → v ∈ Ioo 0 1 → ContinuousAt (fun x => P x v) u)
    (hF : ∀ u v : ℝ, u ∈ Ioo 0 1 → v ∈ Ioo 0 1 → HasDerivAt (fun x => F x v) (P u v) u)
    (hP : ∀ u v : ℝ, u ∈ Ioo 0 1 → v ∈ Ioo 0 1 → HasDerivAt (P u) (f u v) v)
    (hCDF : ∀ u v : I, 0 < (u:ℝ) → (u:ℝ) < 1 → 0 < (v:ℝ) → (v:ℝ) < 1 →
      F u v = C.cdf ![u,v]) :
    C.toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (f (x 0) (x 1))) := by
  symm
  apply measure_eq_copula_of_interior_rectangles C _ (withDensity_absolutelyContinuous _ _)
  intro a b c d ha hab hb hc hcd hd
  let s : Set (Fin 2 → I) := Set.pi Set.univ (fun i : Fin 2 => Ioc (![a,c] i) (![b,d] i))
  let t : Set (Fin 2 → I) := Set.pi Set.univ (fun i : Fin 2 => Icc (![a,c] i) (![b,d] i))
  have hs : MeasurableSet s := MeasurableSet.pi Set.countable_univ (fun i _ => by fin_cases i <;> simp)
  have hcont : ContinuousOn (fun x : Fin 2 → I => f (x 0) (x 1)) t := by
    intro x hx
    have h0 : a ≤ x 0 ∧ x 0 ≤ b := (Set.mem_pi.mp hx) 0 (by simp)
    have h1 : c ≤ x 1 ∧ x 1 ≤ d := (Set.mem_pi.mp hx) 1 (by simp)
    have hxy : ContinuousAt (fun y : Fin 2 → I => ((y 0:ℝ),(y 1:ℝ))) x :=
      ((continuous_subtype_val.comp (continuous_apply 0)).prodMk
        (continuous_subtype_val.comp (continuous_apply 1))).continuousAt
    exact ((hfc (x 0) (x 1) ⟨ha.trans_le h0.1,(show (x 0:ℝ) ≤ b from h0.2).trans_lt hb⟩
      ⟨hc.trans_le h1.1,(show (x 1:ℝ) ≤ d from h1.2).trans_lt hd⟩).comp
        (f := fun y : Fin 2 → I => ((y 0:ℝ),(y 1:ℝ))) (x := x) hxy).continuousWithinAt
  have ht : IsCompact t := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hi : IntegrableOn (fun x : Fin 2 → I => f (x 0) (x 1)) s :=
    (hcont.integrableOn_compact (μ := volume) ht).mono_set
      (fun x hx => Set.mem_pi.mpr (fun i hi => Ioc_subset_Icc_self ((Set.mem_pi.mp hx) i hi)))
  have humem (u : ℝ) (hu : u ∈ uIcc (a:ℝ) (b:ℝ)) : u ∈ Ioo (0:ℝ) 1 := by
    rw [uIcc_of_le (show (a:ℝ) ≤ b from hab)] at hu
    exact ⟨ha.trans_le hu.1,hu.2.trans_lt hb⟩
  have hvmem (v : ℝ) (hv : v ∈ uIcc (c:ℝ) (d:ℝ)) : v ∈ Ioo (0:ℝ) 1 := by
    rw [uIcc_of_le (show (c:ℝ) ≤ d from hcd)] at hv
    exact ⟨hc.trans_le hv.1,hv.2.trans_lt hd⟩
  have hinner (u : ℝ) (hu : u ∈ Ioo 0 1) :
      (∫ v in (c:ℝ)..(d:ℝ), f u v) = P u d-P u c := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v hv => hP u v hu (hvmem v hv))
    apply ContinuousOn.intervalIntegrable
    intro v hv
    have hh : ContinuousAt (f u) v := (hfc u v hu (hvmem v hv)).comp
      (f := fun y : ℝ => (u,y)) (x := v) (continuousAt_const.prodMk continuousAt_id)
    exact hh.continuousWithinAt
  have houter (v : ℝ) (hv : v ∈ Ioo 0 1) :
      (∫ u in (a:ℝ)..(b:ℝ), P u v) = F b v-F a v := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => hF u v (humem u hu) hv)
    exact (show ContinuousOn (fun u => P u v) (uIcc (a:ℝ) (b:ℝ)) from
      fun u hu => (hPc u v (humem u hu) hv).continuousWithinAt).intervalIntegrable
  have hPi (v : ℝ) (hv : v ∈ Ioo 0 1) : IntervalIntegrable (fun u => P u v) volume (a:ℝ) (b:ℝ) :=
    (show ContinuousOn (fun u => P u v) (uIcc (a:ℝ) (b:ℝ)) from
      fun u hu => (hPc u v (humem u hu) hv).continuousWithinAt).intervalIntegrable
  have hdi : (d:ℝ) ∈ Ioo 0 1 := ⟨hc.trans_le hcd,hd⟩
  have hci : (c:ℝ) ∈ Ioo 0 1 := ⟨hc,(show (c:ℝ) ≤ d from hcd).trans_lt hd⟩
  have hdouble : (∫ u in (a:ℝ)..(b:ℝ), ∫ v in (c:ℝ)..(d:ℝ), f u v) =
      F b d-F a d-F b c+F a c := by
    have he : (∫ u in (a:ℝ)..(b:ℝ), ∫ v in (c:ℝ)..(d:ℝ), f u v) =
        ∫ u in (a:ℝ)..(b:ℝ), P u d-P u c :=
      intervalIntegral.integral_congr (fun u hu => hinner u (humem u hu))
    rw [he, intervalIntegral.integral_sub (hPi d hdi) (hPi c hci), houter d hdi, houter c hci]
    ring
  have hreal : (∫ x in s, f (x 0) (x 1)) = C.toMeasure.real s := by
    have hfub := integral_cube_Ioc_two_real f a b c d hab hcd hi
    rw [hfub, hdouble, C.measureReal_rectangle_two ![a,c] ![b,d]
      (by simpa [Pi.le_def, Fin.forall_fin_two] using And.intro hab hcd)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hCDF b d (ha.trans_le hab) hb hdi.1 hd, hCDF a d ha ((show (a:ℝ) ≤ b from hab).trans_lt hb) hdi.1 hd,
      hCDF b c (ha.trans_le hab) hb hc hci.2, hCDF a c ha ((show (a:ℝ) ≤ b from hab).trans_lt hb) hc hci.2]
  have hn : 0 ≤ᵐ[(volume : Measure (Fin 2 → I)).restrict s] (fun x => f (x 0) (x 1)) :=
    Filter.Eventually.of_forall (fun x => hfn (x 0) (x 1))
  change ((volume : Measure (Fin 2 → I)).withDensity (fun x => ENNReal.ofReal (f (x 0) (x 1)))) s = _
  rw [withDensity_apply _ hs, ← ofReal_integral_eq_lintegral_ofReal hi hn, hreal]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

end Verification
