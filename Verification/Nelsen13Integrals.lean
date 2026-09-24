import Verification.Nelsen13Density
import Verification.CubeFubini
import Verification.PositiveRectangleMeasure

open ProbabilityTheory MeasureTheory Set
open Copula
open scoped unitInterval

namespace Verification

noncomputable def n13DensityReal (θ u v : ℝ) : ℝ :=
  n13Second θ⁻¹ (n13Inv θ u+n13Inv θ v)*n13Weight θ u*n13Weight θ v
noncomputable def n13RealCDF (θ u v : ℝ) : ℝ := n13Psi θ⁻¹ (n13Inv θ u+n13Inv θ v)

theorem n13Inv_continuousAt {θ u : ℝ} (hu : 0 < u) (ha : 0 < 1-Real.log u) :
    ContinuousAt (n13Inv θ) u := (n13Inv_deriv hu ha).continuousAt

theorem n13Weight_continuousAt {θ u : ℝ} (hu : 0 < u) (ha : 0 < 1-Real.log u) :
    ContinuousAt (n13Weight θ) u := by
  unfold n13Weight
  have hA : ContinuousAt (fun x : ℝ => 1-Real.log x) u :=
    continuousAt_const.sub (Real.continuousAt_log hu.ne')
  exact ((continuousAt_const.mul (hA.rpow_const (Or.inl ha.ne'))).div hA ha.ne').div
    continuousAt_id hu.ne'

theorem n13Second_continuousAt (p t : ℝ) (ht : 0 < 1+t) : ContinuousAt (n13Second p) t := by
  unfold n13Second n13Psi
  have hX : ContinuousAt (fun x : ℝ => 1+x) t := continuousAt_const.add continuousAt_id
  have hP := hX.rpow_const (p := p) (Or.inl ht.ne')
  exact (((continuousAt_const.mul hP).div (hX.pow 2) (pow_ne_zero _ ht.ne')).mul
    (((continuousAt_const.mul hP).sub continuousAt_const).add continuousAt_const)).mul
      (Real.continuous_exp.continuousAt.comp (continuousAt_const.sub hP))

theorem n13Inv_nonneg_real {θ u : ℝ} (hθ : 0 ≤ θ) (hu : u ∈ Icc 0 1) : 0 ≤ n13Inv θ u :=
  n13Inv_nonneg hθ ⟨u,hu⟩

theorem n13RealCDF_eq {θ : ℝ} (hθ : 0 < θ) (u v : I) (hu : u ≠ 0) (hv : v ≠ 0) :
    n13RealCDF θ u v = (nelsen13 θ hθ.le).cdf ![u,v] := by
  rw [nelsen13_cdf θ hθ]
  simp only [hu, hv, or_self, ite_false]
  unfold n13RealCDF n13Psi n13Inv
  congr 3
  ring

theorem n13Partial_continuous_first {θ u v : ℝ} (hθ : 0 ≤ θ)
    (hu : u ∈ Ioc 0 1) (hv : v ∈ Icc 0 1) : ContinuousAt (fun x => n13Partial θ x v) u := by
  have ha : 0 < 1-Real.log u := by linarith [Real.log_nonpos hu.1.le hu.2]
  have hs : 0 < 1+(n13Inv θ u+n13Inv θ v) := by
    linarith [n13Inv_nonneg_real hθ ⟨hu.1.le,hu.2⟩, n13Inv_nonneg_real hθ hv]
  have hc : ContinuousAt (fun x => n13PsiDeriv θ⁻¹ (n13Inv θ x+n13Inv θ v)) u :=
    (n13Psi_deriv2 θ⁻¹ _ hs).continuousAt.comp (f := fun x => n13Inv θ x+n13Inv θ v) (x := u)
    ((n13Inv_continuousAt (θ := θ) hu.1 ha).add continuousAt_const)
  exact hc.neg.mul (n13Weight_continuousAt hu.1 ha)

theorem n13DensityReal_continuous_second {θ u v : ℝ} (hθ : 0 ≤ θ)
    (hu : u ∈ Icc 0 1) (hv : v ∈ Ioc 0 1) : ContinuousAt (n13DensityReal θ u) v := by
  have ha : 0 < 1-Real.log v := by linarith [Real.log_nonpos hv.1.le hv.2]
  have hs : 0 < 1+(n13Inv θ u+n13Inv θ v) := by
    linarith [n13Inv_nonneg_real hθ hu, n13Inv_nonneg_real hθ ⟨hv.1.le,hv.2⟩]
  have hc : ContinuousAt (fun y => n13Second θ⁻¹ (n13Inv θ u+n13Inv θ y)) v :=
    (n13Second_continuousAt θ⁻¹ _ hs).comp (f := fun y => n13Inv θ u+n13Inv θ y) (x := v)
    (continuousAt_const.add (n13Inv_continuousAt (θ := θ) hv.1 ha))
  exact (hc.mul continuousAt_const).mul (n13Weight_continuousAt hv.1 ha)

theorem integral_n13DensityReal_second {θ u a b : ℝ} (hθ : 0 ≤ θ)
    (hu : u ∈ Icc 0 1) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ v in a..b, n13DensityReal θ u v) = n13Partial θ u b-n13Partial θ u a := by
  have hmem (v : ℝ) (hv : v ∈ uIcc a b) : v ∈ Ioc 0 1 := by
    rw [uIcc_of_le hab] at hv
    exact ⟨ha.trans_le hv.1,hv.2.trans hb⟩
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro v hv
    have hm := hmem v hv
    exact n13Partial_deriv hm.1 (by linarith [Real.log_nonpos hm.1.le hm.2])
      (by linarith [n13Inv_nonneg_real hθ hu, n13Inv_nonneg_real hθ ⟨hm.1.le,hm.2⟩])
  · exact (show ContinuousOn (n13DensityReal θ u) (uIcc a b) from
      fun v hv => (n13DensityReal_continuous_second hθ hu (hmem v hv)).continuousWithinAt).intervalIntegrable

theorem integral_n13Partial_first {θ v a b : ℝ} (hθ : 0 ≤ θ)
    (hv : v ∈ Icc 0 1) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ u in a..b, n13Partial θ u v) = n13RealCDF θ b v-n13RealCDF θ a v := by
  have hmem (u : ℝ) (hu : u ∈ uIcc a b) : u ∈ Ioc 0 1 := by
    rw [uIcc_of_le hab] at hu
    exact ⟨ha.trans_le hu.1,hu.2.trans hb⟩
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    have hm := hmem u hu
    exact n13CDF_deriv hm.1 (by linarith [Real.log_nonpos hm.1.le hm.2])
      (by linarith [n13Inv_nonneg_real hθ hv, n13Inv_nonneg_real hθ ⟨hm.1.le,hm.2⟩])
  · exact (show ContinuousOn (fun u => n13Partial θ u v) (uIcc a b) from
      fun u hu => (n13Partial_continuous_first hθ (hmem u hu) hv).continuousWithinAt).intervalIntegrable

theorem n13Density_continuousAt {θ : ℝ} (hθ : 0 ≤ θ) (x : Fin 2 → I)
    (hx0 : 0 < (x 0:ℝ)) (hx1 : 0 < (x 1:ℝ)) : ContinuousAt (n13Density θ) x := by
  have ha (i : Fin 2) : 0 < 1-Real.log (x i:ℝ) := lt_of_lt_of_le zero_lt_one (n13_inv_base (x i))
  have hi0 : ContinuousAt (fun y : Fin 2 → I => n13Inv θ (y 0)) x :=
    (n13Inv_continuousAt (θ := θ) hx0 (ha 0)).comp
      (f := fun y : Fin 2 → I => (y 0:ℝ)) (x := x) ((continuous_subtype_val.comp (continuous_apply 0)).continuousAt)
  have hi1 : ContinuousAt (fun y : Fin 2 → I => n13Inv θ (y 1)) x :=
    (n13Inv_continuousAt (θ := θ) hx1 (ha 1)).comp
      (f := fun y : Fin 2 → I => (y 1:ℝ)) (x := x) ((continuous_subtype_val.comp (continuous_apply 1)).continuousAt)
  have hw0 : ContinuousAt (fun y : Fin 2 → I => n13Weight θ (y 0)) x :=
    (n13Weight_continuousAt (θ := θ) hx0 (ha 0)).comp
      (f := fun y : Fin 2 → I => (y 0:ℝ)) (x := x) ((continuous_subtype_val.comp (continuous_apply 0)).continuousAt)
  have hw1 : ContinuousAt (fun y : Fin 2 → I => n13Weight θ (y 1)) x :=
    (n13Weight_continuousAt (θ := θ) hx1 (ha 1)).comp
      (f := fun y : Fin 2 → I => (y 1:ℝ)) (x := x) ((continuous_subtype_val.comp (continuous_apply 1)).continuousAt)
  have hs : 0 < 1+(n13Inv θ (x 0)+n13Inv θ (x 1)) := by
    linarith [n13Inv_nonneg hθ (x 0), n13Inv_nonneg hθ (x 1)]
  exact (((n13Second_continuousAt θ⁻¹ _ hs).comp
    (f := fun y : Fin 2 → I => n13Inv θ (y 0)+n13Inv θ (y 1)) (x := x)
    (hi0.add hi1)).mul hw0).mul hw1

theorem n13Density_integrable_rectangle {θ : ℝ} (hθ : 0 ≤ θ) (a b c d : I)
    (ha : 0 < (a:ℝ)) (hc : 0 < (c:ℝ)) :
    IntegrableOn (n13Density θ) (Set.pi Set.univ (fun i : Fin 2 => Ioc (![a,c] i) (![b,d] i))) := by
  let t : Set (Fin 2 → I) := Set.pi Set.univ (fun i : Fin 2 => Icc (![a,c] i) (![b,d] i))
  have hcont : ContinuousOn (n13Density θ) t := by
    intro x hx
    have h0 : a ≤ x 0 := ((Set.mem_pi.mp hx) 0 (by simp)).1
    have h1 : c ≤ x 1 := ((Set.mem_pi.mp hx) 1 (by simp)).1
    exact (n13Density_continuousAt hθ x (ha.trans_le h0) (hc.trans_le h1)).continuousWithinAt
  have ht : IsCompact t := isCompact_univ_pi (fun _ => isCompact_Icc)
  apply (hcont.integrableOn_compact (μ := volume) ht).mono_set
  intro x hx
  exact Set.mem_pi.mpr (fun i hi => Ioc_subset_Icc_self ((Set.mem_pi.mp hx) i hi))

theorem integral_n13Density_rectangle {θ a b c d : ℝ} (hθ : 0 ≤ θ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (hc : 0 < c) (hcd : c ≤ d) (hd : d ≤ 1) :
    (∫ u in a..b, ∫ v in c..d, n13DensityReal θ u v) =
      n13RealCDF θ b d-n13RealCDF θ a d-n13RealCDF θ b c+n13RealCDF θ a c := by
  have hmem (u : ℝ) (hu : u ∈ uIcc a b) : u ∈ Ioc 0 1 := by
    rw [uIcc_of_le hab] at hu
    exact ⟨ha.trans_le hu.1,hu.2.trans hb⟩
  have hd' : d ∈ Icc (0:ℝ) 1 := ⟨(hc.trans_le hcd).le,hd⟩
  have hc' : c ∈ Icc (0:ℝ) 1 := ⟨hc.le,hcd.trans hd⟩
  have hi (v : ℝ) (hv : v ∈ Icc 0 1) : IntervalIntegrable (fun u => n13Partial θ u v) volume a b :=
    (show ContinuousOn (fun u => n13Partial θ u v) (uIcc a b) from
      fun u hu => (n13Partial_continuous_first hθ (hmem u hu) hv).continuousWithinAt).intervalIntegrable
  have he : (∫ u in a..b, ∫ v in c..d, n13DensityReal θ u v) =
      ∫ u in a..b, n13Partial θ u d-n13Partial θ u c := by
    apply intervalIntegral.integral_congr
    intro u hu
    exact integral_n13DensityReal_second hθ ⟨(hmem u hu).1.le,(hmem u hu).2⟩ hc hcd hd
  rw [he, intervalIntegral.integral_sub (hi d hd') (hi c hc'),
    integral_n13Partial_first hθ hd' ha hab hb, integral_n13Partial_first hθ hc' ha hab hb]
  ring

theorem n13Density_rectangle_eq_measure {θ : ℝ} (hθ : 0 < θ) (a b c d : I)
    (ha : 0 < (a:ℝ)) (hab : a ≤ b) (hc : 0 < (c:ℝ)) (hcd : c ≤ d) :
    (∫ x in Set.pi Set.univ (fun i : Fin 2 => Ioc (![a,c] i) (![b,d] i)), n13Density θ x) =
      (nelsen13 θ hθ.le).toMeasure.real
        (Set.pi Set.univ (fun i : Fin 2 => Ioc (![a,c] i) (![b,d] i))) := by
  have hi := n13Density_integrable_rectangle hθ.le a b c d ha hc
  have hF := integral_cube_Ioc_two_real (n13DensityReal θ) a b c d hab hcd hi
  have hR := integral_n13Density_rectangle hθ.le ha hab b.property.2 hc hcd d.property.2
  change (∫ x in Set.pi Set.univ (fun i : Fin 2 => Ioc (![a,c] i) (![b,d] i)),
    n13DensityReal θ (x 0) (x 1)) = _
  rw [hF, hR]
  rw [(nelsen13 θ hθ.le).measureReal_rectangle_two ![a,c] ![b,d]
    (by simpa [Pi.le_def, Fin.forall_fin_two] using And.intro hab hcd)]
  have ha0 : a ≠ 0 := fun h => ha.ne' (congrArg Subtype.val h)
  have hb0 : b ≠ 0 := fun h => (ha.trans_le hab).ne' (congrArg Subtype.val h)
  have hc0 : c ≠ 0 := fun h => hc.ne' (congrArg Subtype.val h)
  have hd0 : d ≠ 0 := fun h => (hc.trans_le hcd).ne' (congrArg Subtype.val h)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [n13RealCDF_eq hθ b d hb0 hd0, n13RealCDF_eq hθ a d ha0 hd0,
    n13RealCDF_eq hθ b c hb0 hc0, n13RealCDF_eq hθ a c ha0 hc0]

end Verification
