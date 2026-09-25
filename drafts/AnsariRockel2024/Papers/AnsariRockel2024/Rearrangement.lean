import Verification.RearrangedCopula
import Copula.Rank.ConditionalDerivative
import Copula.Order.SymmetricSchur

/-! # Rearrangement-based Schur order (Lemma 2.4, Lemma 2.7, Proposition 3.1)

The paper defines `D ≤_{∂₁S} E` by comparing decreasing rearrangements of the partial
derivatives `∂₁D(·,v)` and `∂₁E(·,v)` (Definition 2.3). The library order `SchurLE`
compares the conditional distributions through continuous convex tests. Lemma 2.4 is their
equivalence; it combines the almost-everywhere derivative bridge with the
Hardy–Littlewood–Pólya theorem on the unit interval.
-/

open MeasureTheory ProbabilityTheory Set Filter Copula Verification
open scoped unitInterval

namespace Papers.AnsariRockel2024

/-- Definition 2.3: `D ≤_{∂₁S} E` via decreasing rearrangements of `∂₁D(·,v)`. -/
def PaperSchurLE (D E : Copula 2) : Prop :=
  ∀ v : I, 0<v → v<1 →
    RearrSchurLE (fun u : I => deriv (cdfSection D v) u) (fun u : I => deriv (cdfSection E v) u)

/-- Definition 2.3: the two-direction order `≤_{∂S}`. -/
def PaperSchurBothLE (D E : Copula 2) : Prop :=
  PaperSchurLE D E ∧ PaperSchurLE D.transpose E.transpose

theorem rearrSchurLE_congr {f f' g g' : I → ℝ} (hf : f=ᵐ[volume] f') (hg : g=ᵐ[volume] g') :
    RearrSchurLE f g ↔ RearrSchurLE f' g' := by
  unfold RearrSchurLE
  rw [decRearr_congr hf,decRearr_congr hg,integral_congr_ae hf,integral_congr_ae hg]

theorem schur_endpoint_trivial (D E : Copula 2) (v : I) (hv : v=0 ∨ v=1) (φ : ℝ → ℝ) :
    (∫ u : I, φ (D.conditionalCDF u v))=∫ u : I, φ (E.conditionalCDF u v) := by
  rcases hv with h|h
  · subst h
    rw [integral_congr_ae ((condSection_zero_ae D).fun_comp φ),
      integral_congr_ae ((condSection_zero_ae E).fun_comp φ)]
  · subst h
    have hD : (fun u => D.conditionalCDF u 1)=fun _ => (1:ℝ) := funext (condSection_one D)
    have hE : (fun u => E.conditionalCDF u 1)=fun _ => (1:ℝ) := funext (condSection_one E)
    change (∫ u : I, φ ((fun u => D.conditionalCDF u 1) u))=∫ u : I, φ ((fun u => E.conditionalCDF u 1) u)
    rw [hD,hE]

/-- Lemma 2.4: the rearrangement Schur order of partial derivatives coincides with the
Schur order of conditional distributions (convex-test form). -/
theorem paperSchurLE_iff (D E : Copula 2) : PaperSchurLE D E ↔ D.SchurLE E := by
  have hc (C : Copula 2) (v : I) : (fun u : I => deriv (cdfSection C v) u)=ᵐ[volume] condSection C v :=
    (conditionalCDF_eq_deriv C v).symm
  constructor
  · intro h
    rw [← condRearrSchurLE_iff]
    intro v
    by_cases hv : v=0 ∨ v=1
    · refine (rearrSchurLE_iff_convex (condSection_nonneg D v) (condSection_le_one D v)
        (condSection_measurable D v) (condSection_nonneg E v) (condSection_le_one E v)
        (condSection_measurable E v)).mpr ?_
      intro φ _ _
      exact (schur_endpoint_trivial D E v hv φ).le
    push_neg at hv
    have h0 : 0<v := lt_of_le_of_ne v.property.1 (fun e => hv.1 (Subtype.ext e.symm))
    have h1 : v<1 := lt_of_le_of_ne v.property.2 (fun e => hv.2 (Subtype.ext e))
    exact (rearrSchurLE_congr (hc D v) (hc E v)).mp (h v h0 h1)
  · intro h v _ _
    rw [rearrSchurLE_congr (hc D v) (hc E v)]
    exact (condRearrSchurLE_iff D E).mpr h v

theorem paperSchurBothLE_iff (D E : Copula 2) : PaperSchurBothLE D E ↔ D.SchurBothLE E := by
  unfold PaperSchurBothLE SchurBothLE
  rw [paperSchurLE_iff,paperSchurLE_iff]

/-- Lemma 2.7(i): `E↓ ≤_lo D ≤_lo E↑` for every `D ≤_{∂₁S} E`, and both bounds belong to the
class. -/
theorem rearranged_extremal (D E : Copula 2) (h : D.SchurLE E) :
    (downRearr E).LowerOrthantLE D ∧ D.LowerOrthantLE (upRearr E) :=
  ⟨downRearr_lowerOrthantLE_of_schurLE h,lowerOrthantLE_upRearr_of_schurLE h⟩

theorem rearranged_mem (E : Copula 2) : (upRearr E).SchurLE E ∧ (downRearr E).SchurLE E :=
  ⟨upRearr_mem E,downRearr_mem E⟩

/-- Uniqueness of the lower-orthant maximum and minimum. -/
theorem rearranged_unique_max (E M : Copula 2) (hM : M.SchurLE E)
    (hmax : ∀ D : Copula 2, D.SchurLE E → D.LowerOrthantLE M) : M=upRearr E := by
  apply ext_cdf
  intro u
  exact le_antisymm (lowerOrthantLE_upRearr_of_schurLE hM u) (hmax _ (upRearr_mem E) u)

theorem rearranged_unique_min (E M : Copula 2) (hM : M.SchurLE E)
    (hmin : ∀ D : Copula 2, D.SchurLE E → M.LowerOrthantLE D) : M=downRearr E := by
  apply ext_cdf
  intro u
  exact le_antisymm (hmin _ (downRearr_mem E) u) (downRearr_lowerOrthantLE_of_schurLE hM u)

/-- Lemma 2.7(ii): `E↑` is CIS. -/
theorem upRearr_cis (E : Copula 2) : (upRearr E).IsSI := upRearr_isSI E

/-- Lemma 2.7(iii): `E↓(u,v)=v-E↑(1-u,v)`. -/
theorem downRearr_formula (E : Copula 2) (u v : I) :
    (downRearr E).cdf ![u,v]=(v:ℝ)-(upRearr E).cdf ![unitInterval.symm u,v] :=
  downRearr_cdf E u v

/-- Lemma 2.7(iv): `E↑ =_{∂₁S} E =_{∂₁S} E↓`. -/
theorem rearranged_schur_equiv (E : Copula 2) :
    ((upRearr E).SchurLE E ∧ E.SchurLE (upRearr E)) ∧
      ((downRearr E).SchurLE E ∧ E.SchurLE (downRearr E)) :=
  ⟨upRearr_schur_equiv E,downRearr_schur_equiv E⟩

/-- The increasing rearrangement in explicit form `E↑(u,v)=∫_0^u (∂₁E(·,v))*`. -/
theorem upRearr_formula (E : Copula 2) (u v : I) :
    (upRearr E).cdf ![u,v]=∫ s in Iic u, decRearr (fun t : I => deriv (cdfSection E v) t) s := by
  rw [upRearr_cdf,upRearrCDF,decRearr_congr (conditionalCDF_eq_deriv E v)]
  rfl

/-- Proposition 3.1: `D ≤_{∂₁S} E ⇔ D↑ ≤_lo E↑ ⇔ D↓ ≥_lo E↓`. -/
theorem prop31 (D E : Copula 2) :
    (PaperSchurLE D E ↔ (upRearr D).LowerOrthantLE (upRearr E)) ∧
    ((upRearr D).LowerOrthantLE (upRearr E) ↔ (downRearr E).LowerOrthantLE (downRearr D)) :=
  ⟨(paperSchurLE_iff D E).trans (schurLE_iff_upRearr D E),upRearr_lowerOrthant_iff_downRearr D E⟩

end Papers.AnsariRockel2024
