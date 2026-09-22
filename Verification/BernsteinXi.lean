import Verification.BernsteinDerivativeProducts
import Verification.FiniteTensorIntegral

open MeasureTheory ProbabilityTheory Polynomial Set
open scoped unitInterval BigOperators

namespace Verification

theorem conditionalCDF_bernstein_grid (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n) (v : I) :
    (fun u : I => (C.bernstein m n hm hn).conditionalCDF u v) =ᵐ[volume]
      fun u : I => ∑ i : Fin m, ∑ j : Fin n,
        C.cdf ![_root_.bernstein.z i.succ,_root_.bernstein.z j.succ] *
          bernsteinDerivative m (i.val+1) u * _root_.bernstein n (j.val+1) v := by
  filter_upwards [conditionalCDF_bernstein C m n hm hn v] with u hu
  rw [hu,Fin.sum_univ_succ]
  simp only [_root_.bernstein.z_zero,Copula.cdf_two_zero_left,zero_mul,
    Finset.sum_const_zero,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ]
  simp only [_root_.bernstein.z_zero,Copula.cdf_two_zero_right,zero_mul,zero_add,Fin.val_succ]

/-- Fully evaluated finite Gram contraction for Chatterjee xi of a rectangular Bernstein copula. -/
theorem bernstein_xi_gram (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n) :
    (C.bernstein m n hm hn).chatterjeeXi =
      6 * (∑ i : Fin m, ∑ j : Fin n, ∑ r : Fin m, ∑ s : Fin n,
        C.cdf ![_root_.bernstein.z i.succ,_root_.bernstein.z j.succ] *
        C.cdf ![_root_.bernstein.z r.succ,_root_.bernstein.z s.succ] *
        bernsteinDerivativeGram m i r * bernsteinGram n n (j.val+1) (s.val+1)) - 2 := by
  let f (i : Fin m) : C(I,ℝ) := ⟨bernsteinDerivative m (i.val+1), by unfold bernsteinDerivative; fun_prop⟩
  let g (j : Fin n) : C(I,ℝ) := _root_.bernstein n (j.val+1)
  let D (i : Fin m) (j : Fin n) : ℝ := C.cdf ![_root_.bernstein.z i.succ,_root_.bernstein.z j.succ]
  have he : (∫ v : I, ∫ u : I, (C.bernstein m n hm hn).conditionalCDF u v ^ 2) =
      ∫ v : I, ∫ u : I, (∑ i, ∑ j, D i j * f i u * g j v)^2 := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v => integral_congr_ae (by
      filter_upwards [conditionalCDF_bernstein_grid C m n hm hn v] with u hu
      rw [hu]
      rfl)
  rw [Copula.chatterjeeXi,he,integral_tensor_square]
  simp only [f,g,D,ContinuousMap.coe_mk,integral_bernsteinDerivative_product,
    integral_bernstein_product_nat,bernsteinGram]

end Verification
