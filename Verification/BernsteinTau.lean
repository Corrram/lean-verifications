import Verification.BernsteinDensity
import Verification.BernsteinMixedProducts
import Copula.Rank.Basic

open MeasureTheory ProbabilityTheory
open scoped unitInterval BigOperators

namespace Verification

theorem bernstein_cdf_grid (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n) (u : Fin 2 → I) :
    (C.bernstein m n hm hn).cdf u = ∑ i : Fin m, ∑ j : Fin n,
      C.cdf ![_root_.bernstein.z i.succ,_root_.bernstein.z j.succ] *
        _root_.bernstein m (i.val+1) (u 0) * _root_.bernstein n (j.val+1) (u 1) := by
  rw [Copula.cdf_bernstein,Copula.bernsteinCDF_eq_sum,Fin.sum_univ_succ]
  simp only [_root_.bernstein.z_zero,Copula.cdf_two_zero_left,zero_mul,
    Finset.sum_const_zero,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ]
  simp only [_root_.bernstein.z_zero,Copula.cdf_two_zero_right,zero_mul,zero_add,Fin.val_succ]

/-- Exact finite sum for Kendall tau, with every mixed Bernstein integral evaluated. -/
theorem bernstein_tau_finite_sum (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n) :
    (C.bernstein m n hm hn).kendallTau =
      4 * (∑ i : Fin m, ∑ j : Fin n, ∑ r : Fin m, ∑ s : Fin n,
        C.cdf ![_root_.bernstein.z i.succ,_root_.bernstein.z j.succ] *
        C.cdf ![_root_.bernstein.z r.succ,_root_.bernstein.z s.succ] *
        bernsteinMixedGram m i r * bernsteinMixedGram n j s) - 1 := by
  let D (i : Fin m) (j : Fin n) := C.cdf ![_root_.bernstein.z i.succ,_root_.bernstein.z j.succ]
  let F (i : Fin m) (j : Fin n) (x : Fin 2 → I) :=
    D i j * bernsteinDerivative m (i.val+1) (x 0) * bernsteinDerivative n (j.val+1) (x 1)
  let G (i : Fin m) (j : Fin n) (x : Fin 2 → I) :=
    D i j * _root_.bernstein m (i.val+1) (x 0) * _root_.bernstein n (j.val+1) (x 1)
  have hs (x : Fin 2 → I) : bernsteinDensity C m n x * (C.bernstein m n hm hn).cdf x =
      ∑ i, ∑ j, ∑ r, ∑ s, F i j x * G r s x := by
    rw [bernstein_cdf_grid]
    change (∑ i, ∑ j, F i j x) * (∑ r, ∑ s, G r s x) = _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.mul_sum]
  have hint (i r : Fin m) (j s : Fin n) :
      (∫ x, F i j x * G r s x) = D i j * D r s * bernsteinMixedGram m i r * bernsteinMixedGram n j s := by
    have he (x : Fin 2 → I) : F i j x * G r s x =
        (D i j * D r s) * ((bernsteinDerivative m (i.val+1) (x 0) * _root_.bernstein m (r.val+1) (x 0)) *
        (bernsteinDerivative n (j.val+1) (x 1) * _root_.bernstein n (s.val+1) (x 1))) := by
      dsimp only [F,G]
      ring
    simp_rw [he]
    rw [integral_const_mul]
    change (D i j * D r s) * (∫ x, _ ∂(Copula.independence 2).toMeasure) = _
    rw [Copula.integral_independence_mul
      (fun u => bernsteinDerivative m (i.val+1) u * _root_.bernstein m (r.val+1) u)
      (fun v => bernsteinDerivative n (j.val+1) v * _root_.bernstein n (s.val+1) v),
      integral_bernsteinDerivative_mul,integral_bernsteinDerivative_mul]
    ring
  rw [Copula.kendallTau,integral_bernstein_density]
  simp_rw [hs]
  simp (disch := intro i hi; exact Copula.integrable_continuous_cube volume (by unfold F G bernsteinDerivative; fun_prop)) only
    [integral_finsetSum,hint,D]

end Verification
