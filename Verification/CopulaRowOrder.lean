import Verification.CheckerboardRows
import Verification.MTP2ConditionalIncreasing

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace Verification

theorem uniform_rowMean_antitone (C : Copula 2) (hC : C.IsSI) (m : ℕ) (hm : 0<m) (v : I) :
    Antitone (fun i => copulaRowMean (IntervalPartition.uniform m hm) C i v) := by
  let P := IntervalPartition.uniform m hm
  intro i r hir
  let a := P.point i.castSucc
  let b := P.point i.succ
  let c := P.point r.castSucc
  let d := P.point r.succ
  have hab : a < b := P.strictMono Fin.castSucc_lt_succ
  have hcd : c < d := P.strictMono Fin.castSucc_lt_succ
  have hac : a ≤ c := P.strictMono.monotone (show i.castSucc ≤ r.castSucc from hir)
  have hbd : b ≤ d := P.strictMono.monotone (show i.succ ≤ r.succ by change i.val+1 ≤ r.val+1; omega)
  have had : 0 < (d : ℝ)-(a : ℝ) := sub_pos.mpr (hab.trans_le hbd)
  have hw : (b : ℝ)-(a : ℝ)=(d : ℝ)-(c : ℝ) := by
    change P.width i=P.width r
    simp only [P,IntervalPartition.width_uniform]
  have h1 := hC a b d v hab.le hbd
  have h2 := hC a c d v hac hcd.le
  have he := congrArg (fun x : ℝ => x*(C.cdf ![a,v]-C.cdf ![d,v])) hw
  have hp : 0 ≤ ((d : ℝ)-(a : ℝ))*
      ((C.cdf ![b,v]-C.cdf ![a,v])-(C.cdf ![d,v]-C.cdf ![c,v])) := by
    nlinarith [h1,h2,he]
  have hh := (mul_nonneg_iff_of_pos_left had).mp hp
  change (C.cdf ![d,v]-C.cdf ![c,v])/P.width r ≤ (C.cdf ![b,v]-C.cdf ![a,v])/P.width i
  rw [show P.width r=P.width i by simp only [P,IntervalPartition.width_uniform]]
  apply (div_le_div_iff_of_pos_right (P.width_pos i)).mpr
  linarith

theorem cdf_embed_concavity {n : ℕ} (C : Copula 2) (hC : C.transpose.IsSI)
    (Q : IntervalPartition n) (j : Fin n) (u v : I) :
    (1-(v : ℝ))*C.cdf ![u,Q.point j.castSucc]+(v : ℝ)*C.cdf ![u,Q.point j.succ] ≤
      C.cdf ![u,partitionEmbed Q j v] := by
  have h := hC (Q.point j.castSucc) (partitionEmbed Q j v) (Q.point j.succ) u
    (partitionEmbed_lower Q j v) (partitionEmbed_upper Q j v)
  simp only [Copula.cdf_transpose] at h
  have h1 : (partitionEmbed Q j v : ℝ)-(Q.point j.castSucc : ℝ)=Q.width j*(v : ℝ) := by
    change (Q.point j.castSucc : ℝ)+Q.width j*(v : ℝ)-(Q.point j.castSucc : ℝ)=_
    ring
  have h2 : (Q.point j.succ : ℝ)-(partitionEmbed Q j v : ℝ)=Q.width j*(1-(v : ℝ)) := by
    change (Q.point j.succ : ℝ)-((Q.point j.castSucc : ℝ)+Q.width j*(v : ℝ))=_
    unfold IntervalPartition.width
    ring
  rw [h1,h2,show (Q.point j.succ : ℝ)-(Q.point j.castSucc : ℝ)=Q.width j from rfl] at h
  apply le_of_mul_le_mul_left (a := Q.width j) _ (Q.width_pos j)
  nlinarith

theorem uniform_rowMean_prefix (C : Copula 2) (m : ℕ) (hm : 0<m) (k : Fin (m+1)) (v : I) :
    (∑ i : Fin m, if i.val < k.val then copulaRowMean (IntervalPartition.uniform m hm) C i v else 0) =
      (m : ℝ)*C.cdf ![(IntervalPartition.uniform m hm).point k,v] := by
  let P := IntervalPartition.uniform m hm
  have he (i : Fin m) : (if i.val < k.val then copulaRowMean P C i v else 0) =
      (if i.val < k.val then C.cdf ![P.point i.succ,v]-C.cdf ![P.point i.castSucc,v] else 0)/(1/(m : ℝ)) := by
    split_ifs <;> simp only [copulaRowMean,P,IntervalPartition.width_uniform,zero_div]
  change (∑ i : Fin m, if i.val < k.val then copulaRowMean P C i v else 0) = (m : ℝ)*C.cdf ![P.point k,v]
  simp_rw [he]
  rw [← Finset.sum_div,IntervalPartition.sum_prefix_differences (fun k => C.cdf ![P.point k,v]) k]
  simp only [P.zero,Copula.cdf_two_zero_left,sub_zero]
  field_simp

end Verification
