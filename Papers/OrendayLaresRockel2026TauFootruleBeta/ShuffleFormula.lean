import Verification.BlockShuffle

/-! # Lemma 3.1: Kendall's tau of an arbitrary signed shuffle

`S` records the horizontal and vertical tilings, with widths allowed to be
zero. `π` specifies their relative order. A true sign means +1 and a false
sign means -1. The paper's pair sum is written with the indices renamed
`j < i`; because π is injective, its sign is +1 exactly when `π j < π i`.
-/

open ProbabilityTheory Verification

namespace Papers.OrendayLaresRockel2026TauFootruleBeta

theorem shuffle_tau {n : ℕ} (S : PositiveShuffle n) (ε : Fin n → Bool)
    (π : Equiv.Perm (Fin n))
    (hx : ∀ i j, i < j → (S.strip i).x + (S.strip i).width ≤ (S.strip j).x)
    (hy : ∀ i j, π i < π j → (S.strip i).y + (S.strip i).width ≤ (S.strip j).y) :
    (S.signedCopula ε).kendallTau =
      (∑ i, (if ε i then 1 else -1) * (S.strip i).width ^ 2) +
      2 * ∑ i, ∑ j, if j < i then
        (if π j < π i then 1 else -1) * (S.strip j).width * (S.strip i).width else 0 :=
  S.signed_tau ε π hx hy

end Papers.OrendayLaresRockel2026TauFootruleBeta
