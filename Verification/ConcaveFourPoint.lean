import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

open Set

namespace Verification

/-- Increasing concave functions preserve the ordered four-point inequality
used for submodular logarithmic copula exponents. -/
theorem concave_monotone_four_point {f : ℝ→ℝ}
    (hf : ConcaveOn ℝ (Ici 0) f) (hm : MonotoneOn f (Ici 0))
    {a b c d : ℝ} (ha : 0≤a) (hab : a≤b) (hbd : b≤d)
    (hac : a≤c) (hs : a+d≤b+c) :
    f a+f d≤f b+f c := by
  have had : a≤d := hab.trans hbd
  by_cases he : a=d
  · have hb : b=a := le_antisymm (hbd.trans_eq he.symm) hab
    rw [hb,← he]
    linarith [hm ha (ha.trans hac) hac]
  have hd : 0<d-a := sub_pos.mpr (lt_of_le_of_ne had he)
  let t : ℝ := (b-a)/(d-a)
  have ht0 : 0≤t := div_nonneg (sub_nonneg.mpr hab) hd.le
  have ht1 : t≤1 := (div_le_one hd).mpr (by linarith)
  have hb : (1-t)*a+t*d=b := by dsimp [t]; field_simp; ring
  have hc : t*a+(1-t)*d=a+d-b := by dsimp [t]; field_simp; ring
  have h1 := hf.2 ha (ha.trans had) (sub_nonneg.mpr ht1) ht0 (by ring : (1-t)+t=1)
  have h2 := hf.2 ha (ha.trans had) ht0 (sub_nonneg.mpr ht1) (by ring : t+(1-t)=1)
  simp only [smul_eq_mul,hb,hc] at h1 h2
  have hp : 0≤a+d-b := by linarith
  have hm' := hm hp (ha.trans hac) (show a+d-b≤c by linarith)
  nlinarith

end Verification
