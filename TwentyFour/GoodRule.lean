import TwentyFour.GoodRuleArithmetic
import TwentyFour.Parametric

namespace TwentyFour

/-- The general good-rule theorem. This is valid for arbitrary integer
parameters and arbitrary denominators, and does not rely on finite testing. -/
theorem good_rule
    (s r w m y : ℤ)
    (hs : s ≠ 0) (hw : w ≠ 0) (hm : m ≠ 0) (hy : y ≠ 0)
    (hymD : y * (Int.gcd w (s * m) : ℤ) ∣ m * (Int.gcd w s : ℤ))
    (hunit : w ∣ s * m * y - (Int.gcd w (s * m) : ℤ) ∨
      w ∣ s * m * y + (Int.gcd w (s * m) : ℤ))
    (hmod : s * m ∣ r - w)
    (hr0 : r ≠ 0) (hrw : r ≠ w)
    (hrD : r ≠ (Int.gcd w (s * m) : ℤ))
    (hrnD : r ≠ -(Int.gcd w (s * m) : ℤ)) :
    HasRelation ((s : ℚ) / r) := by
  obtain ⟨n⟩ := normalize_good_rule s r w m y hs hw hm hy hymD hunit hmod hr0 hrw hrD hrnD
  rw [← n.ratio]
  exact good_basic_scaled n.s1 n.r1 n.w1 n.m1 n.y1 n.t n.u n.scale
    n.hr n.hunit n.hym n.hm n.hy n.ht n.hr0 n.hr1 n.hrn1 n.hscale

end TwentyFour
