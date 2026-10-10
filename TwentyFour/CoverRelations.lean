import TwentyFour.CoverBridge
import TwentyFour.GoodRule

namespace TwentyFour
namespace FiniteCover
/-- Every covered nonexceptional signed denominator yields a relation. -/
theorem rule_hasRelation (r : ℤ) (hr : 6 < r.natAbs)
    (he : r.natAbs ∉ exceptionValues) (p : Rule) (hp : p ∈ rules)
    (hc : 24 * (p.m : ℤ) ∣ r - p.w) : HasRelation ((24 : ℚ) / r) := by
  obtain ⟨hw, hm, hy, hgcd, hdiv, hunit, _, _, hexw, hexD⟩ := rules_int_valid p hp
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr
  have hrw : r ≠ (p.w : ℤ) := by
    intro h
    subst r
    simp only [Int.natAbs_natCast] at hr he
    exact he (hexw hr)
  have hrD : r ≠ (p.D : ℤ) := by
    intro h
    subst r
    simp only [Int.natAbs_natCast] at hr he
    exact he (hexD hr)
  have hrnD : r ≠ -(p.D : ℤ) := by
    intro h
    subst r
    simp only [Int.natAbs_neg, Int.natAbs_natCast] at hr he
    exact he (hexD hr)
  apply good_rule 24 r p.w p.m p.y (by norm_num) hw hm hy
  · simpa only [hgcd] using hdiv
  · simpa only [hgcd] using hunit
  · exact hc
  · exact hr0
  · exact hrw
  · simpa only [hgcd] using hrD
  · simpa only [hgcd] using hrnD

theorem outside_omitted_hasRelation (r : ℤ) (hr : 6 < r.natAbs)
    (he : r.natAbs ∉ exceptionValues)
    (hbad : (r % 40320).toNat ∉ omitted) : HasRelation ((24 : ℚ) / r) := by
  obtain ⟨p, hp, hc | hc⟩ := integer_cover r hbad
  · exact rule_hasRelation r hr he p hp hc
  · have hm : 24 * (p.m : ℤ) ∣ -r - p.w := by
      convert dvd_neg.mpr hc using 1 <;> ring
    have h := rule_hasRelation (-r) (by simpa using hr) (by simpa using he) p hp hm
    apply hasRelation_neg
    simpa only [Int.cast_neg, div_neg] using h


#print axioms outside_omitted_hasRelation
end FiniteCover
end TwentyFour
