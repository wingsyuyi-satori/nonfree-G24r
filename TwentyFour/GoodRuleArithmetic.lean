import Mathlib.Data.Int.GCD
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace TwentyFour

/-- Integral data for the five-block relation after dividing out the common gcd.
The denominator is arbitrary: no bound or finite enumeration is used here. -/
structure NormalizedGoodRule (s r : ℤ) where
  s1 : ℤ
  r1 : ℤ
  w1 : ℤ
  m1 : ℤ
  y1 : ℤ
  t : ℤ
  u : ℤ
  scale : ℤ
  hs : s1 ≠ 0
  hw : w1 ≠ 0
  hm : m1 ≠ 0
  hy : y1 ≠ 0
  ht : t ≠ 0
  hscale : scale ≠ 0
  hscale_pos : 0 < scale
  hr0 : r1 ≠ 0
  hr1 : r1 ≠ 1
  hrn1 : r1 ≠ -1
  hr : r1 = w1 + s1 * m1 * t
  hunit : w1 * u + s1 * m1 * y1 = 1
  hym : y1 ∣ m1
  ratio : ((s1 : ℚ) / r1) / scale = (s : ℚ) / r

/-- Divisibility witnesses give the normalization without needing any identities
for integer quotients. In particular, `y * D ∣ m * d` itself proves `D/d ∣ m`. -/
theorem normalize_good_rule_factors
    (s r w m y D d : ℤ)
    (hs : s ≠ 0) (hw : w ≠ 0) (hm : m ≠ 0) (hy : y ≠ 0)
    (hDpos : 0 < D) (hdpos : 0 < d)
    (hdD : d ∣ D) (hds : d ∣ s) (hDw : D ∣ w)
    (hymD : y * D ∣ m * d) (hunit : w ∣ s * m * y - D)
    (hmod : s * m ∣ r - w)
    (hr0 : r ≠ 0) (hrw : r ≠ w) (hrD : r ≠ D) (hrnD : r ≠ -D) :
    Nonempty (NormalizedGoodRule s r) := by
  have hD : D ≠ 0 := ne_of_gt hDpos
  have hd : d ≠ 0 := ne_of_gt hdpos
  obtain ⟨k, hk⟩ := hdD
  obtain ⟨s1, hs1⟩ := hds
  obtain ⟨w1, hw1⟩ := hDw
  obtain ⟨a, ha⟩ := hymD
  obtain ⟨t, ht⟩ := hmod
  obtain ⟨v, hv⟩ := hunit
  let m1 : ℤ := y * a
  let r1 : ℤ := w1 + s1 * m1 * t
  have hm1 : m = k * m1 := by
    apply mul_right_cancel₀ hd
    calc
      m * d = y * D * a := ha
      _ = (k * m1) * d := by rw [hk]; dsimp [m1]; ring
  have hsm : s * m = D * (s1 * m1) := by
    rw [hs1, hm1, hk]
    ring
  have hr : r = D * r1 := by
    dsimp [r1]
    rw [mul_add, ← hw1, ← mul_assoc, ← hsm]
    omega
  have hkpos : 0 < k := (mul_pos_iff_of_pos_left hdpos).mp (by rwa [← hk])
  have hkn : k ≠ 0 := ne_of_gt hkpos
  have hs1n : s1 ≠ 0 := by intro h; apply hs; simpa [h] using hs1
  have hw1n : w1 ≠ 0 := by intro h; apply hw; simpa [h] using hw1
  have hm1n : m1 ≠ 0 := by intro h; apply hm; simpa [h] using hm1
  have htn : t ≠ 0 := by intro h; apply hrw; simp [h] at ht; omega
  have hr1n : r1 ≠ 0 := by intro h; apply hr0; simpa [h] using hr
  have hr1one : r1 ≠ 1 := by intro h; apply hrD; simpa [h] using hr
  have hr1negone : r1 ≠ -1 := by intro h; apply hrnD; simpa [h] using hr
  have hbez : w1 * (-v) + s1 * m1 * y = 1 := by
    apply mul_left_cancel₀ hD
    calc
      D * (w1 * (-v) + s1 * m1 * y) = -(D * w1 * v) + (D * (s1 * m1)) * y := by ring
      _ = -(w * v) + s * m * y := by rw [← hw1, ← hsm]
      _ = D * 1 := by rw [← hv]; ring
  have hq : ((s1 : ℚ) / r1) / k = (s : ℚ) / r := by
    have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hkn
    have hr1q : (r1 : ℚ) ≠ 0 := by exact_mod_cast hr1n
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    rw [hs1, hr, hk]
    push_cast
    field_simp
  exact ⟨{
    s1 := s1, r1 := r1, w1 := w1, m1 := m1, y1 := y,
    t := t, u := -v, scale := k,
    hs := hs1n, hw := hw1n, hm := hm1n, hy := hy, ht := htn,
    hscale := hkn, hscale_pos := hkpos, hr0 := hr1n, hr1 := hr1one, hrn1 := hr1negone,
    hr := rfl, hunit := hbez, hym := ⟨a, rfl⟩, ratio := hq }⟩

/-- The general good-class arithmetic lemma, with either choice of sign in the
unit congruence. A negative sign is absorbed by replacing `y` with `-y`. -/
theorem normalize_good_rule
    (s r w m y : ℤ)
    (hs : s ≠ 0) (hw : w ≠ 0) (hm : m ≠ 0) (hy : y ≠ 0)
    (hymD : y * (Int.gcd w (s * m) : ℤ) ∣ m * (Int.gcd w s : ℤ))
    (hunit : w ∣ s * m * y - (Int.gcd w (s * m) : ℤ) ∨
      w ∣ s * m * y + (Int.gcd w (s * m) : ℤ))
    (hmod : s * m ∣ r - w)
    (hr0 : r ≠ 0) (hrw : r ≠ w)
    (hrD : r ≠ (Int.gcd w (s * m) : ℤ))
    (hrnD : r ≠ -(Int.gcd w (s * m) : ℤ)) :
    Nonempty (NormalizedGoodRule s r) := by
  have hD : 0 < (Int.gcd w (s * m) : ℤ) := by
    exact_mod_cast (Int.gcd_pos_of_ne_zero_left (s * m) hw)
  have hd : 0 < (Int.gcd w s : ℤ) := by
    exact_mod_cast (Int.gcd_pos_of_ne_zero_left s hw)
  have hdD : (Int.gcd w s : ℤ) ∣ (Int.gcd w (s * m) : ℤ) := by
    apply Int.dvd_coe_gcd (Int.gcd_dvd_left w s)
    exact dvd_mul_of_dvd_left (Int.gcd_dvd_right w s) m
  rcases hunit with hminus | hplus
  · exact normalize_good_rule_factors s r w m y _ _ hs hw hm hy hD hd hdD
      (Int.gcd_dvd_right w s) (Int.gcd_dvd_left w (s * m)) hymD hminus
      hmod hr0 hrw hrD hrnD
  · apply normalize_good_rule_factors s r w m (-y) _ _ hs hw hm (neg_ne_zero.mpr hy)
      hD hd hdD (Int.gcd_dvd_right w s) (Int.gcd_dvd_left w (s * m))
      ?_ ?_ hmod hr0 hrw hrD hrnD
    · simpa only [neg_mul, Int.neg_dvd] using hymD
    · convert Int.dvd_neg.mpr hplus using 1; ring

/-- The normalized denominator lies outside {-1, 0, 1}. -/
theorem NormalizedGoodRule.abs_r1_gt_one {s r : ℤ} (n : NormalizedGoodRule s r) :
    1 < |n.r1| := by
  have h0 := n.hr0
  have h1 := n.hr1
  have hn1 := n.hrn1
  rcases le_total 0 n.r1 with h | h
  · rw [abs_of_nonneg h]
    omega
  · rw [abs_of_nonpos h]
    omega

end TwentyFour
