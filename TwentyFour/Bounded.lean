import TwentyFour.SimpleDirect
import TwentyFour.Parametric
import TwentyFour.GoodRuleArithmetic
import TwentyFour.CoverBridge
import TwentyFour.FiniteWords

/-! A uniform syllable bound for every denominator of absolute value greater
than six. The infinite families use the explicit twelve-syllable commutator,
and the twenty-three numerical exceptions have certificates of length at most
sixty-four. No claim about word length is inferred from mere nonfreeness. -/

namespace TwentyFour

/-- A nonempty reduced relation with at most sixty-four syllables. -/
def BoundedRelation (q : ℚ) : Prop :=
  ∃ l : List Syllable, ReducedSyllables l ∧ l ≠ [] ∧ l.length ≤ 64 ∧
    word l ≠ 1 ∧ eval q (word l) = 1

/-- Negating precisely the powers of the upper-triangular generator. -/
def negateBSyllables (l : List Syllable) : List Syllable :=
  l.map (fun s => (s.1, if s.1 then -s.2 else s.2))

theorem word_negateBSyllables (l : List Syllable) :
    word (negateBSyllables l) = negateGenerator (word l) := by
  induction l with
  | nil => simp [negateBSyllables]
  | cons s l ih =>
    rcases s with ⟨b,n⟩
    cases b <;> simp [negateBSyllables, negateGenerator, zpow_neg] <;>
      simpa [negateBSyllables, negateGenerator] using ih

theorem reduced_negateBSyllables {l : List Syllable} (h : ReducedSyllables l) :
    ReducedSyllables (negateBSyllables l) := by
  constructor
  · simpa [negateBSyllables, List.isChain_map] using h.1
  · intro s hs
    obtain ⟨⟨b,n⟩, hm, rfl⟩ := List.mem_map.mp hs
    have hn := h.2 (b,n) hm
    cases b <;> simpa using hn

theorem boundedRelation_neg {q : ℚ} (h : BoundedRelation (-q)) : BoundedRelation q := by
  obtain ⟨l, hred, hne, hlen, _, he⟩ := h
  have hred' := reduced_negateBSyllables hred
  have hne' : negateBSyllables l ≠ [] := by simpa [negateBSyllables] using hne
  refine ⟨negateBSyllables l, hred', hne', ?_, word_ne_one hred' hne', ?_⟩
  · simpa [negateBSyllables] using hlen
  · rw [word_negateBSyllables, eval_negateGenerator]
    exact he

/-- The exact generic five-block construction gives a twelve-syllable relation. -/
theorem generic_fiveBlock_scaled_bounded (s r m y u t e k scale : ℤ)
    (hr : r ≠ 0) (hscale : scale ≠ 0)
    (hm : m = k * y) (he : e = y - u * t)
    (hunit : r * u + s * m * e = 1)
    (hm0 : m ≠ 0) (hy0 : y ≠ 0) (ht0 : t ≠ 0) (he0 : e ≠ 0) :
    BoundedRelation (((s : ℚ) / r) / scale) := by
  have hk0 : k ≠ 0 := by intro hk; simp [hk] at hm; exact hm0 hm
  have h1 := mul_ne_zero hscale (mul_ne_zero hr hy0)
  have h2 := mul_ne_zero (neg_ne_zero.mpr hk0) he0
  have h3 := mul_ne_zero hscale (neg_ne_zero.mpr ht0)
  have h5 := mul_ne_zero hscale (mul_ne_zero (neg_ne_zero.mpr hr) he0)
  obtain ⟨l, hlen, hred, hn, heval⟩ := fiveBlock_unipotent_certificate
    (((s : ℚ) / r) / scale)
    (scale * (r * y)) (-k * e) (scale * (-t)) m (scale * (-r * e))
    ((k : ℚ) * t / r) h1 h2 h3 hm0 h5
    (five_block_identity_scaled s r m y u t e k scale hr hscale hm he hunit)
  refine ⟨l, hred, ?_, by omega, hn, heval⟩
  intro hz
  simp [hz] at hlen

/-- The normalized good-class construction, retaining its explicit length bound. -/
theorem good_basic_scaled_bounded (s r w m y t u scale : ℤ)
    (hr : r = w + s * m * t) (hunit : w * u + s * m * y = 1)
    (hym : y ∣ m) (hm : m ≠ 0) (hy : y ≠ 0) (ht : t ≠ 0)
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hrn1 : r ≠ -1) (hscale : scale ≠ 0) :
    BoundedRelation (((s : ℚ) / r) / scale) := by
  obtain ⟨k, hk⟩ := hym
  have hmk : m = k * y := by simpa [mul_comm] using hk
  let e := y - u * t
  have hue : r * u + s * m * e = 1 := by
    dsimp [e]
    rw [hr]
    linear_combination hunit
  have he0 : e ≠ 0 := by
    intro he
    rw [he, mul_zero, add_zero] at hue
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hue with h | h
    · exact hr1 h
    · exact hrn1 h
  exact generic_fiveBlock_scaled_bounded s r m y u t e k scale
    hr0 hscale hmk rfl hue hm hy ht he0

/-- The general good-rule theorem with the same sixty-four-syllable ceiling. -/
theorem good_rule_bounded
    (s r w m y : ℤ)
    (hs : s ≠ 0) (hw : w ≠ 0) (hm : m ≠ 0) (hy : y ≠ 0)
    (hymD : y * (Int.gcd w (s * m) : ℤ) ∣ m * (Int.gcd w s : ℤ))
    (hunit : w ∣ s * m * y - (Int.gcd w (s * m) : ℤ) ∨
      w ∣ s * m * y + (Int.gcd w (s * m) : ℤ))
    (hmod : s * m ∣ r - w)
    (hr0 : r ≠ 0) (hrw : r ≠ w)
    (hrD : r ≠ (Int.gcd w (s * m) : ℤ))
    (hrnD : r ≠ -(Int.gcd w (s * m) : ℤ)) :
    BoundedRelation ((s : ℚ) / r) := by
  obtain ⟨n⟩ := normalize_good_rule s r w m y hs hw hm hy hymD hunit hmod hr0 hrw hrD hrnD
  rw [← n.ratio]
  exact good_basic_scaled_bounded n.s1 n.r1 n.w1 n.m1 n.y1 n.t n.u n.scale
    n.hr n.hunit n.hym n.hm n.hy n.ht n.hr0 n.hr1 n.hrn1 n.hscale

/-- Both signs of the direct construction retain the explicit length bound. -/
theorem direct_odd_signed_bounded (x scale : ℤ) (hx : x % 2 = 1) (hs : scale ≠ 0) :
    BoundedRelation (((24 : ℚ) / (1 + 1260 * x : ℤ)) / scale) := by
  obtain ⟨m, y, u, t, d, hmy, hd, hu, hm0, hy0, ht0, hd0, hR0⟩ := direct_parameters x hx
  exact generic_fiveBlock_scaled_bounded 24 (1 + 1260 * x) m y u t d 6 scale
    hR0 hs hmy hd hu hm0 hy0 ht0 hd0

theorem four_residues_bounded (r : ℤ)
    (hr : r % 40320 = 1261 ∨ r % 40320 = 6299 ∨
      r % 40320 = 34021 ∨ r % 40320 = 39059) :
    BoundedRelation ((24 : ℚ) / r) := by
  obtain ⟨l, hl, hred, hn, he⟩ := simple_direct_four_residues_certificate r hr
  refine ⟨l, hred, ?_, by omega, hn, he⟩
  intro hnil
  simp [hnil] at hl

namespace FiniteCover

theorem rule_bounded (r : ℤ) (hr : 6 < r.natAbs)
    (he : r.natAbs ∉ exceptionValues) (p : Rule) (hp : p ∈ rules)
    (hc : 24 * (p.m : ℤ) ∣ r - p.w) : BoundedRelation ((24 : ℚ) / r) := by
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
  apply good_rule_bounded 24 r p.w p.m p.y (by norm_num) hw hm hy
  · simpa only [hgcd] using hdiv
  · simpa only [hgcd] using hunit
  · exact hc
  · exact hr0
  · exact hrw
  · simpa only [hgcd] using hrD
  · simpa only [hgcd] using hrnD

theorem outside_omitted_bounded (r : ℤ) (hr : 6 < r.natAbs)
    (he : r.natAbs ∉ exceptionValues)
    (hbad : (r % 40320).toNat ∉ omitted) : BoundedRelation ((24 : ℚ) / r) := by
  obtain ⟨p, hp, hc | hc⟩ := integer_cover r hbad
  · exact rule_bounded r hr he p hp hc
  · have hm : 24 * (p.m : ℤ) ∣ -r - p.w := by
      convert dvd_neg.mpr hc using 1; ring
    have h := rule_bounded (-r) (by simpa using hr) (by simpa using he) p hp hm
    apply boundedRelation_neg
    simpa only [Int.cast_neg, div_neg] using h

end FiniteCover

/-- The finite exception certificates also work for negative denominators,
without changing their length. -/
theorem signed_exception_bounded (r : ℤ) (hr : r.natAbs ∈ FiniteCover.exceptionValues) :
    BoundedRelation ((24 : ℚ) / r) := by
  have h : BoundedRelation (24 / (r.natAbs : ℚ)) := FiniteWords.exception_certificate r.natAbs hr
  by_cases hs : 0 ≤ r
  · have hc : (r.natAbs : ℚ) = (r : ℚ) := by
      have hi : (r.natAbs : ℤ) = r := Int.natAbs_of_nonneg hs
      calc
        (r.natAbs : ℚ) = ((r.natAbs : ℤ) : ℚ) := by simp
        _ = (r : ℚ) := congrArg (fun z : ℤ => (z : ℚ)) hi
    simpa only [hc] using h
  · have hc : (r.natAbs : ℚ) = -(r : ℚ) := by
      have hi : (r.natAbs : ℤ) = -r := Int.ofNat_natAbs_of_nonpos (by omega : r ≤ 0)
      calc
        (r.natAbs : ℚ) = ((r.natAbs : ℤ) : ℚ) := by simp
        _ = ((-r : ℤ) : ℚ) := congrArg (fun z : ℤ => (z : ℚ)) hi
        _ = -(r : ℚ) := by simp
    apply boundedRelation_neg
    simpa only [hc, div_neg] using h

theorem omitted_bounded (r : ℤ) (hr : (r % 40320).toNat ∈ FiniteCover.omitted) :
    BoundedRelation ((24 : ℚ) / r) := by
  have hm : 0 ≤ r % 40320 := Int.emod_nonneg r (by norm_num)
  have hh : (r % 40320).toNat = 1261 ∨ (r % 40320).toNat = 6299 ∨
      (r % 40320).toNat = 34021 ∨ (r % 40320).toNat = 39059 := by
    simpa [FiniteCover.omitted] using hr
  apply four_residues_bounded
  rcases hh with h | h | h | h <;> omega

theorem twentyfour_boundedRelation_natAbs (r : ℤ) (hr : 6 < r.natAbs) :
    BoundedRelation ((24 : ℚ) / r) := by
  by_cases he : r.natAbs ∈ FiniteCover.exceptionValues
  · exact signed_exception_bounded r he
  by_cases hb : (r % 40320).toNat ∈ FiniteCover.omitted
  · exact omitted_bounded r hb
  exact FiniteCover.outside_omitted_bounded r hr he hb

/-- Uniform all-integer certificate: a nonempty reduced relation with no more
than sixty-four syllables in the two displayed generators. -/
theorem twentyfour_boundedRelation (r : ℤ) (hr : 6 < |r|) :
    ∃ l : List Syllable, ReducedSyllables l ∧ l ≠ [] ∧ l.length ≤ 64 ∧
      word l ≠ 1 ∧ eval ((24 : ℚ) / r) (word l) = 1 := by
  apply twentyfour_boundedRelation_natAbs r
  have h : (6 : ℤ) < (r.natAbs : ℤ) := by simpa only [Int.natCast_natAbs] using hr
  exact_mod_cast h

#print axioms twentyfour_boundedRelation

end TwentyFour
