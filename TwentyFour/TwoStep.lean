import TwentyFour.Parametric
import TwentyFour.GoodRuleArithmetic
import TwentyFour.CoverBridge
import TwentyFour.FiniteWords
import TwentyFour.SimpleDirect

/-! A faithful two-step relation-number certificate: an alternating word that
starts and ends with B, has one, three, or five nonzero integer powers, and
has lower-triangular matrix value. This is a bound on the triangular word,
not merely a bound on a relation subsequently derived from it. -/

namespace TwentyFour

/-- The Kim--Koberda two-step condition in the displayed generators. -/
def TwoStep (q : ℚ) : Prop :=
  ∃ es : List ℤ, (∀ e ∈ es, e ≠ 0) ∧
    (es.length = 1 ∨ es.length = 3 ∨ es.length = 5) ∧
    matWord q true es 0 1 = 0

@[simp] theorem syllables_length (b : Bool) (es : List ℤ) :
    (syllables b es).length = es.length := by
  induction es generalizing b with
  | nil => rfl
  | cons e es ih => simp [syllables, ih]

theorem syllables_alternate (b : Bool) (es : List ℤ) :
    (syllables b es).IsChain (fun s t => s.1 ≠ t.1) := by
  induction es generalizing b with
  | nil => simp [syllables]
  | cons e es ih =>
    cases es with
    | nil => simp [syllables]
    | cons f fs =>
      rw [syllables, syllables, List.isChain_cons_cons]
      exact ⟨by cases b <;> simp, ih (!b)⟩

theorem syllables_nonzero (b : Bool) (es : List ℤ) (h : ∀ e ∈ es, e ≠ 0) :
    ∀ s ∈ syllables b es, s.2 ≠ 0 := by
  induction es generalizing b with
  | nil => simp [syllables]
  | cons e es ih =>
    have he : e ≠ 0 := h e (by simp)
    have hes : ∀ x ∈ es, x ≠ 0 := fun x hx => h x (by simp [hx])
    simpa only [syllables, List.mem_cons, forall_eq_or_imp] using
      And.intro he (ih (!b) hes)

/-- The definition certifies a genuinely nontrivial freely reduced word. -/
theorem TwoStep.nontrivial_triangular_word {q : ℚ} (h : TwoStep q) :
    ∃ l : List Syllable, ReducedSyllables l ∧ l ≠ [] ∧ l.length ≤ 5 ∧
      word l ≠ 1 ∧ matrixWord q l 0 1 = 0 := by
  obtain ⟨es, hn, hl, ht⟩ := h
  have hred : ReducedSyllables (syllables true es) :=
    ⟨syllables_alternate true es, syllables_nonzero true es hn⟩
  have hne : syllables true es ≠ [] := by
    intro he
    have hz := congrArg List.length he
    simp only [syllables_length, List.length_nil] at hz
    omega
  exact ⟨syllables true es, hred, hne, by simp only [syllables_length]; omega,
    word_ne_one hred hne, ht⟩

/-- Negate the B-exponents and retain the A-exponents of an alternating word. -/
def signedExponents : Bool → List ℤ → List ℤ
  | _, [] => []
  | b, e :: es => (if b then -e else e) :: signedExponents (!b) es

@[simp] theorem signedExponents_length (b : Bool) (es : List ℤ) :
    (signedExponents b es).length = es.length := by
  induction es generalizing b with
  | nil => rfl
  | cons e es ih => simp [signedExponents, ih]

theorem signedExponents_nonzero (b : Bool) (es : List ℤ)
    (h : ∀ e ∈ es, e ≠ 0) : ∀ e ∈ signedExponents b es, e ≠ 0 := by
  induction es generalizing b with
  | nil => simp [signedExponents]
  | cons e es ih =>
    have he : e ≠ 0 := h e (by simp)
    have hes : ∀ x ∈ es, x ≠ 0 := fun x hx => h x (by simp [hx])
    cases b <;> simp only [signedExponents, Bool.false_eq_true, Bool.not_false,
      Bool.not_true, ite_false, ite_true, List.mem_cons, forall_eq_or_imp, neg_ne_zero] <;>
      exact ⟨he, ih _ hes⟩

theorem matWord_signedExponents (q : ℚ) (b : Bool) (es : List ℤ) :
    matWord q b (signedExponents b es) = matWord (-q) b es := by
  induction es generalizing b with
  | nil => rfl
  | cons e es ih =>
    cases b
    · change lower e * matWord q true (signedExponents true es) =
        lower e * matWord (-q) true es
      rw [ih]
    · change upper (((-e : ℤ) : ℚ) * q) * matWord q false (signedExponents false es) =
        upper ((e : ℚ) * (-q)) * matWord (-q) false es
      rw [ih]
      simp

theorem twoStep_neg {q : ℚ} (h : TwoStep (-q)) : TwoStep q := by
  obtain ⟨es, hn, hl, ht⟩ := h
  refine ⟨signedExponents true es, signedExponents_nonzero true es hn, ?_, ?_⟩
  · simpa only [signedExponents_length] using hl
  · rwa [matWord_signedExponents]

/-- Five nonzero powers in B A B A B order certify the two-step condition. -/
theorem fiveBlock_twoStep (q : ℚ) (e1 e2 e3 e4 e5 : ℤ)
    (h1 : e1 ≠ 0) (h2 : e2 ≠ 0) (h3 : e3 ≠ 0) (h4 : e4 ≠ 0) (h5 : e5 ≠ 0)
    (htri : (upper ((e1 : ℚ) * q) * lower e2 * upper ((e3 : ℚ) * q) *
      lower e4 * upper ((e5 : ℚ) * q)) 0 1 = 0) : TwoStep q := by
  refine ⟨[e1,e2,e3,e4,e5], by simp [h1,h2,h3,h4,h5], by simp, ?_⟩
  simpa [matWord, matrixWord, syllables, mul_assoc] using htri

/-- The generic five-block construction certifies two-step directly. -/
theorem generic_fiveBlock_scaled_twoStep (s r m y u t e k scale : ℤ)
    (hr : r ≠ 0) (hscale : scale ≠ 0)
    (hm : m = k * y) (he : e = y - u * t)
    (hunit : r * u + s * m * e = 1)
    (hm0 : m ≠ 0) (hy0 : y ≠ 0) (ht0 : t ≠ 0) (he0 : e ≠ 0) :
    TwoStep (((s : ℚ) / r) / scale) := by
  have hk0 : k ≠ 0 := by intro hk; simp [hk] at hm; exact hm0 hm
  apply fiveBlock_twoStep (((s : ℚ) / r) / scale)
    (scale * (r * y)) (-k * e) (scale * (-t)) m (scale * (-r * e))
  · exact mul_ne_zero hscale (mul_ne_zero hr hy0)
  · exact mul_ne_zero (neg_ne_zero.mpr hk0) he0
  · exact mul_ne_zero hscale (neg_ne_zero.mpr ht0)
  · exact hm0
  · exact mul_ne_zero hscale (mul_ne_zero (neg_ne_zero.mpr hr) he0)
  · have hm := five_block_identity_scaled s r m y u t e k scale hr hscale hm he hunit
    simpa [lower] using congrArg (fun M : M2 => M 0 1) hm

/-- Normalized good classes retain the five-block triangular word. -/
theorem good_basic_scaled_twoStep (s r w m y t u scale : ℤ)
    (hr : r = w + s * m * t) (hunit : w * u + s * m * y = 1)
    (hym : y ∣ m) (hm : m ≠ 0) (hy : y ≠ 0) (ht : t ≠ 0)
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hrn1 : r ≠ -1) (hscale : scale ≠ 0) :
    TwoStep (((s : ℚ) / r) / scale) := by
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
  exact generic_fiveBlock_scaled_twoStep s r m y u t e k scale
    hr0 hscale hmk rfl hue hm hy ht he0

theorem good_rule_twoStep
    (s r w m y : ℤ)
    (hs : s ≠ 0) (hw : w ≠ 0) (hm : m ≠ 0) (hy : y ≠ 0)
    (hymD : y * (Int.gcd w (s * m) : ℤ) ∣ m * (Int.gcd w s : ℤ))
    (hunit : w ∣ s * m * y - (Int.gcd w (s * m) : ℤ) ∨
      w ∣ s * m * y + (Int.gcd w (s * m) : ℤ))
    (hmod : s * m ∣ r - w)
    (hr0 : r ≠ 0) (hrw : r ≠ w)
    (hrD : r ≠ (Int.gcd w (s * m) : ℤ))
    (hrnD : r ≠ -(Int.gcd w (s * m) : ℤ)) :
    TwoStep ((s : ℚ) / r) := by
  obtain ⟨n⟩ := normalize_good_rule s r w m y hs hw hm hy hymD hunit hmod hr0 hrw hrD hrnD
  rw [← n.ratio]
  exact good_basic_scaled_twoStep n.s1 n.r1 n.w1 n.m1 n.y1 n.t n.u n.scale
    n.hr n.hunit n.hym n.hm n.hy n.ht n.hr0 n.hr1 n.hrn1 n.hscale

/-- The branch-free direct construction has five nonzero syllables for x ≠ 0. -/
theorem simple_direct_twoStep (x : ℤ) (hx : x ≠ 0) :
    TwoStep ((24 : ℚ) / (1 + 1260 * x : ℤ)) := by
  have hr : (1 + 1260 * x : ℤ) ≠ 0 := by omega
  have he2 : (18 + 630 * x : ℤ) ≠ 0 := by omega
  have he5 : (3 + 105 * x : ℤ) ≠ 0 := by omega
  apply fiveBlock_twoStep ((24 : ℚ) / (1 + 1260 * x : ℤ))
    (3 * (1 + 1260 * x) * x) (18 + 630 * x) (-3) (18 * x)
    ((1 + 1260 * x) * (3 + 105 * x))
  · exact mul_ne_zero (mul_ne_zero (by norm_num) hr) hx
  · exact he2
  · norm_num
  · exact mul_ne_zero (by norm_num) hx
  · exact mul_ne_zero hr he5
  · simpa [lower] using congrArg (fun M : M2 => M 0 1) (simple_direct_matrix_identity x)

theorem simple_direct_signed_residue_twoStep (r : ℤ)
    (hr : (r % 1260 = 1 ∧ r ≠ 1) ∨ ((-r) % 1260 = 1 ∧ -r ≠ 1)) :
    TwoStep ((24 : ℚ) / r) := by
  rcases hr with ⟨hr, hr1⟩ | ⟨hr, hr1⟩
  · obtain ⟨x, hx, hR⟩ := simple_direct_residue_parameter r hr hr1
    rw [hR]
    exact simple_direct_twoStep x hx
  · obtain ⟨x, hx, hR⟩ := simple_direct_residue_parameter (-r) hr hr1
    apply twoStep_neg
    have h := simple_direct_twoStep x hx
    rw [← hR] at h
    simpa only [Int.cast_neg, div_neg] using h

namespace FiniteCover

theorem rule_twoStep (r : ℤ) (hr : 6 < r.natAbs)
    (he : r.natAbs ∉ exceptionValues) (p : Rule) (hp : p ∈ rules)
    (hc : 24 * (p.m : ℤ) ∣ r - p.w) : TwoStep ((24 : ℚ) / r) := by
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
  apply good_rule_twoStep 24 r p.w p.m p.y (by norm_num) hw hm hy
  · simpa only [hgcd] using hdiv
  · simpa only [hgcd] using hunit
  · exact hc
  · exact hr0
  · exact hrw
  · simpa only [hgcd] using hrD
  · simpa only [hgcd] using hrnD

theorem outside_omitted_twoStep (r : ℤ) (hr : 6 < r.natAbs)
    (he : r.natAbs ∉ exceptionValues)
    (hbad : (r % 40320).toNat ∉ omitted) : TwoStep ((24 : ℚ) / r) := by
  obtain ⟨p, hp, hc | hc⟩ := integer_cover r hbad
  · exact rule_twoStep r hr he p hp hc
  · have hm : 24 * (p.m : ℤ) ∣ -r - p.w := by
      convert dvd_neg.mpr hc using 1; ring
    have h := rule_twoStep (-r) (by simpa using hr) (by simpa using he) p hp hm
    apply twoStep_neg
    simpa only [Int.cast_neg, div_neg] using h

end FiniteCover

namespace FiniteWords

theorem twoStep_24 : TwoStep (24 / 24) := by
  refine ⟨[2, -1, 2], by norm_num, by decide, ?_⟩
  change matrixWord (24 / 24) word_24 0 1 = 0
  rw [matrix_24]
  rfl

theorem twoStep_31 : TwoStep (24 / 31) := by
  refine ⟨[1, -1, -4, -3, -93], by norm_num, by decide, ?_⟩
  change matrixWord (24 / 31) word_31 0 1 = 0
  rw [matrix_31]
  rfl

theorem twoStep_35 : TwoStep (24 / 35) := by
  refine ⟨[2, -1, 5, 4, -7], by norm_num, by decide, ?_⟩
  change matrixWord (24 / 35) word_35 0 1 = 0
  rw [matrix_35]
  rfl

theorem twoStep_37 : TwoStep (24 / 37) := by
  refine ⟨[3, -1, 3, 9, -222], by norm_num, by decide, ?_⟩
  change matrixWord (24 / 37) word_37 0 1 = 0
  rw [matrix_37]
  rfl

theorem twoStep_59 : TwoStep (24 / 59) := by
  refine ⟨[2, -1, -11, 9, 177], by norm_num, by decide, ?_⟩
  change matrixWord (24 / 59) word_59 0 1 = 0
  rw [matrix_59]
  rfl

theorem twoStep_61 : TwoStep (24 / 61) := by
  refine ⟨[4, -1, 7, -89, 61], by norm_num, by decide, ?_⟩
  change matrixWord (24 / 61) word_61 0 1 = 0
  rw [matrix_61]
  rfl

theorem twoStep_83 : TwoStep (24 / 83) := by
  refine ⟨[2, -2, 13, -15, 249], by norm_num, by decide, ?_⟩
  change matrixWord (24 / 83) word_83 0 1 = 0
  rw [matrix_83]
  rfl

theorem twoStep_85 : TwoStep (24 / 85) := by
  refine ⟨[2, -2, 15, 8, -17], by norm_num, by decide, ?_⟩
  change matrixWord (24 / 85) word_85 0 1 = 0
  rw [matrix_85]
  rfl

theorem twoStep_107 : TwoStep (24 / 107) := by
  refine ⟨[4, -1, -39, 49, 107], by norm_num, by decide, ?_⟩
  change matrixWord (24 / 107) word_107 0 1 = 0
  rw [matrix_107]
  rfl

theorem twoStep_109 : TwoStep (24 / 109) := by
  refine ⟨[1, -5, 10, -50, 109], by norm_num, by decide, ?_⟩
  change matrixWord (24 / 109) word_109 0 1 = 0
  rw [matrix_109]
  rfl

theorem twoStep_613 : TwoStep (24 / 613) := by
  refine ⟨[25, -1, -1179, 166, 1226], by norm_num, by decide, ?_⟩
  change matrixWord (24 / 613) word_613 0 1 = 0
  rw [matrix_613]
  rfl

theorem twoStep_877 : TwoStep (24 / 877) := by
  refine ⟨[2, -18, -135, 475, 877], by norm_num, by decide, ?_⟩
  change matrixWord (24 / 877) word_877 0 1 = 0
  rw [matrix_877]
  rfl

theorem twoStep_1139 : TwoStep (24 / 1139) := by
  refine ⟨[8, -6, 701, -617, 1139], by norm_num, by decide, ?_⟩
  change matrixWord (24 / 1139) word_1139 0 1 = 0
  rw [matrix_1139]
  rfl

theorem twoStep_2267 : TwoStep (24 / 2267) := by
  refine ⟨[1, -94, -206, -1039, -2267], by norm_num, by decide, ?_⟩
  change matrixWord (24 / 2267) word_2267 0 1 = 0
  rw [matrix_2267]
  rfl

/-- Every exception above 17 already has a triangular word of length 3 or 5. -/
theorem exception_twoStep (r : Nat) (hr : 17 < r)
    (he : r ∈ FiniteCover.exceptionValues) : TwoStep (24 / (r : ℚ)) := by
  simp only [FiniteCover.exceptionValues, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst r
    norm_num at hr
  · subst r
    norm_num at hr
  · subst r
    norm_num at hr
  · subst r
    norm_num at hr
  · subst r
    norm_num at hr
  · subst r
    norm_num at hr
  · subst r
    norm_num at hr
  · subst r
    norm_num at hr
  · subst r
    norm_num at hr
  · subst r
    exact twoStep_24
  · subst r
    exact twoStep_31
  · subst r
    exact twoStep_35
  · subst r
    exact twoStep_37
  · subst r
    exact twoStep_59
  · subst r
    exact twoStep_61
  · subst r
    exact twoStep_83
  · subst r
    exact twoStep_85
  · subst r
    exact twoStep_107
  · subst r
    exact twoStep_109
  · subst r
    exact twoStep_613
  · subst r
    exact twoStep_877
  · subst r
    exact twoStep_1139
  · subst r
    exact twoStep_2267

end FiniteWords

/-- Negating a denominator does not change the number of triangular-word steps. -/
theorem signed_exception_twoStep (r : ℤ) (hr : 17 < r.natAbs)
    (he : r.natAbs ∈ FiniteCover.exceptionValues) : TwoStep ((24 : ℚ) / r) := by
  have h : TwoStep (24 / (r.natAbs : ℚ)) := FiniteWords.exception_twoStep r.natAbs hr he
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
    apply twoStep_neg
    simpa only [hc, div_neg] using h

theorem omitted_twoStep (r : ℤ) (hr : (r % 40320).toNat ∈ FiniteCover.omitted) :
    TwoStep ((24 : ℚ) / r) := by
  have hm : 0 ≤ r % 40320 := Int.emod_nonneg r (by norm_num)
  have hh : (r % 40320).toNat = 1261 ∨ (r % 40320).toNat = 6299 ∨
      (r % 40320).toNat = 34021 ∨ (r % 40320).toNat = 39059 := by
    simpa [FiniteCover.omitted] using hr
  apply simple_direct_signed_residue_twoStep
  apply simple_direct_four_residues_sign
  rcases hh with h | h | h | h <;> omega

/-- A cofinite two-step theorem with the finite bound made explicit. -/
theorem twentyfour_twoStep_natAbs (r : ℤ) (hr : 17 < r.natAbs) :
    TwoStep ((24 : ℚ) / r) := by
  by_cases he : r.natAbs ∈ FiniteCover.exceptionValues
  · exact signed_exception_twoStep r hr he
  by_cases hb : (r % 40320).toNat ∈ FiniteCover.omitted
  · exact omitted_twoStep r hb
  exact FiniteCover.outside_omitted_twoStep r (by omega) he hb

/-- Every integer denominator with absolute value greater than 17 is two-step
in the original triangular-word sense, with nonzero exponents throughout. -/
theorem twentyfour_twoStep (r : ℤ) (hr : 17 < |r|) :
    TwoStep ((24 : ℚ) / r) := by
  apply twentyfour_twoStep_natAbs r
  have h : (17 : ℤ) < (r.natAbs : ℤ) := by simpa only [Int.natCast_natAbs] using hr
  exact_mod_cast h

#print axioms twentyfour_twoStep

end TwentyFour
