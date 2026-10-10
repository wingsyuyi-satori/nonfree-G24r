import TwentyFour.Core

/-! A branch-free direct construction for the two residue classes ±1 modulo
1260. The only excluded parameter is x = 0, which would give a zero syllable.
This module imports only Core and does not use a 3-adic factorization. -/

namespace TwentyFour

/-- The fixed-parameter direct construction. -/
theorem simple_direct_parameters (x : ℤ) (hx : x ≠ 0) :
    18 * x = 6 * (3 * x) ∧
    -3 - 105 * x = 3 * x - (1 + 36 * x) * 3 ∧
    (1 + 1260 * x) * (1 + 36 * x) + 24 * (18 * x) * (-3 - 105 * x) = 1 ∧
    18 * x ≠ 0 ∧ 3 * x ≠ 0 ∧ (3 : ℤ) ≠ 0 ∧
    -3 - 105 * x ≠ 0 ∧ 1 + 1260 * x ≠ 0 := by
  refine ⟨by ring, by ring, by ring, ?_, ?_, by norm_num, ?_, ?_⟩ <;> omega

/-- Exact five-block matrix identity for every integral x, including x = 0. -/
theorem simple_direct_matrix_identity (x : ℤ) :
    upper (((3 * (1 + 1260 * x) * x : ℤ) : ℚ) * ((24 : ℚ) / (1 + 1260 * x : ℤ))) *
    lower ((18 + 630 * x : ℤ) : ℚ) *
    upper ((-3 : ℚ) * ((24 : ℚ) / (1 + 1260 * x : ℤ))) *
    lower ((18 * x : ℤ) : ℚ) *
    upper ((((1 + 1260 * x) * (3 + 105 * x) : ℤ) : ℚ) *
      ((24 : ℚ) / (1 + 1260 * x : ℤ))) =
    lower ((18 : ℚ) / (1 + 1260 * x : ℤ)) := by
  have hr : (1 + 1260 * (x : ℚ)) ≠ 0 := by
    exact_mod_cast (show (1 + 1260 * x : ℤ) ≠ 0 by omega)
  have hr' : (1 + (x : ℚ) * 1260) ≠ 0 := by simpa only [mul_comm] using hr
  push_cast
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, lower, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hr, hr'] <;> ring

/-- The matrix certificate written directly as the five powers used in the paper. -/
theorem simple_direct_power_identity (x : ℤ) :
    B ((24 : ℚ) / (1 + 1260 * x : ℤ)) ^ (3 * (1 + 1260 * x) * x) *
    A ^ (18 + 630 * x) *
    B ((24 : ℚ) / (1 + 1260 * x : ℤ)) ^ (-3 : ℤ) *
    A ^ (18 * x) *
    B ((24 : ℚ) / (1 + 1260 * x : ℤ)) ^ ((1 + 1260 * x) * (3 + 105 * x)) =
    lowerSL ((18 : ℚ) / (1 + 1260 * x : ℤ)) := by
  apply Subtype.ext
  simpa only [Matrix.SpecialLinearGroup.coe_mul, A_zpow_val, B_zpow_val,
    Int.cast_neg, Int.cast_ofNat, lowerSL_coe] using simple_direct_matrix_identity x

/-- Scaling all B-exponents preserves the displayed matrix identity at q/scale. -/
theorem simple_direct_scaled_matrix_identity (x scale : ℤ) (hs : scale ≠ 0) :
    let q : ℚ := ((24 : ℚ) / (1 + 1260 * x : ℤ)) / scale
    upper (((scale * (3 * (1 + 1260 * x) * x) : ℤ) : ℚ) * q) *
    lower ((18 + 630 * x : ℤ) : ℚ) *
    upper (((scale * (-3) : ℤ) : ℚ) * q) *
    lower ((18 * x : ℤ) : ℚ) *
    upper (((scale * ((1 + 1260 * x) * (3 + 105 * x)) : ℤ) : ℚ) * q) =
    lower ((18 : ℚ) / (1 + 1260 * x : ℤ)) := by
  have hsq : (scale : ℚ) ≠ 0 := by exact_mod_cast hs
  have hcancel (a q : ℚ) : ((scale : ℚ) * a) * (q / scale) = a * q := by
    field_simp [hsq]
  dsimp
  push_cast
  rw [hcancel, hcancel, hcancel]
  simpa only [Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_ofNat] using
    simple_direct_matrix_identity x

/-- Every nonzero parameter gives a nontrivial reduced twelve-syllable relation.
The scaling parameter includes both signs and more general integral pullbacks. -/
theorem simple_direct_scaled_certificate (x scale : ℤ) (hx : x ≠ 0) (hs : scale ≠ 0) :
    ∃ l : List Syllable, l.length = 12 ∧ ReducedSyllables l ∧
      word l ≠ 1 ∧ eval (((24 : ℚ) / (1 + 1260 * x : ℤ)) / scale) (word l) = 1 := by
  have hr : (1 + 1260 * x : ℤ) ≠ 0 := by omega
  have he2 : (18 + 630 * x : ℤ) ≠ 0 := by omega
  have he5 : (3 + 105 * x : ℤ) ≠ 0 := by omega
  exact fiveBlock_unipotent_certificate
    (((24 : ℚ) / (1 + 1260 * x : ℤ)) / scale)
    (scale * (3 * (1 + 1260 * x) * x)) (18 + 630 * x) (scale * (-3))
    (18 * x) (scale * ((1 + 1260 * x) * (3 + 105 * x)))
    ((18 : ℚ) / (1 + 1260 * x : ℤ))
    (mul_ne_zero hs (mul_ne_zero (mul_ne_zero (by norm_num) hr) hx))
    he2 (mul_ne_zero hs (by norm_num)) (mul_ne_zero (by norm_num) hx)
    (mul_ne_zero hs (mul_ne_zero hr he5))
    (simple_direct_scaled_matrix_identity x scale hs)

/-- Unscaled direct construction, with the exact syllable count. -/
theorem simple_direct_certificate (x : ℤ) (hx : x ≠ 0) :
    ∃ l : List Syllable, l.length = 12 ∧ ReducedSyllables l ∧
      word l ≠ 1 ∧ eval ((24 : ℚ) / (1 + 1260 * x : ℤ)) (word l) = 1 := by
  simpa using simple_direct_scaled_certificate x 1 hx (by norm_num)

/-- The branch-free construction gives a relation for every nonzero x. -/
theorem simple_direct_hasRelation (x : ℤ) (hx : x ≠ 0) :
    HasRelation ((24 : ℚ) / (1 + 1260 * x : ℤ)) := by
  obtain ⟨l, _, _, hn, he⟩ := simple_direct_certificate x hx
  exact ⟨word l, hn, he⟩

/-- A residue of 1 modulo 1260 has a unique displayed integral parameter;
excluding r = 1 excludes precisely the zero parameter. -/
theorem simple_direct_residue_parameter (r : ℤ) (hr : r % 1260 = 1) (hr1 : r ≠ 1) :
    ∃ x : ℤ, x ≠ 0 ∧ r = 1 + 1260 * x := by
  exact ⟨r / 1260, by omega, by omega⟩

/-- All four original omitted residues belong to the two branch-free classes. -/
theorem simple_direct_four_residues_sign (r : ℤ)
    (hr : r % 40320 = 1261 ∨ r % 40320 = 6299 ∨
      r % 40320 = 34021 ∨ r % 40320 = 39059) :
    (r % 1260 = 1 ∧ r ≠ 1) ∨ ((-r) % 1260 = 1 ∧ -r ≠ 1) := by
  rcases hr with hr | hr | hr | hr <;> omega

/-- Either nondegenerate signed class has an explicit twelve-syllable relation. -/
theorem simple_direct_signed_residue_certificate (r : ℤ)
    (hr : (r % 1260 = 1 ∧ r ≠ 1) ∨ ((-r) % 1260 = 1 ∧ -r ≠ 1)) :
    ∃ l : List Syllable, l.length = 12 ∧ ReducedSyllables l ∧
      word l ≠ 1 ∧ eval ((24 : ℚ) / r) (word l) = 1 := by
  rcases hr with ⟨hr, hr1⟩ | ⟨hr, hr1⟩
  · obtain ⟨x, hx, hR⟩ := simple_direct_residue_parameter r hr hr1
    rw [hR]
    exact simple_direct_certificate x hx
  · obtain ⟨x, hx, hR⟩ := simple_direct_residue_parameter (-r) hr hr1
    have h := simple_direct_scaled_certificate x (-1) hx (by norm_num)
    rw [← hR] at h
    simpa only [Int.cast_neg, Int.cast_one, div_neg, div_one, neg_neg] using h

/-- The original four omitted residues all have twelve-syllable certificates,
without any valuation, parity, or four-branch parameter construction. -/
theorem simple_direct_four_residues_certificate (r : ℤ)
    (hr : r % 40320 = 1261 ∨ r % 40320 = 6299 ∨
      r % 40320 = 34021 ∨ r % 40320 = 39059) :
    ∃ l : List Syllable, l.length = 12 ∧ ReducedSyllables l ∧
      word l ≠ 1 ∧ eval ((24 : ℚ) / r) (word l) = 1 := by
  exact simple_direct_signed_residue_certificate r (simple_direct_four_residues_sign r hr)

/-- A bounded form with the same conjunction order as the uniform theorem.
It is stated directly, to keep this module independent of the global cover. -/
theorem simple_direct_scaled_bounded (x scale : ℤ) (hx : x ≠ 0) (hs : scale ≠ 0) :
    ∃ l : List Syllable, ReducedSyllables l ∧ l ≠ [] ∧ l.length ≤ 64 ∧
      word l ≠ 1 ∧ eval (((24 : ℚ) / (1 + 1260 * x : ℤ)) / scale) (word l) = 1 := by
  obtain ⟨l, hlen, hred, hn, he⟩ := simple_direct_scaled_certificate x scale hx hs
  refine ⟨l, hred, ?_, by omega, hn, he⟩
  intro hz
  simp [hz] at hlen

/-- The bounded certificate for the four omitted classes; the stronger theorem
above records the exact count of twelve syllables. -/
theorem simple_direct_four_residues_bounded (r : ℤ)
    (hr : r % 40320 = 1261 ∨ r % 40320 = 6299 ∨
      r % 40320 = 34021 ∨ r % 40320 = 39059) :
    ∃ l : List Syllable, ReducedSyllables l ∧ l ≠ [] ∧ l.length ≤ 64 ∧
      word l ≠ 1 ∧ eval ((24 : ℚ) / r) (word l) = 1 := by
  obtain ⟨l, hlen, hred, hn, he⟩ := simple_direct_four_residues_certificate r hr
  refine ⟨l, hred, ?_, by omega, hn, he⟩
  intro hz
  simp [hz] at hlen

/-- A nontrivial relation for each of the four omitted classes. -/
theorem simple_direct_four_residues_hasRelation (r : ℤ)
    (hr : r % 40320 = 1261 ∨ r % 40320 = 6299 ∨
      r % 40320 = 34021 ∨ r % 40320 = 39059) :
    HasRelation ((24 : ℚ) / r) := by
  obtain ⟨l, _, _, hn, he⟩ := simple_direct_four_residues_certificate r hr
  exact ⟨word l, hn, he⟩

end TwentyFour
