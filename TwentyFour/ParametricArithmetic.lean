import Mathlib.RingTheory.Multiplicity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace TwentyFour

/-- The finite 3-adic factorization exists for every nonzero integer, including
negative integers. The exponent is mathlib's multiplicity, not a sample bound. -/
theorem three_factor (x : ℤ) (hx : x ≠ 0) :
    ∃ h : ℤ, x = (3 : ℤ) ^ multiplicity 3 x * h ∧ ¬ (3 : ℤ) ∣ h := by
  apply FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd
  exact Int.finiteMultiplicity_iff.mpr ⟨by norm_num, hx⟩

/-- The four possible units modulo 12, with an integral reciprocal factor of 35. -/
theorem four_branch (h : ℤ) (hodd : h % 2 = 1) (hthree : ¬ (3 : ℤ) ∣ h) :
    ∃ c p k : ℤ,
      (c = 1 ∨ c = -1 ∨ c = 5 ∨ c = -5) ∧
      h = 12 * p + c ∧ c * k = 35 := by
  have hmod : h % 3 ≠ 0 := by simpa [Int.dvd_iff_emod_eq_zero] using hthree
  have hc : h % 12 = 1 ∨ h % 12 = 11 ∨ h % 12 = 5 ∨ h % 12 = 7 := by omega
  rcases hc with hc | hc | hc | hc
  · exact ⟨1, h / 12, 35, Or.inl rfl, by omega, by norm_num⟩
  · exact ⟨-1, h / 12 + 1, -35, Or.inr (Or.inl rfl), by omega, by norm_num⟩
  · exact ⟨5, h / 12, 7, Or.inr (Or.inr (Or.inl rfl)), by omega, by norm_num⟩
  · exact ⟨-5, h / 12 + 1, -7, Or.inr (Or.inr (Or.inr rfl)), by omega, by norm_num⟩

/-- The integral branch parameter is precisely the quotient in the paper. -/
theorem branch_t_formula (h c p k : ℤ) (hc : c ≠ 0)
    (hh : h = 12 * p + c) (hk : c * k = 35) :
    (35 * h + c) / (12 * c) = k * p + 3 := by
  apply Int.ediv_eq_of_eq_mul_right (mul_ne_zero (by norm_num) hc)
  rw [hh]
  linear_combination -12 * p * hk

/-- The branch construction covers every odd integer, with no upper bound on
its 3-adic valuation. -/
theorem odd_three_branch (x : ℤ) (hx : x % 2 = 1) :
    ∃ h c p k : ℤ,
      x = (3 : ℤ) ^ multiplicity 3 x * h ∧
      ¬ (3 : ℤ) ∣ h ∧ h % 2 = 1 ∧
      (c = 1 ∨ c = -1 ∨ c = 5 ∨ c = -5) ∧
      h = 12 * p + c ∧ c * k = 35 := by
  have hx0 : x ≠ 0 := by omega
  obtain ⟨h, hfac, hthree⟩ := three_factor x hx0
  have hpows : ∀ i : ℕ, (3 : ℤ) ^ i % 2 = 1 := by
    intro i
    induction i with
    | zero => norm_num
    | succ i ih => rw [pow_succ, Int.mul_emod, ih]; norm_num
  have hpow := hpows (multiplicity 3 x)
  have hodd : h % 2 = 1 := by
    rw [hfac, Int.mul_emod, hpow] at hx
    simpa using hx
  obtain ⟨c, p, k, hc, hh, hk⟩ := four_branch h hodd hthree
  exact ⟨h, c, p, k, hfac, hthree, hodd, hc, hh, hk⟩

/-- The exact five integral parameters used by the direct four-branch rule. -/
theorem direct_parameters (x : ℤ) (hx : x % 2 = 1) :
    ∃ m y u t d : ℤ,
      m = 6 * y ∧ d = y - u * t ∧
      (1 + 1260 * x) * u + 24 * m * d = 1 ∧
      m ≠ 0 ∧ y ≠ 0 ∧ t ≠ 0 ∧ d ≠ 0 ∧ (1 + 1260 * x) ≠ 0 := by
  obtain ⟨h, c, p, k, hfac, hthree, hodd, hc, hh, hck⟩ := odd_three_branch x hx
  let z : ℤ := (3 : ℤ) ^ multiplicity 3 x
  let m : ℤ := 18 * c * z
  let y : ℤ := 3 * c * z
  let u : ℤ := 1 + 2 * m
  let t : ℤ := k * p + 3
  let d : ℤ := y - u * t
  have hc0 : c ≠ 0 := by rcases hc with rfl | rfl | rfl | rfl <;> norm_num
  have hz0 : z ≠ 0 := pow_ne_zero _ (by norm_num)
  have hm0 : m ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hc0) hz0
  have hy0 : y ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hc0) hz0
  have hmy : m = 6 * y := by dsimp [m, y]; ring
  have ht : 12 * c * t = 35 * h + c := by
    dsimp [t]
    rw [hh]
    linear_combination 12 * p * hck
  have ht0 : t ≠ 0 := by
    intro ht0
    rw [ht0] at ht
    rcases hc with rfl | rfl | rfl | rfl <;> omega
  have hR : 1 + 1260 * x = 1 - 2 * m + 24 * m * t := by
    dsimp [m, z]
    conv_lhs => rw [hfac]
    linear_combination -36 * (3 : ℤ) ^ multiplicity 3 x * ht
  have hunit : (1 + 1260 * x) * u + 24 * m * d = 1 := by
    rw [hR]
    dsimp [d, u]
    rw [hmy]
    ring
  have hx0 : x ≠ 0 := by omega
  have hR0 : 1 + 1260 * x ≠ 0 := by omega
  have hR1 : 1 + 1260 * x ≠ 1 := by omega
  have hRn1 : 1 + 1260 * x ≠ -1 := by omega
  have hd0 : d ≠ 0 := by
    intro hd0
    rw [hd0, mul_zero, add_zero] at hunit
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hunit with h1 | hn1
    · exact hR1 h1
    · exact hRn1 hn1
  exact ⟨m, y, u, t, d, hmy, rfl, hunit, hm0, hy0, ht0, hd0, hR0⟩

/-- The positive-sign bad residue is exactly the odd-x family. -/
theorem residue_1261_odd (r : ℤ) (hr : r % 2520 = 1261) :
    ∃ x : ℤ, x % 2 = 1 ∧ r = 1 + 1260 * x := by
  refine ⟨2 * (r / 2520) + 1, ?_, ?_⟩ <;> omega

/-- All four uncovered residues reduce to one of the two signs. -/
theorem four_residues_sign (r : ℤ)
    (hr : r % 40320 = 1261 ∨ r % 40320 = 6299 ∨
      r % 40320 = 34021 ∨ r % 40320 = 39059) :
    r % 2520 = 1261 ∨ (-r) % 2520 = 1261 := by
  rcases hr with hr | hr | hr | hr <;> omega

end TwentyFour
