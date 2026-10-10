import TwentyFour.Core
import TwentyFour.ParametricArithmetic

namespace TwentyFour

/-- Exact universal five-block matrix identity. All variables here are arbitrary
rationals satisfying the three displayed algebraic equations. -/
theorem five_block_identity (s r m y u t e k : ℚ) (hr : r ≠ 0)
    (hm : m = k * y) (he : e = y - u * t)
    (hunit : r * u + s * m * e = 1) :
    upper ((r * y) * (s / r)) * lower (-k * e) *
      upper ((-t) * (s / r)) * lower m * upper ((-r * e) * (s / r)) =
      lower (k * t / r) := by
  have h1 : (r * y) * (s / r) = s * y := by field_simp [hr]
  have h5 : (-r * e) * (s / r) = -s * e := by field_simp [hr]
  rw [h1, h5]
  have hfirst : upper (s * y) * lower (-k * e) = !![r * u, s * y; -k * e, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper, lower, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hm] at hunit
    linear_combination -hunit
  rw [hfirst]
  have hthree : !![r * u, s * y; -k * e, 1] * upper ((-t) * (s / r)) =
      !![r * u, s * e; -k * e, 1 + s * k * e * t / r] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper, Matrix.mul_apply, Fin.sum_univ_two]
    · rw [he]
      field_simp [hr]
      ring
    · ring
  rw [hthree]
  have hK : m * r - k * e * r + s * k * m * e * t = k * t := by
    calc
      m * r - k * e * r + s * k * m * e * t =
          k * t * (r * u + s * m * e) := by rw [he, hm]; ring
      _ = k * t := by rw [hunit]; ring
  have hfour : !![r * u, s * e; -k * e, 1 + s * k * e * t / r] * lower m =
      !![1, s * e; k * t / r, 1 + s * k * e * t / r] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lower, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination hunit
    · field_simp [hr]
      linear_combination hK
  rw [hfour]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper, lower, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Integer-scaled version, so substitution B ↦ B^scale requires no
unproved free-group injectivity assertion. -/
theorem five_block_identity_scaled (s r m y u t e k scale : ℤ)
    (hr : r ≠ 0) (hscale : scale ≠ 0)
    (hm : m = k * y) (he : e = y - u * t)
    (hunit : r * u + s * m * e = 1) :
    let q : ℚ := ((s : ℚ) / r) / scale
    upper (((scale * (r * y) : ℤ) : ℚ) * q) * lower ((-k * e : ℤ) : ℚ) *
      upper (((scale * (-t) : ℤ) : ℚ) * q) * lower (m : ℚ) *
      upper (((scale * (-r * e) : ℤ) : ℚ) * q) = lower ((k : ℚ) * t / r) := by
  have hrq : (r : ℚ) ≠ 0 := by exact_mod_cast hr
  have hscaleq : (scale : ℚ) ≠ 0 := by exact_mod_cast hscale
  have hmq : (m : ℚ) = (k : ℚ) * y := by exact_mod_cast hm
  have heq : (e : ℚ) = (y : ℚ) - u * t := by exact_mod_cast he
  have huq : (r : ℚ) * u + s * m * e = 1 := by exact_mod_cast hunit
  dsimp
  push_cast
  have hcancel (a : ℚ) : (scale : ℚ) * a * ((s : ℚ) / r / scale) = a * ((s : ℚ) / r) := by
    field_simp [hrq, hscaleq]
  rw [hcancel, hcancel, hcancel]
  exact five_block_identity s r m y u t e k hrq hmq heq huq

/-- Every integer instance of the generic template gives a nontrivial relation.
The five powers are certified nonzero here, rather than checked by sampling. -/
theorem generic_fiveBlock_scaled (s r m y u t e k scale : ℤ)
    (hr : r ≠ 0) (hscale : scale ≠ 0)
    (hm : m = k * y) (he : e = y - u * t)
    (hunit : r * u + s * m * e = 1)
    (hm0 : m ≠ 0) (hy0 : y ≠ 0) (ht0 : t ≠ 0) (he0 : e ≠ 0) :
    HasRelation (((s : ℚ) / r) / scale) := by
  have hk0 : k ≠ 0 := by intro hk; simp [hk] at hm; exact hm0 hm
  apply fiveBlock_hasRelation (((s : ℚ) / r) / scale)
    (scale * (r * y)) (-k * e) (scale * (-t)) m (scale * (-r * e))
  · exact mul_ne_zero hscale (mul_ne_zero hr hy0)
  · exact mul_ne_zero (neg_ne_zero.mpr hk0) he0
  · exact mul_ne_zero hscale (neg_ne_zero.mpr ht0)
  · exact hm0
  · exact mul_ne_zero hscale (mul_ne_zero (neg_ne_zero.mpr hr) he0)
  · have hmatrix := five_block_identity_scaled s r m y u t e k scale hr hscale hm he hunit
    have hentry := congrArg (fun M : M2 => M 0 1) hmatrix
    simpa [lower] using hentry

/-- The D=1 good-class lemma, including the harmless case u=0. -/
theorem good_basic_scaled (s r w m y t u scale : ℤ)
    (hr : r = w + s * m * t) (hunit : w * u + s * m * y = 1)
    (hym : y ∣ m) (hm : m ≠ 0) (hy : y ≠ 0) (ht : t ≠ 0)
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hrn1 : r ≠ -1) (hscale : scale ≠ 0) :
    HasRelation (((s : ℚ) / r) / scale) := by
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
  exact generic_fiveBlock_scaled s r m y u t e k scale hr0 hscale hmk rfl hue hm hy ht he0

theorem good_basic (s r w m y t u : ℤ)
    (hr : r = w + s * m * t) (hunit : w * u + s * m * y = 1)
    (hym : y ∣ m) (hm : m ≠ 0) (hy : y ≠ 0) (ht : t ≠ 0)
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hrn1 : r ≠ -1) :
    HasRelation ((s : ℚ) / r) := by
  simpa using good_basic_scaled s r w m y t u 1 hr hunit hym hm hy ht hr0 hr1 hrn1 (by norm_num)

/-- The direct construction for every odd integer x. -/
theorem direct_odd_hasRelation (x : ℤ) (hx : x % 2 = 1) :
    HasRelation ((24 : ℚ) / (1 + 1260 * x : ℤ)) := by
  obtain ⟨m, y, u, t, d, hmy, hd, hu, hm0, hy0, ht0, hd0, hR0⟩ := direct_parameters x hx
  simpa using generic_fiveBlock_scaled 24 (1 + 1260 * x) m y u t d 6 1
    hR0 (by norm_num) hmy hd hu hm0 hy0 ht0 hd0

/-- Both signs of the direct construction, by multiplying all B-exponents by -1. -/
theorem direct_odd_signed_hasRelation (x scale : ℤ) (hx : x % 2 = 1) (hs : scale ≠ 0) :
    HasRelation (((24 : ℚ) / (1 + 1260 * x : ℤ)) / scale) := by
  obtain ⟨m, y, u, t, d, hmy, hd, hu, hm0, hy0, ht0, hd0, hR0⟩ := direct_parameters x hx
  exact generic_fiveBlock_scaled 24 (1 + 1260 * x) m y u t d 6 scale
    hR0 hs hmy hd hu hm0 hy0 ht0 hd0

/-- The four actual uncovered residue classes, for arbitrary integer r. -/
theorem four_residues_hasRelation (r : ℤ)
    (hr : r % 40320 = 1261 ∨ r % 40320 = 6299 ∨
      r % 40320 = 34021 ∨ r % 40320 = 39059) :
    HasRelation ((24 : ℚ) / r) := by
  rcases four_residues_sign r hr with h | h
  · obtain ⟨x, hx, hR⟩ := residue_1261_odd r h
    rw [hR]
    exact direct_odd_hasRelation x hx
  · obtain ⟨x, hx, hR⟩ := residue_1261_odd (-r) h
    have hrel := direct_odd_signed_hasRelation x (-1) hx (by norm_num)
    rw [← hR] at hrel
    simpa only [Int.cast_neg, Int.cast_one, div_neg, div_one, neg_neg] using hrel

end TwentyFour
