import TwentyFour.FiniteCover
import Mathlib.Tactic
import Mathlib.Data.Int.ModEq

namespace TwentyFour
namespace FiniteCover

/-- The same finite arithmetic data, cast to integers without truncated subtraction. -/
def Rule.IntValid (p : Rule) : Prop :=
  (p.w : ℤ) ≠ 0 ∧ (p.m : ℤ) ≠ 0 ∧ (p.y : ℤ) ≠ 0 ∧
  Int.gcd (p.w : ℤ) (24 * p.m) = p.D ∧
  (p.y : ℤ) * p.D ∣ (p.m : ℤ) * (Int.gcd (p.w : ℤ) 24 : ℤ) ∧
  ((p.w : ℤ) ∣ 24 * (p.m : ℤ) * p.y - p.D ∨
   (p.w : ℤ) ∣ 24 * (p.m : ℤ) * p.y + p.D) ∧
  (24 * (p.m : ℤ) ∣ 40320) ∧ p.w ≤ 24 * p.m ∧
  (6 < p.w → p.w ∈ exceptionValues) ∧
  (6 < p.D → p.D ∈ exceptionValues)

instance (p : Rule) : Decidable p.IntValid := inferInstanceAs (Decidable (_ ∧ _))

theorem rules_int_valid : ∀ p ∈ rules, p.IntValid := by decide

/-- A complete finite residue certificate gives an integer divisibility branch,
for unbounded positive or negative integers. -/
theorem integer_cover (r : ℤ) (hbad : (r % 40320).toNat ∉ omitted) :
    ∃ p ∈ rules, 24 * (p.m : ℤ) ∣ r - p.w ∨ 24 * (p.m : ℤ) ∣ r + p.w := by
  let a := (r % 40320).toNat
  have hn : 0 ≤ r % 40320 := Int.emod_nonneg r (by norm_num)
  have ha : a < 40320 := by
    have hh := Int.emod_lt_of_pos r (by norm_num : (0:ℤ) < 40320)
    omega
  have hc : covered a = true := (cover_remainder a ha).mpr hbad
  obtain ⟨p, hp, hpc⟩ := List.any_eq_true.mp hc
  refine ⟨p, hp, ?_⟩
  have hi := rules_int_valid p hp
  rcases hi with ⟨_, _, _, _, _, _, hdiv, hwle, _, _⟩
  have hac : (a : ℤ) = r % 40320 := Int.toNat_of_nonneg hn
  simp only [Rule.covers, Bool.or_eq_true, beq_iff_eq] at hpc
  rcases hpc with hpos | hneg
  · left
    have he := congrArg (fun n : ℕ => (n : ℤ)) hpos
    simp only [Int.natCast_mod, Int.natCast_mul, Nat.cast_ofNat] at he
    rw [hac, Int.emod_emod_of_dvd r hdiv] at he
    exact Int.ModEq.dvd he.symm
  · right
    have he := congrArg (fun n : ℕ => (n : ℤ)) hneg
    simp only [Int.natCast_mod, Int.natCast_sub hwle, Int.natCast_mul, Nat.cast_ofNat] at he
    rw [hac, Int.emod_emod_of_dvd r hdiv] at he
    have hd : 24 * (p.m : ℤ) ∣ r - (24 * (p.m : ℤ) - p.w) := Int.ModEq.dvd he.symm
    convert dvd_add hd (dvd_refl (24 * (p.m : ℤ))) using 1 <;> ring

#print axioms rules_int_valid
#print axioms integer_cover
end FiniteCover
end TwentyFour
