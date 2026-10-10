import TwentyFour.SimpleDirect
import TwentyFour.CoverRelations
import TwentyFour.FiniteWords
import TwentyFour.NonFree

namespace TwentyFour

/-- The explicitly checked exceptions also work for negative denominators. -/
theorem signed_exception_hasRelation (r : ℤ) (hr : r.natAbs ∈ FiniteCover.exceptionValues) :
    HasRelation ((24 : ℚ) / r) := by
  have h := FiniteWords.exception_hasRelation r.natAbs hr
  by_cases hs : 0 ≤ r
  · have hc : (r.natAbs : ℚ) = (r : ℚ) := by
      simpa only [Int.cast_natCast] using
        congrArg (fun z : ℤ => (z : ℚ)) (Int.natAbs_of_nonneg hs)
    simpa only [hc] using h
  · have hc : (r.natAbs : ℚ) = -(r : ℚ) := by
      simpa only [Int.cast_natCast, Int.cast_neg] using
        congrArg (fun z : ℤ => (z : ℚ)) (Int.ofNat_natAbs_of_nonpos (by omega : r ≤ 0))
    apply hasRelation_neg
    simpa only [hc, div_neg] using h

/-- The four finite omitted residues are the hypotheses of the infinite direct family. -/
theorem omitted_hasRelation (r : ℤ) (hr : (r % 40320).toNat ∈ FiniteCover.omitted) :
    HasRelation ((24 : ℚ) / r) := by
  have hm : 0 ≤ r % 40320 := Int.emod_nonneg r (by norm_num)
  have hh : (r % 40320).toNat = 1261 ∨ (r % 40320).toNat = 6299 ∨
      (r % 40320).toNat = 34021 ∨ (r % 40320).toNat = 39059 := by
    simpa [FiniteCover.omitted] using hr
  have hfour : r % 40320 = 1261 ∨ r % 40320 = 6299 ∨
      r % 40320 = 34021 ∨ r % 40320 = 39059 := by
    rcases hh with h | h | h | h <;> omega
  obtain ⟨l, _, _, hn, he⟩ := simple_direct_four_residues_certificate r hfour
  exact ⟨word l, hn, he⟩

/-- Every integer denominator of absolute value greater than six yields a genuine,
nontrivial element in the kernel of the canonical free-group evaluation map. -/
theorem twentyfour_hasRelation_natAbs (r : ℤ) (hr : 6 < r.natAbs) :
    HasRelation ((24 : ℚ) / r) := by
  by_cases he : r.natAbs ∈ FiniteCover.exceptionValues
  · exact signed_exception_hasRelation r he
  by_cases hb : (r % 40320).toNat ∈ FiniteCover.omitted
  · exact omitted_hasRelation r hb
  exact FiniteCover.outside_omitted_hasRelation r hr he hb

/-- The main all-integer theorem, in the usual absolute-value formulation. -/
theorem twentyfour_hasRelation (r : ℤ) (hr : 6 < |r|) :
    ∃ w : FreeGroup Bool, w ≠ 1 ∧ eval ((24 : ℚ) / r) w = 1 := by
  apply twentyfour_hasRelation_natAbs r
  have h : (6 : ℤ) < (r.natAbs : ℤ) := by simpa only [Int.natCast_natAbs] using hr
  exact_mod_cast h

/-- Thus these two displayed matrices never form a free generating pair. -/
theorem twentyfour_evaluation_not_injective (r : ℤ) (hr : 6 < |r|) :
    ¬ Function.Injective (eval ((24 : ℚ) / r)) :=
  hasRelation_not_injective (twentyfour_hasRelation r hr)

/-- The full abstract non-freeness conclusion, not merely failure of the given
pair to be a free basis. -/
theorem twentyfour_not_free (r : ℤ) (hr : 6 < |r|) :
    ¬ IsFreeGroup (G ((24 : ℚ) / r)) := by
  apply hasRelation_not_isFreeGroup
  · exact div_ne_zero (by norm_num) (by exact_mod_cast (show r ≠ 0 by intro h; simp [h] at hr))
  · exact twentyfour_hasRelation r hr

theorem twentyfour_not_free_natAbs (r : ℤ) (hr : 6 < r.natAbs) :
    ¬ IsFreeGroup (G ((24 : ℚ) / r)) := by
  apply twentyfour_not_free r
  have h : (6 : ℤ) < (r.natAbs : ℤ) := by exact_mod_cast hr
  simpa only [Int.natCast_natAbs] using h

#print axioms twentyfour_not_free
#print axioms twentyfour_hasRelation
#print axioms twentyfour_evaluation_not_injective

end TwentyFour
