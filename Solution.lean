import Challenge
import TwentyFour.Main
import TwentyFour.ComplexVersion
import TwentyFour.Bounded
import TwentyFour.SimpleDirect
import TwentyFour.TwoStep

/-- The complete abstract non-freeness theorem, checked against the independent
Mathlib-only statement in Challenge.lean. -/
theorem twentyfour_not_free : Challenge.MainStatement := by
  intro r hr
  change ¬ IsFreeGroup (TwentyFour.G ((24 : ℚ) / r))
  exact TwentyFour.twentyfour_not_free r hr

/-- The constructive relation conclusion is retained separately for audit. -/
theorem twentyfour_hasRelation : Challenge.RelationStatement := by
  intro r hr
  change ∃ w : FreeGroup Bool, w ≠ 1 ∧ TwentyFour.eval ((24 : ℚ) / r) w = 1
  exact TwentyFour.twentyfour_hasRelation r hr

/-- Every denominator has a nonempty, freely reduced relation with at most
sixty-four generator-power syllables. -/
theorem twentyfour_boundedRelation : Challenge.BoundedStatement := by
  intro r hr
  change TwentyFour.BoundedRelation ((24 : ℚ) / r)
  exact TwentyFour.twentyfour_boundedRelation r hr

/-- The full conclusion for the subgroup of SL(2, ℂ), checked against a separately
written Mathlib-only statement of the actual complex matrices. -/
theorem twentyfour_complex_not_free : Challenge.ComplexMainStatement := by
  intro r hr
  change ¬ IsFreeGroup (TwentyFour.Gcomplex ((24 : ℂ) / r))
  exact TwentyFour.twentyfour_complex_not_free r hr

/-- The explicit cofinite two-step theorem, checked against the independent
triangular-matrix-word specification. -/
theorem twentyfour_twoStep : Challenge.TwoStepStatement := by
  intro r hr
  obtain ⟨es, hn, hl, ht⟩ := TwentyFour.twentyfour_twoStep r hr
  refine ⟨es, hn, hl, ?_⟩
  have he (b : Bool) (xs : List ℤ) :
      Challenge.alternatingSyllables b xs = TwentyFour.syllables b xs := by
    induction xs generalizing b with
    | nil => rfl
    | cons e xs ih => simp only [Challenge.alternatingSyllables, TwentyFour.syllables, ih]
  simpa only [Challenge.alternatingMatrixWord, he, TwentyFour.matWord,
    TwentyFour.matrixWord, TwentyFour.upper, TwentyFour.lower] using ht
