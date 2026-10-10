import Std

/-! The complete finite covering certificate. All closed computations use `decide`,
which constructs proof terms checked by the Lean kernel (no native_decide). -/
namespace TwentyFour
namespace FiniteCover
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
structure Rule where
  w : Nat
  m : Nat
  y : Nat
  D : Nat
  deriving DecidableEq, Repr

def rules : List Rule := [
  ⟨1, 1, 1, 1⟩,
  ⟨2, 1, 1, 2⟩,
  ⟨3, 1, 1, 3⟩,
  ⟨4, 1, 1, 4⟩,
  ⟨5, 1, 1, 1⟩,
  ⟨6, 1, 1, 6⟩,
  ⟨8, 1, 1, 8⟩,
  ⟨9, 1, 1, 3⟩,
  ⟨12, 1, 1, 12⟩,
  ⟨24, 1, 1, 24⟩,
  ⟨7, 2, 1, 1⟩,
  ⟨10, 2, 1, 2⟩,
  ⟨14, 2, 2, 2⟩,
  ⟨7, 3, 3, 1⟩,
  ⟨31, 3, 3, 1⟩,
  ⟨11, 4, 4, 1⟩,
  ⟨35, 4, 4, 1⟩,
  ⟨7, 5, 1, 1⟩,
  ⟨11, 5, 1, 1⟩,
  ⟨17, 5, 1, 1⟩,
  ⟨11, 6, 1, 1⟩,
  ⟨13, 6, 1, 1⟩,
  ⟨17, 6, 2, 1⟩,
  ⟨11, 7, 7, 1⟩,
  ⟨13, 7, 1, 1⟩,
  ⟨35, 7, 1, 7⟩,
  ⟨107, 7, 7, 1⟩,
  ⟨13, 8, 4, 1⟩,
  ⟨59, 8, 4, 1⟩,
  ⟨13, 10, 2, 1⟩,
  ⟨35, 10, 1, 5⟩,
  ⟨37, 10, 2, 1⟩,
  ⟨13, 15, 3, 1⟩,
  ⟨35, 15, 3, 5⟩,
  ⟨83, 15, 3, 1⟩,
  ⟨37, 16, 8, 1⟩,
  ⟨83, 16, 8, 1⟩,
  ⟨59, 30, 5, 1⟩,
  ⟨61, 30, 5, 1⟩,
  ⟨85, 30, 2, 5⟩,
  ⟨37, 84, 2, 1⟩,
  ⟨109, 84, 2, 1⟩,
  ⟨59, 140, 20, 1⟩,
  ⟨1139, 140, 20, 1⟩,
  ⟨83, 280, 28, 1⟩,
  ⟨2267, 280, 28, 1⟩,
  ⟨613, 560, 40, 1⟩,
  ⟨877, 560, 40, 1⟩
]

def Rule.Valid (p : Rule) : Prop :=
  0 < p.w ∧ 0 < p.m ∧ 0 < p.y ∧ 0 < p.D ∧
  p.w ≤ 24 * p.m ∧ p.D = Nat.gcd p.w (24 * p.m) ∧
  p.y * p.D ∣ p.m * Nat.gcd p.w 24 ∧
  (p.w ∣ 24 * p.m * p.y - p.D ∨ p.w ∣ 24 * p.m * p.y + p.D) ∧
  24 * p.m ∣ 40320
instance (p : Rule) : Decidable p.Valid := inferInstanceAs (Decidable (_ ∧ _))

def Rule.covers (p : Rule) (a : Nat) : Bool :=
  a % (24 * p.m) == p.w % (24 * p.m) ||
  a % (24 * p.m) == (24 * p.m - p.w) % (24 * p.m)

def covered (a : Nat) : Bool := rules.any (fun p => p.covers a)

def omitted : List Nat := [1261, 6299, 34021, 39059]

def exceptionValues : List Nat :=
  [7, 8, 9, 10, 11, 12, 13, 14, 17, 24, 31, 35, 37, 59,
   61, 83, 85, 107, 109, 613, 877, 1139, 2267]

theorem rules_length : rules.length = 48 := by decide

theorem rules_valid : ∀ p ∈ rules, p.Valid := by
  decide

def coverageCheck (a : Nat) : Bool := covered a == !(omitted.contains a)

def coverageBlock (b : Nat) : Bool :=
  (List.range 1008).all (fun k => coverageCheck (b * 1008 + k))

theorem coverage_block_0 : coverageBlock 0 = true := by decide
theorem coverage_block_1 : coverageBlock 1 = true := by decide
theorem coverage_block_2 : coverageBlock 2 = true := by decide
theorem coverage_block_3 : coverageBlock 3 = true := by decide
theorem coverage_block_4 : coverageBlock 4 = true := by decide
theorem coverage_block_5 : coverageBlock 5 = true := by decide
theorem coverage_block_6 : coverageBlock 6 = true := by decide
theorem coverage_block_7 : coverageBlock 7 = true := by decide
theorem coverage_block_8 : coverageBlock 8 = true := by decide
theorem coverage_block_9 : coverageBlock 9 = true := by decide
theorem coverage_block_10 : coverageBlock 10 = true := by decide
theorem coverage_block_11 : coverageBlock 11 = true := by decide
theorem coverage_block_12 : coverageBlock 12 = true := by decide
theorem coverage_block_13 : coverageBlock 13 = true := by decide
theorem coverage_block_14 : coverageBlock 14 = true := by decide
theorem coverage_block_15 : coverageBlock 15 = true := by decide
theorem coverage_block_16 : coverageBlock 16 = true := by decide
theorem coverage_block_17 : coverageBlock 17 = true := by decide
theorem coverage_block_18 : coverageBlock 18 = true := by decide
theorem coverage_block_19 : coverageBlock 19 = true := by decide
theorem coverage_block_20 : coverageBlock 20 = true := by decide
theorem coverage_block_21 : coverageBlock 21 = true := by decide
theorem coverage_block_22 : coverageBlock 22 = true := by decide
theorem coverage_block_23 : coverageBlock 23 = true := by decide
theorem coverage_block_24 : coverageBlock 24 = true := by decide
theorem coverage_block_25 : coverageBlock 25 = true := by decide
theorem coverage_block_26 : coverageBlock 26 = true := by decide
theorem coverage_block_27 : coverageBlock 27 = true := by decide
theorem coverage_block_28 : coverageBlock 28 = true := by decide
theorem coverage_block_29 : coverageBlock 29 = true := by decide
theorem coverage_block_30 : coverageBlock 30 = true := by decide
theorem coverage_block_31 : coverageBlock 31 = true := by decide
theorem coverage_block_32 : coverageBlock 32 = true := by decide
theorem coverage_block_33 : coverageBlock 33 = true := by decide
theorem coverage_block_34 : coverageBlock 34 = true := by decide
theorem coverage_block_35 : coverageBlock 35 = true := by decide
theorem coverage_block_36 : coverageBlock 36 = true := by decide
theorem coverage_block_37 : coverageBlock 37 = true := by decide
theorem coverage_block_38 : coverageBlock 38 = true := by decide
theorem coverage_block_39 : coverageBlock 39 = true := by decide

theorem coverage_blocks (b : Nat) (hb : b < 40) : coverageBlock b = true := by
  by_cases h : b = 0
  · simpa only [h] using coverage_block_0
  by_cases h : b = 1
  · simpa only [h] using coverage_block_1
  by_cases h : b = 2
  · simpa only [h] using coverage_block_2
  by_cases h : b = 3
  · simpa only [h] using coverage_block_3
  by_cases h : b = 4
  · simpa only [h] using coverage_block_4
  by_cases h : b = 5
  · simpa only [h] using coverage_block_5
  by_cases h : b = 6
  · simpa only [h] using coverage_block_6
  by_cases h : b = 7
  · simpa only [h] using coverage_block_7
  by_cases h : b = 8
  · simpa only [h] using coverage_block_8
  by_cases h : b = 9
  · simpa only [h] using coverage_block_9
  by_cases h : b = 10
  · simpa only [h] using coverage_block_10
  by_cases h : b = 11
  · simpa only [h] using coverage_block_11
  by_cases h : b = 12
  · simpa only [h] using coverage_block_12
  by_cases h : b = 13
  · simpa only [h] using coverage_block_13
  by_cases h : b = 14
  · simpa only [h] using coverage_block_14
  by_cases h : b = 15
  · simpa only [h] using coverage_block_15
  by_cases h : b = 16
  · simpa only [h] using coverage_block_16
  by_cases h : b = 17
  · simpa only [h] using coverage_block_17
  by_cases h : b = 18
  · simpa only [h] using coverage_block_18
  by_cases h : b = 19
  · simpa only [h] using coverage_block_19
  by_cases h : b = 20
  · simpa only [h] using coverage_block_20
  by_cases h : b = 21
  · simpa only [h] using coverage_block_21
  by_cases h : b = 22
  · simpa only [h] using coverage_block_22
  by_cases h : b = 23
  · simpa only [h] using coverage_block_23
  by_cases h : b = 24
  · simpa only [h] using coverage_block_24
  by_cases h : b = 25
  · simpa only [h] using coverage_block_25
  by_cases h : b = 26
  · simpa only [h] using coverage_block_26
  by_cases h : b = 27
  · simpa only [h] using coverage_block_27
  by_cases h : b = 28
  · simpa only [h] using coverage_block_28
  by_cases h : b = 29
  · simpa only [h] using coverage_block_29
  by_cases h : b = 30
  · simpa only [h] using coverage_block_30
  by_cases h : b = 31
  · simpa only [h] using coverage_block_31
  by_cases h : b = 32
  · simpa only [h] using coverage_block_32
  by_cases h : b = 33
  · simpa only [h] using coverage_block_33
  by_cases h : b = 34
  · simpa only [h] using coverage_block_34
  by_cases h : b = 35
  · simpa only [h] using coverage_block_35
  by_cases h : b = 36
  · simpa only [h] using coverage_block_36
  by_cases h : b = 37
  · simpa only [h] using coverage_block_37
  by_cases h : b = 38
  · simpa only [h] using coverage_block_38
  by_cases h : b = 39
  · simpa only [h] using coverage_block_39
  omega

theorem coverage_check (a : Nat) (ha : a < 40320) : coverageCheck a = true := by
  have hb : a / 1008 < 40 := by omega
  have hk : a % 1008 < 1008 := Nat.mod_lt _ (by decide)
  have hh := (List.all_eq_true.mp (coverage_blocks (a / 1008) hb))
    (a % 1008) (List.mem_range.mpr hk)
  have he : a / 1008 * 1008 + a % 1008 = a := by omega
  simpa only [he] using hh

theorem cover_remainder (a : Nat) (ha : a < 40320) :
    covered a = true ↔ a ∉ omitted := by
  have h := coverage_check a ha
  unfold coverageCheck at h
  cases h₁ : covered a <;> cases h₂ : omitted.contains a <;> simp_all

theorem rule_bound : ∀ p ∈ rules, p.D ≤ 24 * p.m * p.y := by decide

theorem exception_values_cover : ∀ p ∈ rules,
    (6 < p.w → p.w ∈ exceptionValues) ∧
    (6 < p.D → p.D ∈ exceptionValues) := by decide

theorem omitted_branches : ∀ a ∈ omitted,
    a % 2520 = 1261 ∨ a % 2520 = 1259 := by decide

theorem covered_iff (a : Nat) :
    covered a = true ↔ ∃ p ∈ rules, p.covers a = true := by
  simp only [covered, List.any_eq_true]

theorem rule_modulus_dvd (p : Rule) (hp : p ∈ rules) : 24 * p.m ∣ 40320 :=
  (rules_valid p hp).2.2.2.2.2.2.2.2

theorem rule_covers_mod (p : Rule) (hp : p ∈ rules) (a : Nat) :
    p.covers (a % 40320) = p.covers a := by
  simp only [Rule.covers, Nat.mod_mod_of_dvd a (rule_modulus_dvd p hp)]

theorem covered_mod (a : Nat) : covered (a % 40320) = covered a := by
  apply Bool.eq_iff_iff.mpr
  rw [covered_iff, covered_iff]
  constructor
  · rintro ⟨p, hp, hc⟩
    exact ⟨p, hp, (rule_covers_mod p hp a) ▸ hc⟩
  · rintro ⟨p, hp, hc⟩
    exact ⟨p, hp, (rule_covers_mod p hp a).symm ▸ hc⟩

#print axioms rules_valid
#print axioms cover_remainder
end FiniteCover
end TwentyFour
