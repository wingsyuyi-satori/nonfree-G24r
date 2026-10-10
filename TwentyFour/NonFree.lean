import TwentyFour.Core
import TwentyFour.FreeGroupHopf
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

namespace TwentyFour

/-- A free group on at most one generator is commutative. -/
theorem freeGroup_commute_of_subsingleton {α : Type*} [Subsingleton α]
    (x y : FreeGroup α) : Commute x y := by
  have hg (a : α) (z : FreeGroup α) : Commute (FreeGroup.of a) z := by
    induction z using FreeGroup.induction_on with
    | C1 => exact Commute.one_right _
    | of b => simpa only [Subsingleton.elim b a] using Commute.refl (FreeGroup.of a)
    | inv_of b ih => exact ih.inv_right
    | mul z t ihz iht => exact ihz.mul_right iht
  induction x using FreeGroup.induction_on with
  | C1 => exact Commute.one_left _
  | of a => exact hg a y
  | inv_of a ih => exact ih.inv_left
  | mul z t ihz iht => exact ihz.mul_left iht

/-- Every noncommutative abstract free group surjects onto the rank-two free group. -/
theorem freeGroup_surjects_rankTwo {H : Type*} [Group H] [IsFreeGroup H]
    (x y : H) (hxy : x * y ≠ y * x) :
    ∃ f : H →* FreeGroup Bool, Function.Surjective f := by
  classical
  let α := IsFreeGroup.Generators H
  let e : H ≃* FreeGroup α := IsFreeGroup.toFreeGroup H
  have hn : Nontrivial α := by
    by_contra hn
    haveI : Subsingleton α := not_nontrivial_iff_subsingleton.mp hn
    apply hxy
    apply e.injective
    simpa only [map_mul] using (freeGroup_commute_of_subsingleton (e x) (e y)).eq
  letI := hn
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  let r : α → Bool := fun c => decide (c = b)
  let s : Bool → α := fun c => if c then b else a
  have hrs (c : Bool) : r (s c) = c := by
    cases c <;> simp [r, s, hab]
  have he : (FreeGroup.map r).comp (FreeGroup.map s) = MonoidHom.id (FreeGroup Bool) := by
    apply FreeGroup.ext_hom
    intro c
    simp [hrs]
  have hr : Function.Surjective (FreeGroup.map r) := by
    intro w
    exact ⟨FreeGroup.map s w, DFunLike.congr_fun he w⟩
  refine ⟨(FreeGroup.map r).comp e.toMonoidHom, hr.comp e.surjective⟩

/-- A noncommutative abstract free group cannot be a proper quotient of a rank-two free group. -/
theorem twoGenerator_free_injective {H : Type*} [Group H] [IsFreeGroup H]
    (x y : H) (hxy : x * y ≠ y * x)
    (f : FreeGroup Bool →* H) (hf : Function.Surjective f) : Function.Injective f := by
  obtain ⟨g, hg⟩ := freeGroup_surjects_rankTwo x y hxy
  have hi := freeGroup_hopf (g.comp f) (hg.comp hf)
  intro a b hab
  apply hi
  exact congrArg g hab

/-- A nonzero parameter with a nontrivial relation gives a group which is not abstractly free. -/
theorem hasRelation_not_isFreeGroup {q : ℚ} (hq : q ≠ 0) (hr : HasRelation q) :
    ¬ IsFreeGroup (G q) := by
  intro hfree
  letI := hfree
  let a : G q := ⟨A, Subgroup.subset_closure (by simp)⟩
  let b : G q := ⟨B q, Subgroup.subset_closure (by simp)⟩
  have hab : a * b ≠ b * a := by
    intro he
    exact generators_noncommute q hq (congrArg Subtype.val he)
  let f : FreeGroup Bool →* G q := (eval q).codRestrict (G q) (by
    intro w
    rw [← range_eval q]
    exact ⟨w, rfl⟩)
  have hf : Function.Surjective f := by
    intro z
    have hz : (z : SL2) ∈ (eval q).range := by rw [range_eval]; exact z.2
    obtain ⟨w, hw⟩ := hz
    exact ⟨w, Subtype.ext hw⟩
  have hi := twoGenerator_free_injective a b hab f hf
  apply hasRelation_not_injective hr
  intro x y hxy
  apply hi
  exact Subtype.ext hxy

/-- An equivalent formulation excluding a free-group isomorphism over any generator type. -/
theorem hasRelation_no_freeGroup_equiv {q : ℚ} (hq : q ≠ 0) (hr : HasRelation q)
    (ι : Type*) : ¬ Nonempty (G q ≃* FreeGroup ι) := by
  rintro ⟨e⟩
  exact hasRelation_not_isFreeGroup hq hr (FreeGroupBasis.isFreeGroup ⟨e⟩)

end TwentyFour
