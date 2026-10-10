import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic

/-!
# Finite permutation models and the Hopf property for free groups

A word is detected by a finite permutation representation on its suffix products.
Each generator acts by extending its partially defined left multiplication on that set.
For a finite generating type, precomposition by a surjective endomorphism permutes the
finite set of homomorphisms to any fixed finite group. Residual finiteness then forces
that endomorphism to be injective.
-/

universe u

namespace TwentyFour
namespace FiniteModel

noncomputable section
open Classical

variable {H : Type*} [Group H]

/-- Left multiplication, restricted to the portion of a finite set on which it stays in the set. -/
def partialMul (S : Finset H) (g : H) :
    {x : S // g * (x : H) ∈ S} ≃ {x : S // g⁻¹ * (x : H) ∈ S} where
  toFun x := ⟨⟨g * x.1, x.2⟩, by simpa using x.1.2⟩
  invFun x := ⟨⟨g⁻¹ * x.1, x.2⟩, by simpa using x.1.2⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; apply Subtype.ext; simp

/-- A permutation agreeing with left multiplication wherever both endpoints are in the set. -/
def perm (S : Finset H) (g : H) : Equiv.Perm S := (partialMul S g).extendSubtype

lemma perm_apply (S : Finset H) (g : H) (x : S) (hx : g * (x : H) ∈ S) :
    ((perm S g x : S) : H) = g * x := by
  change ((partialMul S g).extendSubtype x).val = g * x
  exact congrArg Subtype.val ((partialMul S g).extendSubtype_apply_of_mem x hx)

lemma perm_inv_apply (S : Finset H) (g : H) (x : S) (hx : g⁻¹ * (x : H) ∈ S) :
    (((perm S g)⁻¹ x : S) : H) = g⁻¹ * x := by
  let y : S := ⟨g⁻¹ * x, hx⟩
  have hy : perm S g y = x := by
    apply Subtype.ext
    rw [perm_apply]
    · simp [y]
    · simpa [y] using x.2
  have he : (perm S g)⁻¹ x = y := by
    rw [← hy]
    exact Equiv.symm_apply_apply _ _
  rw [he]

variable {α : Type u}

/-- All suffix products of a word, including the empty suffix. -/
def trace : List (α × Bool) → Finset (FreeGroup α)
  | [] => {1}
  | a :: l => insert (FreeGroup.mk (a :: l)) (trace l)

lemma one_mem_trace (l : List (α × Bool)) : (1 : FreeGroup α) ∈ trace l := by
  induction l with
  | nil => simp [trace]
  | cons a l ih => exact Finset.mem_insert_of_mem ih

lemma mk_mem_trace (l : List (α × Bool)) : FreeGroup.mk l ∈ trace l := by
  cases l with
  | nil => simp [trace, ← FreeGroup.one_eq_mk]
  | cons a l => simp [trace]

def model (S : Finset (FreeGroup α)) : FreeGroup α →* Equiv.Perm S :=
  FreeGroup.lift (fun a => perm S (FreeGroup.of a))

lemma model_mk_apply (S : Finset (FreeGroup α)) (l : List (α × Bool))
    (hl : trace l ⊆ S) (h1 : (1 : FreeGroup α) ∈ S) :
    (((model S) (FreeGroup.mk l) ⟨1, h1⟩ : S) : FreeGroup α) = FreeGroup.mk l := by
  induction l with
  | nil => simp [← FreeGroup.one_eq_mk]
  | cons a l ih =>
    have ht : trace l ⊆ S := fun x hx => hl (Finset.mem_insert_of_mem hx)
    have hm : FreeGroup.mk (a :: l) ∈ S := hl (mk_mem_trace _)
    have he := ih ht
    obtain ⟨a, b⟩ := a
    cases b
    · change (((perm S (FreeGroup.of a))⁻¹ * (model S) (FreeGroup.mk l)) ⟨1, h1⟩ : S).val = _
      rw [Equiv.Perm.mul_apply, perm_inv_apply, he]
      · rfl
      · rw [he]
        exact hm
    · change ((perm S (FreeGroup.of a) * (model S) (FreeGroup.mk l)) ⟨1, h1⟩ : S).val = _
      rw [Equiv.Perm.mul_apply, perm_apply, he]
      · rfl
      · rw [he]
        exact hm

/-- Every nonidentity free-group element is detected in a finite permutation group. -/
theorem separates {w : FreeGroup α} (hw : w ≠ 1) :
    ∃ (K : Type u) (_ : Group K) (_ : Finite K) (f : FreeGroup α →* K), f w ≠ 1 := by
  obtain ⟨l⟩ := w
  let S := trace l
  refine ⟨Equiv.Perm S, inferInstance, inferInstance, model S, ?_⟩
  intro he
  change (model S) (FreeGroup.mk l) = 1 at he
  have hm := model_mk_apply S l (fun _ hx => hx) (one_mem_trace l)
  rw [he] at hm
  exact hw hm.symm

end
end FiniteModel

/-- A surjective endomorphism of a finitely generated free group is injective. -/
theorem freeGroup_hopf {α : Type*} [Finite α]
    (φ : FreeGroup α →* FreeGroup α) (hφ : Function.Surjective φ) :
    Function.Injective φ := by
  classical
  apply (injective_iff_map_eq_one φ).mpr
  intro w hw
  by_contra hn
  obtain ⟨K, instG, instF, f, hf⟩ := FiniteModel.separates hn
  letI : Group K := instG
  letI : Finite K := instF
  letI : Finite (FreeGroup α →* K) :=
    Finite.of_injective (fun f : FreeGroup α →* K => fun a => f (FreeGroup.of a))
      (fun f g h => FreeGroup.ext_hom f g (congrFun h))
  have hinj : Function.Injective (fun f : FreeGroup α →* K => f.comp φ) := by
    intro f g h
    apply MonoidHom.ext
    intro x
    obtain ⟨y, rfl⟩ := hφ x
    exact DFunLike.congr_fun h y
  obtain ⟨g, hg⟩ := Finite.surjective_of_injective hinj f
  apply hf
  rw [← hg, MonoidHom.comp_apply, hw, map_one]

end TwentyFour
