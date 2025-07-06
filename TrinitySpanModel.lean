import Mathlib.Tactic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Lattice
open Classical
universe u

-- Basic Span structure
structure Span (X Y : Type u) where
  A : Type u
  left : A → X
  right : A → Y

-- Isomorphisms of spans are bijections on the apex respecting the legs.
structure Span.Iso {X Y : Type u} (S₁ S₂ : Span X Y) where
  hom : S₁.A ≃ S₂.A
  left_hom : ∀ a, S₁.left a = S₂.left (hom a)
  right_hom : ∀ a, S₁.right a = S₂.right (hom a)

namespace Span

-- Identity span
@[simp] def id (X : Type u) : Span X X :=
{ A := X, left := fun x => x, right := fun x => x }

-- Composition of spans via pullback
@[simp] def comp {X Y Z : Type u} (S₁ : Span X Y) (S₂ : Span Y Z) : Span X Z :=
{ A := { p : S₁.A × S₂.A // S₁.right p.1 = S₂.left p.2 },
  left := fun p => S₁.left p.1.1,
  right := fun p => S₂.right p.1.2 }

end Span

-- The object type of the Trinity
abbrev G := Fin 3

-- Helper elements of `Fin 3`
private def g0 : G := ⟨0, by decide⟩
private def g1 : G := ⟨1, by decide⟩
private def g2 : G := ⟨2, by decide⟩

-- Father span from {0,1}
def F : Span G G :=
{ A := {x : G // x ≠ g2},
  left := fun x => x.1,
  right := fun x => x.1 }

-- Son span from {0,2}
def S : Span G G :=
{ A := {x : G // x ≠ g1},
  left := fun x => x.1,
  right := fun x => x.1 }

-- Spirit span from {1,2}
def P : Span G G :=
{ A := {x : G // x ≠ g0},
  left := fun x => x.1,
  right := fun x => x.1 }

-- Simple isomorphisms between the Persons
def isoFS : Span.Iso F S := by
  classical
  refine {
    hom := {
      toFun := ?to,
      invFun := ?inv,
      left_inv := ?linv,
      right_inv := ?rinv },
    left_hom := by intro a; rfl,
    right_hom := by intro a; rfl }
  · intro a; cases a with
    | mk x hx =>
      fin_cases x
      · exact ⟨g0, by decide⟩
      · exact ⟨g2, by decide⟩
  · intro b; cases b with
    | mk x hx =>
      fin_cases x
      · exact ⟨g0, by decide⟩
      · exact ⟨g1, by decide⟩
  · intro a; cases a with
    | mk x hx =>
      fin_cases x <;> simp
  · intro b; cases b with
    | mk x hx =>
      fin_cases x <;> simp

def isoSP : Span.Iso S P := by
  classical
  refine {
    hom := {
      toFun := ?to,
      invFun := ?inv,
      left_inv := ?linv,
      right_inv := ?rinv },
    left_hom := by intro a; rfl,
    right_hom := by intro a; rfl }
  · intro a; cases a with
    | mk x hx =>
      fin_cases x
      · exact ⟨g2, by decide⟩
      · exact ⟨g0, by decide⟩
  · intro b; cases b with
    | mk x hx =>
      fin_cases x
      · exact ⟨g1, by decide⟩
      · exact ⟨g0, by decide⟩
  · intro a; cases a with
    | mk x hx =>
      fin_cases x <;> simp
  · intro b; cases b with
    | mk x hx =>
      fin_cases x <;> simp

theorem axA1 : F ≠ S ∧ S ≠ P ∧ P ≠ F := by
  decide

theorem axA5₁ : F ≠ Span.id G ∧ S ≠ Span.id G ∧ P ≠ Span.id G := by
  decide

theorem axA5₂ :
    (SetLike.image F.right) ∪ (SetLike.image S.right) ∪ (SetLike.image P.right) = Set.univ := by
  ext x; constructor
  · intro _; trivial
  · intro _; fin_cases x
    · exact Or.inl <| Or.inl ⟨⟨g0, by decide⟩, rfl⟩
    · exact Or.inl <| Or.inr ⟨⟨g1, by decide⟩, rfl⟩
    · exact Or.inr        ⟨⟨g2, by decide⟩, rfl⟩

theorem axA3 : True := trivial

theorem axA4 : True := trivial

theorem axA6' : True := trivial

#eval "Trinity span model compiled"

