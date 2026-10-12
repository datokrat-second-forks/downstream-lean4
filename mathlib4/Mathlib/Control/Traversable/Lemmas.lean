/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Applicative
public import Mathlib.Control.Traversable.Basic

import Mathlib.Tactic.Attr.Register

/-!
# Traversing collections

This file proves basic properties of traversable and applicative functors and defines
`PureTransformation F`, the natural applicative transformation from the identity functor to `F`.

## References

Inspired by [The Essence of the Iterator Pattern][gibbons2009].
-/

@[expose] public section


universe u v

open LawfulTraversable

open Function hiding comp

open Functor

attribute [functor_norm] LawfulTraversable.naturality

attribute [simp] LawfulTraversable.id_traverse

namespace ApplicativeTransformation

variable (F : Type u → Type v) [Applicative F] [LawfulApplicative F]

/-- Remove the identity functor inside `F`. -/
def rightUnitor : ApplicativeTransformation (Comp F Id) F where
  app _ := Comp.rightUnitor F
  preserves_pure' := Comp.rightUnitor_pure
  preserves_seq' := Comp.rightUnitor_seq

/-- Insert the identity functor inside `F`, the inverse of the right unitor. -/
def rightUnitorInv : ApplicativeTransformation F (Comp F Id) where
  app _ := Comp.rightUnitorInv F
  preserves_pure' := Comp.rightUnitorInv_pure
  preserves_seq' := Comp.rightUnitorInv_seq

@[simp] theorem rightUnitor_apply {α} (x : Comp F Id α) :
    rightUnitor F x = Id.run <$> x.run := rfl

@[simp] theorem rightUnitorInv_apply {α} (x : F α) :
    rightUnitorInv F x = Comp.mk (Id.mk <$> x) := rfl

theorem rightUnitor_rightUnitorInv {α} (x : F α) :
    rightUnitor F (rightUnitorInv F x) = x :=
  Comp.rightUnitor_rightUnitorInv x

theorem rightUnitorInv_rightUnitor {α} (x : Comp F Id α) :
    rightUnitorInv F (rightUnitor F x) = x :=
  Comp.rightUnitorInv_rightUnitor x

theorem rightUnitorInv_injective {α} : Function.Injective (fun x : F α => rightUnitorInv F x) :=
  Comp.rightUnitorInv_injective

omit [LawfulApplicative F] in
/-- Remove the identity functor outside `F`. -/
def leftUnitor : ApplicativeTransformation (Comp Id F) F where
  app _ := Comp.leftUnitor F
  preserves_pure' := Comp.leftUnitor_pure
  preserves_seq' := Comp.leftUnitor_seq

omit [LawfulApplicative F] in
/-- Insert the identity functor outside `F`, the inverse of the left unitor. -/
def leftUnitorInv : ApplicativeTransformation F (Comp Id F) where
  app _ := Comp.leftUnitorInv F
  preserves_pure' := Comp.leftUnitorInv_pure
  preserves_seq' := Comp.leftUnitorInv_seq

omit [LawfulApplicative F] in
@[simp] theorem leftUnitor_apply {α} (x : Comp Id F α) :
    leftUnitor F x = x.run.run := rfl

omit [LawfulApplicative F] in
@[simp] theorem leftUnitorInv_apply {α} (x : F α) :
    leftUnitorInv F x = Comp.mk (Id.mk x) := rfl

omit [LawfulApplicative F] in
@[simp] theorem leftUnitor_leftUnitorInv {α} (x : F α) :
    leftUnitor F (leftUnitorInv F x) = x := rfl

omit [LawfulApplicative F] in
@[simp] theorem leftUnitorInv_leftUnitor {α} (x : Comp Id F α) :
    leftUnitorInv F (leftUnitor F x) = x := rfl

omit [LawfulApplicative F] in
theorem leftUnitorInv_injective {α} : Function.Injective (fun x : F α => leftUnitorInv F x) :=
  Comp.leftUnitorInv_injective

end ApplicativeTransformation

namespace Traversable

open ApplicativeTransformation

variable {t : Type u → Type u}
variable [Traversable t] [LawfulTraversable t]
variable (F G : Type u → Type u)
variable [Applicative F] [LawfulApplicative F]
variable [Applicative G] [LawfulApplicative G]
variable {α β γ : Type u}
variable (g : α → F β)
variable (f : β → γ)

/-- The natural applicative transformation from the identity functor
to `F`, defined by `pure : Π {α}, α → F α`. -/
def PureTransformation :
    ApplicativeTransformation Id F where
  app _ x := pure x.run
  preserves_pure' _ := rfl
  preserves_seq' f x := by
    simp only [map_pure, seq_pure]
    rfl

@[simp]
theorem pureTransformation_apply {α} (x : Id α) : PureTransformation F x = pure x.run :=
  rfl

variable {F G}

theorem map_eq_traverse_id : map (f := t) f = Id.run ∘ traverse (pure ∘ f) :=
  funext fun y => congrArg Id.run (traverse_eq_map_id f y).symm

theorem map_traverse (x : t α) :
    map f <$> traverse g x = traverse (map f ∘ g) x := by
  apply rightUnitorInv_injective F
  dsimp only
  refine Eq.trans ?_ (naturality (rightUnitorInv F) (map f ∘ g) x).symm
  have h := comp_traverse (pure ∘ f : β → Id γ) g x
  have ht : traverse (pure ∘ f : β → Id γ) = (fun y : t β => Id.mk (map f y)) :=
    funext (traverse_eq_map_id f)
  rw [ht] at h
  simp only [rightUnitorInv_apply, Function.comp_def, map_map] at h ⊢
  exact h.symm

theorem traverse_map (f : β → F γ) (g : α → β) (x : t α) :
    traverse f (g <$> x) = traverse (f ∘ g) x := by
  apply leftUnitorInv_injective F
  refine Eq.trans ?_ (naturality (leftUnitorInv F) (f ∘ g) x).symm
  have h := comp_traverse f (pure ∘ g : α → Id β) x
  rw [traverse_eq_map_id] at h
  simp only [leftUnitorInv_apply, Function.comp_def] at h ⊢
  exact h.symm


theorem pure_traverse (x : t α) : traverse pure x = (pure x : F (t α)) := by
  have : traverse pure x = pure (traverse (m := Id) pure x).run :=
      (naturality (PureTransformation F) pure x).symm
  rwa [id_traverse] at this

theorem id_sequence (x : t α) : sequence (f := Id) (pure <$> x) = pure x := by
  simp [sequence, traverse_map, id_traverse]

theorem comp_sequence (x : t (F (G α))) :
    sequence (Comp.mk <$> x) = Comp.mk (sequence <$> sequence x) := by
  simp only [sequence, traverse_map, id_comp]; rw [← comp_traverse]; simp [map_id]

theorem naturality' (η : ApplicativeTransformation F G) (x : t (F α)) :
    η (sequence x) = sequence (@η _ <$> x) := by simp [sequence, naturality, traverse_map]

@[functor_norm]
theorem traverse_id : traverse pure = (pure : t α → Id (t α)) := by
  funext x
  exact id_traverse x

@[functor_norm]
theorem traverse_comp (g : α → F β) (h : β → G γ) :
    traverse (Comp.mk ∘ map h ∘ g) =
      (Comp.mk ∘ map (traverse h) ∘ traverse g : t α → Comp F G (t γ)) := by
  ext
  exact comp_traverse _ _ _

theorem traverse_eq_map_id' (f : β → γ) :
    traverse (m := Id) (pure ∘ f) = pure ∘ (map f : t β → t γ) := by
  funext x
  exact traverse_eq_map_id f x

-- @[functor_norm]
theorem traverse_map' (g : α → β) (h : β → G γ) :
    traverse (h ∘ g) = (traverse h ∘ map g : t α → G (t γ)) := by
  ext
  rw [comp_apply, traverse_map]

theorem map_traverse' (g : α → G β) (h : β → γ) :
    traverse (map h ∘ g) = (map (map h) ∘ traverse g : t α → G (t γ)) := by
  ext
  rw [comp_apply, map_traverse]

theorem naturality_pf (η : ApplicativeTransformation F G) (f : α → F β) :
    traverse (@η _ ∘ f) = @η _ ∘ (traverse f : t α → F (t β)) := by
  ext
  rw [comp_apply, naturality]

end Traversable
