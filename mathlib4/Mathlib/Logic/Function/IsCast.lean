/-
Copyright (c) 2026 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import Mathlib.Init

/-!
# Cast functions

`Function.IsCast f` says that `f : α → β` is a cast along a type equality `α = β`. A map along a
cast function, such as `List.congrMap f`, is a cast as well. Maps are registered with
`@[congr_map]`: when `f` is the constructor or projection of a `+defeq` structure, the elaborator
reduces them like the identity. For example,
`List.congrMap OrderDual.ofDual' (List.congrMap OrderDual.toDual' l)` is `l` by `rfl`.
-/

@[expose] public section

universe u

namespace Function

/-- `f` is a cast along a type equality. -/
class IsCast {α β : Type u} (f : α → β) : Prop where
  eq : α = β
  apply_eq : ∀ a, f a = cast eq a

instance IsCast.id {α : Type u} : IsCast (@id α) := ⟨rfl, fun _ ↦ rfl⟩

instance IsCast.comp {α β γ : Type u} (g : β → γ) (f : α → β) [hg : IsCast g] [hf : IsCast f] :
    IsCast (g ∘ f) where
  eq := hf.eq.trans hg.eq
  apply_eq a := by
    change g (f a) = _
    rw [hf.apply_eq, hg.apply_eq, cast_cast]

theorem IsCast.injective {α β : Type u} (f : α → β) [h : IsCast f] : Injective f := fun a b hab ↦ by
  have := congrArg (cast h.eq.symm) hab
  rwa [h.apply_eq, h.apply_eq, cast_cast, cast_cast, cast_eq, cast_eq] at this

end Function

/-- `l` as a list of `β`, along a cast function `f`. -/
@[congr_map, irreducible]
def List.congrMap {α β : Type u} (f : α → β) [h : Function.IsCast f] (l : List α) : List β :=
  cast (congrArg List h.eq) l

instance List.isCast_congrMap {α β : Type u} (f : α → β) [h : Function.IsCast f] :
    Function.IsCast (List.congrMap f) where
  eq := congrArg List h.eq
  apply_eq _ := by unfold List.congrMap; rfl
