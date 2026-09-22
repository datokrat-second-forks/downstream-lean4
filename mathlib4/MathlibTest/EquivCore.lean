import Mathlib.Logic.Equiv.Defs

/-! Regression tests for Mathlib's integration with the core `Equiv` API. -/

universe u v w
variable {α : Sort u} {β : Sort v} {γ : Sort w}

-- The coercion rules must not cycle through `Equiv.symm` and its underlying constructor.
example (e : α ≃ β) (x : β) : e (e.symm x) = x := by simp
example (e : α ≃ β) (x : α) : e.symm (e x) = x := by simp
example (e : α ≃ β) : e.toFun = e := by simp
example (e : α ≃ β) : e.invFun = e.symm := by simp

-- Mathlib's pointwise extensionality remains available to `ext` and `grind`.
example (e f : α ≃ β) (h : ∀ x, e x = f x) : e = f := by ext x; exact h x
example (e f : α ≃ β) (h : ∀ x, e x = f x) : e = f := by grind

-- Core uses Mathlib's established names for cancellation and composition inversion.
example (e : α ≃ β) : e.symm.trans e = Equiv.refl β := e.symm_trans_self
example (e : α ≃ β) (f : β ≃ γ) : (e.trans f).symm = f.symm.trans e.symm := by simp

-- `simps` must still use the application projections of core equivalences.
@[simps] def identityEquiv (α : Sort u) : α ≃ α where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

example (x : α) : identityEquiv α x = x := by simp
example (x : α) : (identityEquiv α).symm x = x := by simp

example (e f : α ≃ β) (h : ∀ x, e x = f x) : e = f := Equiv.ext h
example (e : α ≃ β) (f : β ≃ γ) : (e.trans f).symm = f.symm.trans e.symm :=
  Equiv.symm_trans e f
example (f : α → β) (g : β → α) (l r) : (Equiv.mk f g l r : α → β) = f := by simp
example (f : α → β) (g : β → α) (l r) :
    (Equiv.mk f g l r).symm = Equiv.mk g f r l := by simp
