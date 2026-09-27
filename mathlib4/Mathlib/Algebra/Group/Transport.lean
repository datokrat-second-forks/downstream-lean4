/-
Copyright (c) 2026 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import Mathlib.Algebra.Group.Ext
public import Mathlib.Algebra.Group.InjSurj

/-!
# Transporting monoid and group structures

`@[transport]` congruences for the semigroup, monoid and group classes, so that `inferInstanceAs`
and `deriving` carry these structures across a `newtype`. The operations are those of the
per-operation congruences (`Mul.canonicalCongr`, `One.canonicalCongr`, …), so that transport
unfolds them, and diamonds between separately transported instances close by unfolding.

This file is kept light (no `Finset`), so that the order synonyms can import it.
-/

public section

variable {α β M : Type*}

/-- `Pow` instances correspond along canonical equivalences of the bases and of the exponents. -/
@[transport]
protected abbrev Pow.canonicalCongr {N : Type*} (e₁ : Lean.CanonicalEquivalence α β)
    (e₂ : Lean.CanonicalEquivalence M N) :
    Lean.CanonicalEquivalence (Pow α M) (Pow β N) where
  toFun i := ⟨fun x n ↦ e₁.toFun (i.pow (e₁.invFun x) (e₂.invFun n))⟩
  invFun i := ⟨fun x n ↦ e₁.invFun (i.pow (e₁.toFun x) (e₂.toFun n))⟩
  left_inv i := congrArg Pow.mk <| funext fun x ↦ funext fun n ↦
    (e₁.left_inv _).trans (congr (congrArg i.pow (e₁.left_inv x)) (e₂.left_inv n))
  right_inv i := congrArg Pow.mk <| funext fun x ↦ funext fun n ↦
    (e₁.right_inv _).trans (congr (congrArg i.pow (e₁.right_inv x)) (e₂.right_inv n))

@[to_additive]
theorem Semigroup.toMul_injective : Function.Injective (@Semigroup.toMul α) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

/-- `Semigroup` instances correspond along a canonical equivalence. -/
@[to_additive (attr := transport)
  /-- `AddSemigroup` instances correspond along a canonical equivalence. -/]
protected abbrev Semigroup.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (Semigroup α) (Semigroup β) where
  toFun i := @Function.Injective.semigroup β α ((Mul.canonicalCongr e).toFun i.toMul) i e.invFun
    e.right_inv.injective fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.semigroup α β ((Mul.canonicalCongr e).invFun i.toMul) i e.toFun
    e.left_inv.injective fun _ _ ↦ e.right_inv _
  left_inv i := Semigroup.toMul_injective ((Mul.canonicalCongr e).left_inv i.toMul)
  right_inv i := Semigroup.toMul_injective ((Mul.canonicalCongr e).right_inv i.toMul)

@[to_additive]
theorem CommSemigroup.toSemigroup_injective :
    Function.Injective (@CommSemigroup.toSemigroup α) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

/-- `CommSemigroup` instances correspond along a canonical equivalence. -/
@[to_additive (attr := transport)
  /-- `AddCommSemigroup` instances correspond along a canonical equivalence. -/]
protected abbrev CommSemigroup.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (CommSemigroup α) (CommSemigroup β) where
  toFun i := @Function.Injective.commSemigroup β α ((Mul.canonicalCongr e).toFun i.toMul) i
    e.invFun e.right_inv.injective fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.commSemigroup α β ((Mul.canonicalCongr e).invFun i.toMul) i
    e.toFun e.left_inv.injective fun _ _ ↦ e.right_inv _
  left_inv i := CommSemigroup.toSemigroup_injective <|
    (Semigroup.canonicalCongr e).left_inv i.toSemigroup
  right_inv i := CommSemigroup.toSemigroup_injective <|
    (Semigroup.canonicalCongr e).right_inv i.toSemigroup

/-- `IsLeftCancelMul` holds on both sides of a canonical equivalence, for the transported
multiplication. -/
@[to_additive (attr := transport) /-- `IsLeftCancelAdd` holds on both sides of a canonical
equivalence, for the transported addition. -/]
protected abbrev IsLeftCancelMul.canonicalCongr (e : Lean.CanonicalEquivalence α β) [i : Mul β]
    {i' : Mul α} (hi : i' = (Mul.canonicalCongr e).invFun i) :
    Lean.CanonicalEquivalence (IsLeftCancelMul α) (IsLeftCancelMul β) := by
  subst hi
  letI := (Mul.canonicalCongr e).invFun i
  exact {
    toFun _ := Function.Injective.isLeftCancelMul e.invFun e.right_inv.injective fun x y ↦
      congrArg e.invFun (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)).symm
    invFun _ := Function.Injective.isLeftCancelMul e.toFun e.left_inv.injective fun _ _ ↦
      e.right_inv _
    left_inv _ := rfl
    right_inv _ := rfl }

/-- `IsRightCancelMul` holds on both sides of a canonical equivalence, for the transported
multiplication. -/
@[to_additive (attr := transport) /-- `IsRightCancelAdd` holds on both sides of a canonical
equivalence, for the transported addition. -/]
protected abbrev IsRightCancelMul.canonicalCongr (e : Lean.CanonicalEquivalence α β) [i : Mul β]
    {i' : Mul α} (hi : i' = (Mul.canonicalCongr e).invFun i) :
    Lean.CanonicalEquivalence (IsRightCancelMul α) (IsRightCancelMul β) := by
  subst hi
  letI := (Mul.canonicalCongr e).invFun i
  exact {
    toFun _ := Function.Injective.isRightCancelMul e.invFun e.right_inv.injective fun x y ↦
      congrArg e.invFun (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)).symm
    invFun _ := Function.Injective.isRightCancelMul e.toFun e.left_inv.injective fun _ _ ↦
      e.right_inv _
    left_inv _ := rfl
    right_inv _ := rfl }

/-- `MulOneClass` instances correspond along a canonical equivalence. -/
@[to_additive (attr := transport)
  /-- `AddZeroClass` instances correspond along a canonical equivalence. -/]
protected abbrev MulOneClass.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (MulOneClass α) (MulOneClass β) where
  toFun i := @Function.Injective.mulOneClass β α ((Mul.canonicalCongr e).toFun i.toMul)
    ((One.canonicalCongr e).toFun i.toOne) i e.invFun e.right_inv.injective (e.left_inv _)
    fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.mulOneClass α β ((Mul.canonicalCongr e).invFun i.toMul)
    ((One.canonicalCongr e).invFun i.toOne) i e.toFun e.left_inv.injective (e.right_inv _)
    fun _ _ ↦ e.right_inv _
  left_inv _ := MulOneClass.ext <| funext₂ fun x y ↦
    (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y))
  right_inv _ := MulOneClass.ext <| funext₂ fun x y ↦
    (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y))

/-- `Monoid` instances correspond along a canonical equivalence. -/
@[to_additive (attr := transport)
  /-- `AddMonoid` instances correspond along a canonical equivalence. -/]
protected abbrev Monoid.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (Monoid α) (Monoid β) where
  toFun i := @Function.Injective.monoid β α ((Mul.canonicalCongr e).toFun i.toMul)
    ((One.canonicalCongr e).toFun i.toOne) ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩ i e.invFun
    e.right_inv.injective (e.left_inv _) (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.monoid α β ((Mul.canonicalCongr e).invFun i.toMul)
    ((One.canonicalCongr e).invFun i.toOne) ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩ i e.toFun
    e.left_inv.injective (e.right_inv _) (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv _ := Monoid.ext <| funext₂ fun x y ↦
    (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y))
  right_inv _ := Monoid.ext <| funext₂ fun x y ↦
    (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y))

/-- `CommMonoid` instances correspond along a canonical equivalence. -/
@[to_additive (attr := transport)
  /-- `AddCommMonoid` instances correspond along a canonical equivalence. -/]
protected abbrev CommMonoid.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (CommMonoid α) (CommMonoid β) where
  toFun i := @Function.Injective.commMonoid β α ((Mul.canonicalCongr e).toFun i.toMul)
    ((One.canonicalCongr e).toFun i.toOne) ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩ i e.invFun
    e.right_inv.injective (e.left_inv _) (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.commMonoid α β ((Mul.canonicalCongr e).invFun i.toMul)
    ((One.canonicalCongr e).invFun i.toOne) ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩ i e.toFun
    e.left_inv.injective (e.right_inv _) (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv _ := CommMonoid.ext <| funext₂ fun x y ↦
    (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y))
  right_inv _ := CommMonoid.ext <| funext₂ fun x y ↦
    (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y))

/-- `LeftCancelMonoid` instances correspond along a canonical equivalence. -/
@[to_additive (attr := transport)
  /-- `AddLeftCancelMonoid` instances correspond along a canonical equivalence. -/]
protected abbrev LeftCancelMonoid.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (LeftCancelMonoid α) (LeftCancelMonoid β) where
  toFun i := @Function.Injective.leftCancelMonoid β α ((Mul.canonicalCongr e).toFun i.toMul)
    ((One.canonicalCongr e).toFun i.toOne) ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩ i e.invFun
    e.right_inv.injective (e.left_inv _) (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.leftCancelMonoid α β ((Mul.canonicalCongr e).invFun i.toMul)
    ((One.canonicalCongr e).invFun i.toOne) ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩ i e.toFun
    e.left_inv.injective (e.right_inv _) (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv _ := LeftCancelMonoid.ext <| funext₂ fun x y ↦
    (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y))
  right_inv _ := LeftCancelMonoid.ext <| funext₂ fun x y ↦
    (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y))

/-- `RightCancelMonoid` instances correspond along a canonical equivalence. -/
@[to_additive (attr := transport)
  /-- `AddRightCancelMonoid` instances correspond along a canonical equivalence. -/]
protected abbrev RightCancelMonoid.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (RightCancelMonoid α) (RightCancelMonoid β) where
  toFun i := @Function.Injective.rightCancelMonoid β α ((Mul.canonicalCongr e).toFun i.toMul)
    ((One.canonicalCongr e).toFun i.toOne) ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩ i e.invFun
    e.right_inv.injective (e.left_inv _) (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.rightCancelMonoid α β ((Mul.canonicalCongr e).invFun i.toMul)
    ((One.canonicalCongr e).invFun i.toOne) ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩ i e.toFun
    e.left_inv.injective (e.right_inv _) (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv _ := RightCancelMonoid.ext <| funext₂ fun x y ↦
    (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y))
  right_inv _ := RightCancelMonoid.ext <| funext₂ fun x y ↦
    (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y))

/-- `CancelMonoid` instances correspond along a canonical equivalence. -/
@[to_additive (attr := transport)
  /-- `AddCancelMonoid` instances correspond along a canonical equivalence. -/]
protected abbrev CancelMonoid.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (CancelMonoid α) (CancelMonoid β) where
  toFun i := @Function.Injective.cancelMonoid β α ((Mul.canonicalCongr e).toFun i.toMul)
    ((One.canonicalCongr e).toFun i.toOne) ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩ i e.invFun
    e.right_inv.injective (e.left_inv _) (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.cancelMonoid α β ((Mul.canonicalCongr e).invFun i.toMul)
    ((One.canonicalCongr e).invFun i.toOne) ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩ i e.toFun
    e.left_inv.injective (e.right_inv _) (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv _ := CancelMonoid.ext <| funext₂ fun x y ↦
    (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y))
  right_inv _ := CancelMonoid.ext <| funext₂ fun x y ↦
    (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y))

/-- `CancelCommMonoid` instances correspond along a canonical equivalence. -/
@[to_additive (attr := transport)
  /-- `AddCancelCommMonoid` instances correspond along a canonical equivalence. -/]
protected abbrev CancelCommMonoid.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (CancelCommMonoid α) (CancelCommMonoid β) where
  toFun i := @Function.Injective.cancelCommMonoid β α ((Mul.canonicalCongr e).toFun i.toMul)
    ((One.canonicalCongr e).toFun i.toOne) ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩ i e.invFun
    e.right_inv.injective (e.left_inv _) (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.cancelCommMonoid α β ((Mul.canonicalCongr e).invFun i.toMul)
    ((One.canonicalCongr e).invFun i.toOne) ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩ i e.toFun
    e.left_inv.injective (e.right_inv _) (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv _ := CancelCommMonoid.ext <| funext₂ fun x y ↦
    (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y))
  right_inv _ := CancelCommMonoid.ext <| funext₂ fun x y ↦
    (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y))

@[to_additive]
theorem InvolutiveInv.toInv_injective : Function.Injective (@InvolutiveInv.toInv α) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

/-- `InvolutiveInv` instances correspond along a canonical equivalence. -/
@[to_additive (attr := transport)
  /-- `InvolutiveNeg` instances correspond along a canonical equivalence. -/]
protected abbrev InvolutiveInv.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (InvolutiveInv α) (InvolutiveInv β) where
  toFun i := @Function.Injective.involutiveInv α β ((Inv.canonicalCongr e).toFun i.toInv) i
    e.invFun e.right_inv.injective fun _ ↦ e.left_inv _
  invFun i := @Function.Injective.involutiveInv β α ((Inv.canonicalCongr e).invFun i.toInv) i
    e.toFun e.left_inv.injective fun _ ↦ e.right_inv _
  left_inv i := InvolutiveInv.toInv_injective ((Inv.canonicalCongr e).left_inv i.toInv)
  right_inv i := InvolutiveInv.toInv_injective ((Inv.canonicalCongr e).right_inv i.toInv)

/-- `DivInvMonoid` instances correspond along a canonical equivalence. -/
@[to_additive (attr := transport)
  /-- `SubNegMonoid` instances correspond along a canonical equivalence. -/]
protected abbrev DivInvMonoid.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (DivInvMonoid α) (DivInvMonoid β) where
  toFun i := @Function.Injective.divInvMonoid β α ((Mul.canonicalCongr e).toFun i.toMul)
    ((One.canonicalCongr e).toFun i.toOne) ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩
    ((Inv.canonicalCongr e).toFun i.toInv) ((Div.canonicalCongr e).toFun i.toDiv)
    ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩ i e.invFun e.right_inv.injective (e.left_inv _)
    (fun _ _ ↦ e.left_inv _) (fun _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _)
    (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.divInvMonoid α β ((Mul.canonicalCongr e).invFun i.toMul)
    ((One.canonicalCongr e).invFun i.toOne) ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩
    ((Inv.canonicalCongr e).invFun i.toInv) ((Div.canonicalCongr e).invFun i.toDiv)
    ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩ i e.toFun e.left_inv.injective (e.right_inv _)
    (fun _ _ ↦ e.right_inv _) (fun _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _)
    (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv _ := DivInvMonoid.ext
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y)))
    (funext fun x ↦ (e.left_inv _).trans (congrArg (·⁻¹) (e.left_inv x)))
  right_inv _ := DivInvMonoid.ext
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)))
    (funext fun x ↦ (e.right_inv _).trans (congrArg (·⁻¹) (e.right_inv x)))

@[to_additive]
theorem DivisionMonoid.toDivInvMonoid_injective :
    Function.Injective (@DivisionMonoid.toDivInvMonoid α) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

/-- `DivisionMonoid` instances correspond along a canonical equivalence. -/
@[to_additive (attr := transport)
  /-- `SubtractionMonoid` instances correspond along a canonical equivalence. -/]
protected abbrev DivisionMonoid.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (DivisionMonoid α) (DivisionMonoid β) where
  toFun i := @Function.Injective.divisionMonoid β α ((Mul.canonicalCongr e).toFun i.toMul)
    ((One.canonicalCongr e).toFun i.toOne) ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩
    ((Inv.canonicalCongr e).toFun i.toInv) ((Div.canonicalCongr e).toFun i.toDiv)
    ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩ i e.invFun e.right_inv.injective (e.left_inv _)
    (fun _ _ ↦ e.left_inv _) (fun _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _)
    (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.divisionMonoid α β ((Mul.canonicalCongr e).invFun i.toMul)
    ((One.canonicalCongr e).invFun i.toOne) ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩
    ((Inv.canonicalCongr e).invFun i.toInv) ((Div.canonicalCongr e).invFun i.toDiv)
    ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩ i e.toFun e.left_inv.injective (e.right_inv _)
    (fun _ _ ↦ e.right_inv _) (fun _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _)
    (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv i := DivisionMonoid.toDivInvMonoid_injective <|
    (DivInvMonoid.canonicalCongr e).left_inv i.toDivInvMonoid
  right_inv i := DivisionMonoid.toDivInvMonoid_injective <|
    (DivInvMonoid.canonicalCongr e).right_inv i.toDivInvMonoid

@[to_additive]
theorem DivisionCommMonoid.toDivisionMonoid_injective :
    Function.Injective (@DivisionCommMonoid.toDivisionMonoid α) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

/-- `DivisionCommMonoid` instances correspond along a canonical equivalence. -/
@[to_additive (attr := transport)
  /-- `SubtractionCommMonoid` instances correspond along a canonical equivalence. -/]
protected abbrev DivisionCommMonoid.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (DivisionCommMonoid α) (DivisionCommMonoid β) where
  toFun i := @Function.Injective.divisionCommMonoid β α ((Mul.canonicalCongr e).toFun i.toMul)
    ((One.canonicalCongr e).toFun i.toOne) ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩
    ((Inv.canonicalCongr e).toFun i.toInv) ((Div.canonicalCongr e).toFun i.toDiv)
    ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩ i e.invFun e.right_inv.injective (e.left_inv _)
    (fun _ _ ↦ e.left_inv _) (fun _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _)
    (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.divisionCommMonoid α β ((Mul.canonicalCongr e).invFun i.toMul)
    ((One.canonicalCongr e).invFun i.toOne) ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩
    ((Inv.canonicalCongr e).invFun i.toInv) ((Div.canonicalCongr e).invFun i.toDiv)
    ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩ i e.toFun e.left_inv.injective (e.right_inv _)
    (fun _ _ ↦ e.right_inv _) (fun _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _)
    (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv i := DivisionCommMonoid.toDivisionMonoid_injective <|
    (DivisionMonoid.canonicalCongr e).left_inv i.toDivisionMonoid
  right_inv i := DivisionCommMonoid.toDivisionMonoid_injective <|
    (DivisionMonoid.canonicalCongr e).right_inv i.toDivisionMonoid

/-- `Group` instances correspond along a canonical equivalence. -/
@[to_additive (attr := transport)
  /-- `AddGroup` instances correspond along a canonical equivalence. -/]
protected abbrev Group.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (Group α) (Group β) where
  toFun i := @Function.Injective.group β α ((Mul.canonicalCongr e).toFun i.toMul)
    ((One.canonicalCongr e).toFun i.toOne) ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩
    ((Inv.canonicalCongr e).toFun i.toInv) ((Div.canonicalCongr e).toFun i.toDiv)
    ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩ i e.invFun e.right_inv.injective (e.left_inv _)
    (fun _ _ ↦ e.left_inv _) (fun _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _)
    (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.group α β ((Mul.canonicalCongr e).invFun i.toMul)
    ((One.canonicalCongr e).invFun i.toOne) ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩
    ((Inv.canonicalCongr e).invFun i.toInv) ((Div.canonicalCongr e).invFun i.toDiv)
    ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩ i e.toFun e.left_inv.injective (e.right_inv _)
    (fun _ _ ↦ e.right_inv _) (fun _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _)
    (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv _ := Group.ext <| funext₂ fun x y ↦
    (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y))
  right_inv _ := Group.ext <| funext₂ fun x y ↦
    (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y))

/-- `CommGroup` instances correspond along a canonical equivalence. -/
@[to_additive (attr := transport)
  /-- `AddCommGroup` instances correspond along a canonical equivalence. -/]
protected abbrev CommGroup.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (CommGroup α) (CommGroup β) where
  toFun i := @Function.Injective.commGroup β α ((Mul.canonicalCongr e).toFun i.toMul)
    ((One.canonicalCongr e).toFun i.toOne) ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩
    ((Inv.canonicalCongr e).toFun i.toInv) ((Div.canonicalCongr e).toFun i.toDiv)
    ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩ i e.invFun e.right_inv.injective (e.left_inv _)
    (fun _ _ ↦ e.left_inv _) (fun _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _)
    (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.commGroup α β ((Mul.canonicalCongr e).invFun i.toMul)
    ((One.canonicalCongr e).invFun i.toOne) ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩
    ((Inv.canonicalCongr e).invFun i.toInv) ((Div.canonicalCongr e).invFun i.toDiv)
    ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩ i e.toFun e.left_inv.injective (e.right_inv _)
    (fun _ _ ↦ e.right_inv _) (fun _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _)
    (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv _ := CommGroup.ext <| funext₂ fun x y ↦
    (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y))
  right_inv _ := CommGroup.ext <| funext₂ fun x y ↦
    (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y))
