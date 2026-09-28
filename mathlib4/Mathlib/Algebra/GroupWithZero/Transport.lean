/-
Copyright (c) 2026 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import Mathlib.Algebra.Group.Transport
public import Mathlib.Algebra.GroupWithZero.InjSurj

/-!
# Transporting monoid and group with zero structures

`@[transport]` congruences for the classes of monoids and groups with zero, so that
`inferInstanceAs` and `deriving` carry these structures across a `newtype`. As in
`Mathlib/Algebra/Group/Transport.lean`, the operations are those of the per-operation congruences,
so that transport unfolds them.
-/

public section

variable {α β : Type*}

theorem MulZeroClass.ext_toMul_toZero ⦃i j : MulZeroClass α⦄ (h₁ : i.toMul = j.toMul)
    (h₂ : i.toZero = j.toZero) : i = j := by
  rcases i with ⟨⟩; rcases j with ⟨⟩; cases h₁; cases h₂; rfl

/-- `MulZeroClass` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev MulZeroClass.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (MulZeroClass α) (MulZeroClass β) where
  toFun i := @Function.Injective.mulZeroClass α β i ((Mul.canonicalCongr e).toFun i.toMul)
    ((Zero.canonicalCongr e).toFun i.toZero) e.invFun e.right_inv.injective (e.left_inv _)
    fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.mulZeroClass β α i ((Mul.canonicalCongr e).invFun i.toMul)
    ((Zero.canonicalCongr e).invFun i.toZero) e.toFun e.left_inv.injective (e.right_inv _)
    fun _ _ ↦ e.right_inv _
  left_inv i := MulZeroClass.ext_toMul_toZero ((Mul.canonicalCongr e).left_inv i.toMul)
    ((Zero.canonicalCongr e).left_inv i.toZero)
  right_inv i := MulZeroClass.ext_toMul_toZero ((Mul.canonicalCongr e).right_inv i.toMul)
    ((Zero.canonicalCongr e).right_inv i.toZero)

/-- `NoZeroDivisors` holds on both sides of a canonical equivalence, for the transported
multiplication and zero. -/
@[transport]
protected abbrev NoZeroDivisors.canonicalCongr (e : Lean.CanonicalEquivalence α β) [iM : Mul β]
    [iZ : Zero β] {iM' : Mul α} {iZ' : Zero α} (hM : iM' = (Mul.canonicalCongr e).invFun iM)
    (hZ : iZ' = (Zero.canonicalCongr e).invFun iZ) :
    Lean.CanonicalEquivalence (NoZeroDivisors α) (NoZeroDivisors β) := by
  subst hM hZ
  letI := (Mul.canonicalCongr e).invFun iM
  letI := (Zero.canonicalCongr e).invFun iZ
  exact {
    toFun _ := Function.Injective.noZeroDivisors e.invFun e.right_inv.injective rfl fun x y ↦
      congrArg e.invFun (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)).symm
    invFun _ := Function.Injective.noZeroDivisors e.toFun e.left_inv.injective (e.right_inv _)
      fun _ _ ↦ e.right_inv _
    left_inv _ := rfl
    right_inv _ := rfl }

/-- `IsLeftCancelMulZero` holds on both sides of a canonical equivalence, for the transported
multiplication and zero. -/
@[transport]
protected abbrev IsLeftCancelMulZero.canonicalCongr (e : Lean.CanonicalEquivalence α β)
    [iM : Mul β] [iZ : Zero β] {iM' : Mul α} {iZ' : Zero α}
    (hM : iM' = (Mul.canonicalCongr e).invFun iM) (hZ : iZ' = (Zero.canonicalCongr e).invFun iZ) :
    Lean.CanonicalEquivalence (IsLeftCancelMulZero α) (IsLeftCancelMulZero β) := by
  subst hM hZ
  letI := (Mul.canonicalCongr e).invFun iM
  letI := (Zero.canonicalCongr e).invFun iZ
  exact {
    toFun _ := Function.Injective.isLeftCancelMulZero e.invFun e.right_inv.injective rfl
      fun x y ↦ congrArg e.invFun (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)).symm
    invFun _ := Function.Injective.isLeftCancelMulZero e.toFun e.left_inv.injective (e.right_inv _)
      fun _ _ ↦ e.right_inv _
    left_inv _ := rfl
    right_inv _ := rfl }

/-- `IsRightCancelMulZero` holds on both sides of a canonical equivalence, for the transported
multiplication and zero. -/
@[transport]
protected abbrev IsRightCancelMulZero.canonicalCongr (e : Lean.CanonicalEquivalence α β)
    [iM : Mul β] [iZ : Zero β] {iM' : Mul α} {iZ' : Zero α}
    (hM : iM' = (Mul.canonicalCongr e).invFun iM) (hZ : iZ' = (Zero.canonicalCongr e).invFun iZ) :
    Lean.CanonicalEquivalence (IsRightCancelMulZero α) (IsRightCancelMulZero β) := by
  subst hM hZ
  letI := (Mul.canonicalCongr e).invFun iM
  letI := (Zero.canonicalCongr e).invFun iZ
  exact {
    toFun _ := Function.Injective.isRightCancelMulZero e.invFun e.right_inv.injective rfl
      fun x y ↦ congrArg e.invFun (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)).symm
    invFun _ := Function.Injective.isRightCancelMulZero e.toFun e.left_inv.injective
      (e.right_inv _) fun _ _ ↦ e.right_inv _
    left_inv _ := rfl
    right_inv _ := rfl }

theorem MulZeroOneClass.ext_toMulOneClass_toZero ⦃i j : MulZeroOneClass α⦄
    (h₁ : i.toMulOneClass = j.toMulOneClass) (h₂ : i.toZero = j.toZero) : i = j := by
  rcases i with ⟨⟩; rcases j with ⟨⟩; cases h₁; cases h₂; rfl

/-- `MulZeroOneClass` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev MulZeroOneClass.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (MulZeroOneClass α) (MulZeroOneClass β) where
  toFun i := @Function.Injective.mulZeroOneClass α β i ((Mul.canonicalCongr e).toFun i.toMul)
    ((Zero.canonicalCongr e).toFun i.toZero) ((One.canonicalCongr e).toFun i.toOne) e.invFun
    e.right_inv.injective (e.left_inv _) (e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.mulZeroOneClass β α i ((Mul.canonicalCongr e).invFun i.toMul)
    ((Zero.canonicalCongr e).invFun i.toZero) ((One.canonicalCongr e).invFun i.toOne) e.toFun
    e.left_inv.injective (e.right_inv _) (e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv i := MulZeroOneClass.ext_toMulOneClass_toZero
    ((MulOneClass.canonicalCongr e).left_inv i.toMulOneClass)
    ((Zero.canonicalCongr e).left_inv i.toZero)
  right_inv i := MulZeroOneClass.ext_toMulOneClass_toZero
    ((MulOneClass.canonicalCongr e).right_inv i.toMulOneClass)
    ((Zero.canonicalCongr e).right_inv i.toZero)

theorem SemigroupWithZero.ext_toSemigroup_toZero ⦃i j : SemigroupWithZero α⦄
    (h₁ : i.toSemigroup = j.toSemigroup) (h₂ : i.toZero = j.toZero) : i = j := by
  rcases i with ⟨⟩; rcases j with ⟨⟩; cases h₁; cases h₂; rfl

/-- `SemigroupWithZero` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev SemigroupWithZero.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (SemigroupWithZero α) (SemigroupWithZero β) where
  toFun i := @Function.Injective.semigroupWithZero α β ((Zero.canonicalCongr e).toFun i.toZero)
    ((Mul.canonicalCongr e).toFun i.toMul) i e.invFun e.right_inv.injective (e.left_inv _)
    fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.semigroupWithZero β α ((Zero.canonicalCongr e).invFun i.toZero)
    ((Mul.canonicalCongr e).invFun i.toMul) i e.toFun e.left_inv.injective (e.right_inv _)
    fun _ _ ↦ e.right_inv _
  left_inv i := SemigroupWithZero.ext_toSemigroup_toZero
    ((Semigroup.canonicalCongr e).left_inv i.toSemigroup)
    ((Zero.canonicalCongr e).left_inv i.toZero)
  right_inv i := SemigroupWithZero.ext_toSemigroup_toZero
    ((Semigroup.canonicalCongr e).right_inv i.toSemigroup)
    ((Zero.canonicalCongr e).right_inv i.toZero)

theorem MonoidWithZero.ext_toMonoid_toZero ⦃i j : MonoidWithZero α⦄
    (h₁ : i.toMonoid = j.toMonoid) (h₂ : i.toZero = j.toZero) : i = j := by
  rcases i with ⟨⟩; rcases j with ⟨⟩; cases h₁; cases h₂; rfl

/-- `MonoidWithZero` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev MonoidWithZero.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (MonoidWithZero α) (MonoidWithZero β) where
  toFun i := @Function.Injective.monoidWithZero α β ((Zero.canonicalCongr e).toFun i.toZero)
    ((Mul.canonicalCongr e).toFun i.toMul) ((One.canonicalCongr e).toFun i.toOne)
    ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩ i e.invFun e.right_inv.injective (e.left_inv _)
    (e.left_inv _) (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.monoidWithZero β α ((Zero.canonicalCongr e).invFun i.toZero)
    ((Mul.canonicalCongr e).invFun i.toMul) ((One.canonicalCongr e).invFun i.toOne)
    ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩ i e.toFun e.left_inv.injective (e.right_inv _)
    (e.right_inv _) (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv i := MonoidWithZero.ext_toMonoid_toZero ((Monoid.canonicalCongr e).left_inv i.toMonoid)
    ((Zero.canonicalCongr e).left_inv i.toZero)
  right_inv i := MonoidWithZero.ext_toMonoid_toZero
    ((Monoid.canonicalCongr e).right_inv i.toMonoid) ((Zero.canonicalCongr e).right_inv i.toZero)

theorem CommMonoidWithZero.ext_toCommMonoid_toZero ⦃i j : CommMonoidWithZero α⦄
    (h₁ : i.toCommMonoid = j.toCommMonoid) (h₂ : i.toZero = j.toZero) : i = j := by
  rcases i with ⟨⟩; rcases j with ⟨⟩; cases h₁; cases h₂; rfl

/-- `CommMonoidWithZero` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev CommMonoidWithZero.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (CommMonoidWithZero α) (CommMonoidWithZero β) where
  toFun i := @Function.Injective.commMonoidWithZero α β ((Zero.canonicalCongr e).toFun i.toZero)
    ((Mul.canonicalCongr e).toFun i.toMul) ((One.canonicalCongr e).toFun i.toOne)
    ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩ i e.invFun e.right_inv.injective (e.left_inv _)
    (e.left_inv _) (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.commMonoidWithZero β α ((Zero.canonicalCongr e).invFun i.toZero)
    ((Mul.canonicalCongr e).invFun i.toMul) ((One.canonicalCongr e).invFun i.toOne)
    ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩ i e.toFun e.left_inv.injective (e.right_inv _)
    (e.right_inv _) (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv i := CommMonoidWithZero.ext_toCommMonoid_toZero
    ((CommMonoid.canonicalCongr e).left_inv i.toCommMonoid)
    ((Zero.canonicalCongr e).left_inv i.toZero)
  right_inv i := CommMonoidWithZero.ext_toCommMonoid_toZero
    ((CommMonoid.canonicalCongr e).right_inv i.toCommMonoid)
    ((Zero.canonicalCongr e).right_inv i.toZero)

theorem GroupWithZero.ext_toMonoidWithZero_toDivInvMonoid ⦃i j : GroupWithZero α⦄
    (h₁ : i.toMonoidWithZero = j.toMonoidWithZero) (h₂ : i.toDivInvMonoid = j.toDivInvMonoid) :
    i = j := by
  rcases i with ⟨⟩; rcases j with ⟨⟩; cases h₁; cases h₂; rfl

/-- `GroupWithZero` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev GroupWithZero.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (GroupWithZero α) (GroupWithZero β) where
  toFun i := @Function.Injective.groupWithZero α β i ((Zero.canonicalCongr e).toFun i.toZero)
    ((Mul.canonicalCongr e).toFun i.toMul) ((One.canonicalCongr e).toFun i.toOne)
    ((Inv.canonicalCongr e).toFun i.toInv) ((Div.canonicalCongr e).toFun i.toDiv)
    ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩ ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩ e.invFun
    e.right_inv.injective (e.left_inv _) (e.left_inv _) (fun _ _ ↦ e.left_inv _)
    (fun _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _)
    fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.groupWithZero β α i ((Zero.canonicalCongr e).invFun i.toZero)
    ((Mul.canonicalCongr e).invFun i.toMul) ((One.canonicalCongr e).invFun i.toOne)
    ((Inv.canonicalCongr e).invFun i.toInv) ((Div.canonicalCongr e).invFun i.toDiv)
    ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩ ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩ e.toFun
    e.left_inv.injective (e.right_inv _) (e.right_inv _) (fun _ _ ↦ e.right_inv _)
    (fun _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _)
    fun _ _ ↦ e.right_inv _
  left_inv i := GroupWithZero.ext_toMonoidWithZero_toDivInvMonoid
    ((MonoidWithZero.canonicalCongr e).left_inv i.toMonoidWithZero)
    ((DivInvMonoid.canonicalCongr e).left_inv i.toDivInvMonoid)
  right_inv i := GroupWithZero.ext_toMonoidWithZero_toDivInvMonoid
    ((MonoidWithZero.canonicalCongr e).right_inv i.toMonoidWithZero)
    ((DivInvMonoid.canonicalCongr e).right_inv i.toDivInvMonoid)

theorem CommGroupWithZero.ext_toCommMonoidWithZero_toDivInvMonoid ⦃i j : CommGroupWithZero α⦄
    (h₁ : i.toCommMonoidWithZero = j.toCommMonoidWithZero)
    (h₂ : i.toDivInvMonoid = j.toDivInvMonoid) : i = j := by
  rcases i with ⟨⟩; rcases j with ⟨⟩; cases h₁; cases h₂; rfl

/-- `CommGroupWithZero` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev CommGroupWithZero.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (CommGroupWithZero α) (CommGroupWithZero β) where
  toFun i := @Function.Injective.commGroupWithZero α β i ((Zero.canonicalCongr e).toFun i.toZero)
    ((Mul.canonicalCongr e).toFun i.toMul) ((One.canonicalCongr e).toFun i.toOne)
    ((Inv.canonicalCongr e).toFun i.toInv) ((Div.canonicalCongr e).toFun i.toDiv)
    ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩ ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩ e.invFun
    e.right_inv.injective (e.left_inv _) (e.left_inv _) (fun _ _ ↦ e.left_inv _)
    (fun _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _)
    fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.commGroupWithZero β α i ((Zero.canonicalCongr e).invFun i.toZero)
    ((Mul.canonicalCongr e).invFun i.toMul) ((One.canonicalCongr e).invFun i.toOne)
    ((Inv.canonicalCongr e).invFun i.toInv) ((Div.canonicalCongr e).invFun i.toDiv)
    ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩ ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩ e.toFun
    e.left_inv.injective (e.right_inv _) (e.right_inv _) (fun _ _ ↦ e.right_inv _)
    (fun _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _)
    fun _ _ ↦ e.right_inv _
  left_inv i := CommGroupWithZero.ext_toCommMonoidWithZero_toDivInvMonoid
    ((CommMonoidWithZero.canonicalCongr e).left_inv i.toCommMonoidWithZero)
    ((DivInvMonoid.canonicalCongr e).left_inv i.toDivInvMonoid)
  right_inv i := CommGroupWithZero.ext_toCommMonoidWithZero_toDivInvMonoid
    ((CommMonoidWithZero.canonicalCongr e).right_inv i.toCommMonoidWithZero)
    ((DivInvMonoid.canonicalCongr e).right_inv i.toDivInvMonoid)
