/-
Copyright (c) 2026 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import Mathlib.Algebra.Ring.Ext
public import Mathlib.Algebra.Ring.InjSurj

/-!
# Transporting semiring and ring structures

`@[transport]` congruences for the casts, the additive monoids and groups with one, and the
semiring and ring classes, so that `inferInstanceAs` and `deriving` carry these structures across a
`newtype`. The operations are those of the per-operation congruences (`Add.canonicalCongr`,
`NatCast.canonicalCongr`, …), so that transport unfolds them, and diamonds between separately
transported instances close by unfolding.
-/

public section

variable {α β : Type*}

/-- `NatCast` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev NatCast.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (NatCast α) (NatCast β) where
  toFun i := ⟨fun n ↦ e.toFun (i.natCast n)⟩
  invFun i := ⟨fun n ↦ e.invFun (i.natCast n)⟩
  left_inv i := congrArg NatCast.mk <| funext fun n ↦ e.left_inv (i.natCast n)
  right_inv i := congrArg NatCast.mk <| funext fun n ↦ e.right_inv (i.natCast n)

/-- `IntCast` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev IntCast.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (IntCast α) (IntCast β) where
  toFun i := ⟨fun n ↦ e.toFun (i.intCast n)⟩
  invFun i := ⟨fun n ↦ e.invFun (i.intCast n)⟩
  left_inv i := congrArg IntCast.mk <| funext fun n ↦ e.left_inv (i.intCast n)
  right_inv i := congrArg IntCast.mk <| funext fun n ↦ e.right_inv (i.intCast n)

/-- `Distrib` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev Distrib.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (Distrib α) (Distrib β) where
  toFun i :=
    letI := (Add.canonicalCongr e).toFun i.toAdd
    letI := (Mul.canonicalCongr e).toFun i.toMul
    Function.Injective.distrib e.invFun e.right_inv.injective (fun _ _ ↦ e.left_inv _)
      fun _ _ ↦ e.left_inv _
  invFun i :=
    letI := (Add.canonicalCongr e).invFun i.toAdd
    letI := (Mul.canonicalCongr e).invFun i.toMul
    Function.Injective.distrib e.toFun e.left_inv.injective (fun _ _ ↦ e.right_inv _)
      fun _ _ ↦ e.right_inv _
  left_inv _ := Distrib.ext
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· + ·) (e.left_inv x) (e.left_inv y)))
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y)))
  right_inv _ := Distrib.ext
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)))
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)))

/-- `LeftDistribClass` holds on both sides of a canonical equivalence, for the transported
operations. -/
@[transport]
protected abbrev LeftDistribClass.canonicalCongr (e : Lean.CanonicalEquivalence α β) [iM : Mul β]
    [iA : Add β] {iM' : Mul α} {iA' : Add α} (hM : iM' = (Mul.canonicalCongr e).invFun iM)
    (hA : iA' = (Add.canonicalCongr e).invFun iA) :
    Lean.CanonicalEquivalence (LeftDistribClass α) (LeftDistribClass β) := by
  subst hM hA
  letI := (Mul.canonicalCongr e).invFun iM
  letI := (Add.canonicalCongr e).invFun iA
  exact {
    toFun _ := Function.Injective.leftDistribClass e.invFun e.right_inv.injective
      (fun x y ↦ congrArg e.invFun (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)).symm)
      fun x y ↦ congrArg e.invFun (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)).symm
    invFun _ := Function.Injective.leftDistribClass e.toFun e.left_inv.injective
      (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
    left_inv _ := rfl
    right_inv _ := rfl }

/-- `RightDistribClass` holds on both sides of a canonical equivalence, for the transported
operations. -/
@[transport]
protected abbrev RightDistribClass.canonicalCongr (e : Lean.CanonicalEquivalence α β) [iM : Mul β]
    [iA : Add β] {iM' : Mul α} {iA' : Add α} (hM : iM' = (Mul.canonicalCongr e).invFun iM)
    (hA : iA' = (Add.canonicalCongr e).invFun iA) :
    Lean.CanonicalEquivalence (RightDistribClass α) (RightDistribClass β) := by
  subst hM hA
  letI := (Mul.canonicalCongr e).invFun iM
  letI := (Add.canonicalCongr e).invFun iA
  exact {
    toFun _ := Function.Injective.rightDistribClass e.invFun e.right_inv.injective
      (fun x y ↦ congrArg e.invFun (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)).symm)
      fun x y ↦ congrArg e.invFun (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)).symm
    invFun _ := Function.Injective.rightDistribClass e.toFun e.left_inv.injective
      (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
    left_inv _ := rfl
    right_inv _ := rfl }

theorem HasDistribNeg.toNeg_injective [Mul α] :
    Function.Injective fun i : HasDistribNeg α ↦ i.toNeg := by
  rintro @⟨@⟨⟨_⟩, _⟩, _, _⟩ @⟨@⟨⟨_⟩, _⟩, _, _⟩ ⟨⟩; rfl

/-- `HasDistribNeg` instances correspond along a canonical equivalence, for the transported
multiplication. -/
@[transport]
protected abbrev HasDistribNeg.canonicalCongr (e : Lean.CanonicalEquivalence α β) [i : Mul β]
    {i' : Mul α} (hi : i' = (Mul.canonicalCongr e).invFun i) :
    Lean.CanonicalEquivalence (HasDistribNeg α) (HasDistribNeg β) where
  toFun h :=
    letI := (Neg.canonicalCongr e).toFun h.toNeg
    Function.Injective.hasDistribNeg e.invFun e.right_inv.injective (fun _ ↦ e.left_inv _) <| by
      subst hi
      exact fun x y ↦ congrArg e.invFun (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)).symm
  invFun h :=
    letI := (Neg.canonicalCongr e).invFun h.toNeg
    Function.Injective.hasDistribNeg e.toFun e.left_inv.injective (fun _ ↦ e.right_inv _) <| by
      subst hi
      exact fun _ _ ↦ e.right_inv _
  left_inv h := HasDistribNeg.toNeg_injective ((Neg.canonicalCongr e).left_inv h.toNeg)
  right_inv h := HasDistribNeg.toNeg_injective ((Neg.canonicalCongr e).right_inv h.toNeg)

/-- `AddMonoidWithOne` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev AddMonoidWithOne.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (AddMonoidWithOne α) (AddMonoidWithOne β) where
  toFun i :=
    letI := (Zero.canonicalCongr e).toFun i.toZero
    letI := (One.canonicalCongr e).toFun i.toOne
    letI := (Add.canonicalCongr e).toFun i.toAdd
    letI : SMul ℕ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    letI := (NatCast.canonicalCongr e).toFun i.toNatCast
    Function.Injective.addMonoidWithOne e.invFun e.right_inv.injective (e.left_inv _)
      (e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) fun _ ↦ e.left_inv _
  invFun i :=
    letI := (Zero.canonicalCongr e).invFun i.toZero
    letI := (One.canonicalCongr e).invFun i.toOne
    letI := (Add.canonicalCongr e).invFun i.toAdd
    letI : SMul ℕ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    letI := (NatCast.canonicalCongr e).invFun i.toNatCast
    Function.Injective.addMonoidWithOne e.toFun e.left_inv.injective (e.right_inv _)
      (e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) fun _ ↦ e.right_inv _
  left_inv _ := AddMonoidWithOne.ext
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· + ·) (e.left_inv x) (e.left_inv y)))
    (e.left_inv _)
  right_inv _ := AddMonoidWithOne.ext
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)))
    (e.right_inv _)

/-- `AddCommMonoidWithOne` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev AddCommMonoidWithOne.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (AddCommMonoidWithOne α) (AddCommMonoidWithOne β) where
  toFun i :=
    letI := (Zero.canonicalCongr e).toFun i.toZero
    letI := (One.canonicalCongr e).toFun i.toOne
    letI := (Add.canonicalCongr e).toFun i.toAdd
    letI : SMul ℕ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    letI := (NatCast.canonicalCongr e).toFun i.toNatCast
    Function.Injective.addCommMonoidWithOne e.invFun e.right_inv.injective (e.left_inv _)
      (e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) fun _ ↦ e.left_inv _
  invFun i :=
    letI := (Zero.canonicalCongr e).invFun i.toZero
    letI := (One.canonicalCongr e).invFun i.toOne
    letI := (Add.canonicalCongr e).invFun i.toAdd
    letI : SMul ℕ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    letI := (NatCast.canonicalCongr e).invFun i.toNatCast
    Function.Injective.addCommMonoidWithOne e.toFun e.left_inv.injective (e.right_inv _)
      (e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) fun _ ↦ e.right_inv _
  left_inv _ := AddCommMonoidWithOne.ext
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· + ·) (e.left_inv x) (e.left_inv y)))
    (e.left_inv _)
  right_inv _ := AddCommMonoidWithOne.ext
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)))
    (e.right_inv _)

/-- `AddGroupWithOne` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev AddGroupWithOne.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (AddGroupWithOne α) (AddGroupWithOne β) where
  toFun i :=
    letI := (Zero.canonicalCongr e).toFun i.toZero
    letI := (One.canonicalCongr e).toFun i.toOne
    letI := (Add.canonicalCongr e).toFun i.toAdd
    letI := (Neg.canonicalCongr e).toFun i.toNeg
    letI := (Sub.canonicalCongr e).toFun i.toSub
    letI : SMul ℕ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    letI : SMul ℤ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    letI := (NatCast.canonicalCongr e).toFun i.toNatCast
    letI := (IntCast.canonicalCongr e).toFun i.toIntCast
    Function.Injective.addGroupWithOne e.invFun e.right_inv.injective (e.left_inv _)
      (e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ ↦ e.left_inv _)
      fun _ ↦ e.left_inv _
  invFun i :=
    letI := (Zero.canonicalCongr e).invFun i.toZero
    letI := (One.canonicalCongr e).invFun i.toOne
    letI := (Add.canonicalCongr e).invFun i.toAdd
    letI := (Neg.canonicalCongr e).invFun i.toNeg
    letI := (Sub.canonicalCongr e).invFun i.toSub
    letI : SMul ℕ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    letI : SMul ℤ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    letI := (NatCast.canonicalCongr e).invFun i.toNatCast
    letI := (IntCast.canonicalCongr e).invFun i.toIntCast
    Function.Injective.addGroupWithOne e.toFun e.left_inv.injective (e.right_inv _)
      (e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ ↦ e.right_inv _)
      fun _ ↦ e.right_inv _
  left_inv _ := AddGroupWithOne.ext
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· + ·) (e.left_inv x) (e.left_inv y)))
    (e.left_inv _)
  right_inv _ := AddGroupWithOne.ext
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)))
    (e.right_inv _)

/-- `AddCommGroupWithOne` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev AddCommGroupWithOne.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (AddCommGroupWithOne α) (AddCommGroupWithOne β) where
  toFun i :=
    letI := (Zero.canonicalCongr e).toFun i.toZero
    letI := (One.canonicalCongr e).toFun i.toOne
    letI := (Add.canonicalCongr e).toFun i.toAdd
    letI := (Neg.canonicalCongr e).toFun i.toNeg
    letI := (Sub.canonicalCongr e).toFun i.toSub
    letI : SMul ℕ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    letI : SMul ℤ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    letI := (NatCast.canonicalCongr e).toFun i.toNatCast
    letI := (IntCast.canonicalCongr e).toFun i.toIntCast
    Function.Injective.addCommGroupWithOne e.invFun e.right_inv.injective (e.left_inv _)
      (e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ ↦ e.left_inv _)
      fun _ ↦ e.left_inv _
  invFun i :=
    letI := (Zero.canonicalCongr e).invFun i.toZero
    letI := (One.canonicalCongr e).invFun i.toOne
    letI := (Add.canonicalCongr e).invFun i.toAdd
    letI := (Neg.canonicalCongr e).invFun i.toNeg
    letI := (Sub.canonicalCongr e).invFun i.toSub
    letI : SMul ℕ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    letI : SMul ℤ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    letI := (NatCast.canonicalCongr e).invFun i.toNatCast
    letI := (IntCast.canonicalCongr e).invFun i.toIntCast
    Function.Injective.addCommGroupWithOne e.toFun e.left_inv.injective (e.right_inv _)
      (e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ ↦ e.right_inv _)
      fun _ ↦ e.right_inv _
  left_inv _ := AddCommGroupWithOne.ext
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· + ·) (e.left_inv x) (e.left_inv y)))
    (e.left_inv _)
  right_inv _ := AddCommGroupWithOne.ext
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)))
    (e.right_inv _)

/-- `NonUnitalNonAssocSemiring` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev NonUnitalNonAssocSemiring.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (NonUnitalNonAssocSemiring α) (NonUnitalNonAssocSemiring β) where
  toFun i :=
    letI := (Zero.canonicalCongr e).toFun i.toZero
    letI := (Add.canonicalCongr e).toFun i.toAdd
    letI := (Mul.canonicalCongr e).toFun i.toMul
    letI : SMul ℕ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    Function.Injective.nonUnitalNonAssocSemiring e.invFun e.right_inv.injective (e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i :=
    letI := (Zero.canonicalCongr e).invFun i.toZero
    letI := (Add.canonicalCongr e).invFun i.toAdd
    letI := (Mul.canonicalCongr e).invFun i.toMul
    letI : SMul ℕ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    Function.Injective.nonUnitalNonAssocSemiring e.toFun e.left_inv.injective (e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv _ := NonUnitalNonAssocSemiring.ext
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· + ·) (e.left_inv x) (e.left_inv y)))
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y)))
  right_inv _ := NonUnitalNonAssocSemiring.ext
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)))
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)))

/-- `NonUnitalSemiring` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev NonUnitalSemiring.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (NonUnitalSemiring α) (NonUnitalSemiring β) where
  toFun i :=
    letI := (Zero.canonicalCongr e).toFun i.toZero
    letI := (Add.canonicalCongr e).toFun i.toAdd
    letI := (Mul.canonicalCongr e).toFun i.toMul
    letI : SMul ℕ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    Function.Injective.nonUnitalSemiring e.invFun e.right_inv.injective (e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i :=
    letI := (Zero.canonicalCongr e).invFun i.toZero
    letI := (Add.canonicalCongr e).invFun i.toAdd
    letI := (Mul.canonicalCongr e).invFun i.toMul
    letI : SMul ℕ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    Function.Injective.nonUnitalSemiring e.toFun e.left_inv.injective (e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv _ := NonUnitalSemiring.ext
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· + ·) (e.left_inv x) (e.left_inv y)))
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y)))
  right_inv _ := NonUnitalSemiring.ext
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)))
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)))

/-- `NonAssocSemiring` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev NonAssocSemiring.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (NonAssocSemiring α) (NonAssocSemiring β) where
  toFun i :=
    letI := (Zero.canonicalCongr e).toFun i.toZero
    letI := (One.canonicalCongr e).toFun i.toOne
    letI := (Add.canonicalCongr e).toFun i.toAdd
    letI := (Mul.canonicalCongr e).toFun i.toMul
    letI : SMul ℕ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    letI := (NatCast.canonicalCongr e).toFun i.toNatCast
    Function.Injective.nonAssocSemiring e.invFun e.right_inv.injective (e.left_inv _)
      (e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _)
      fun _ ↦ e.left_inv _
  invFun i :=
    letI := (Zero.canonicalCongr e).invFun i.toZero
    letI := (One.canonicalCongr e).invFun i.toOne
    letI := (Add.canonicalCongr e).invFun i.toAdd
    letI := (Mul.canonicalCongr e).invFun i.toMul
    letI : SMul ℕ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    letI := (NatCast.canonicalCongr e).invFun i.toNatCast
    Function.Injective.nonAssocSemiring e.toFun e.left_inv.injective (e.right_inv _)
      (e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _)
      (fun _ _ ↦ e.right_inv _) fun _ ↦ e.right_inv _
  left_inv _ := NonAssocSemiring.ext
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· + ·) (e.left_inv x) (e.left_inv y)))
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y)))
  right_inv _ := NonAssocSemiring.ext
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)))
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)))

/-- `Semiring` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev Semiring.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (Semiring α) (Semiring β) where
  toFun i :=
    letI := (Zero.canonicalCongr e).toFun i.toZero
    letI := (One.canonicalCongr e).toFun i.toOne
    letI := (Add.canonicalCongr e).toFun i.toAdd
    letI := (Mul.canonicalCongr e).toFun i.toMul
    letI : SMul ℕ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    letI : Pow β ℕ := ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩
    letI := (NatCast.canonicalCongr e).toFun i.toNatCast
    Function.Injective.semiring e.invFun e.right_inv.injective (e.left_inv _) (e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _)
      (fun _ _ ↦ e.left_inv _) fun _ ↦ e.left_inv _
  invFun i :=
    letI := (Zero.canonicalCongr e).invFun i.toZero
    letI := (One.canonicalCongr e).invFun i.toOne
    letI := (Add.canonicalCongr e).invFun i.toAdd
    letI := (Mul.canonicalCongr e).invFun i.toMul
    letI : SMul ℕ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    letI : Pow α ℕ := ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩
    letI := (NatCast.canonicalCongr e).invFun i.toNatCast
    Function.Injective.semiring e.toFun e.left_inv.injective (e.right_inv _) (e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _)
      (fun _ _ ↦ e.right_inv _) fun _ ↦ e.right_inv _
  left_inv _ := Semiring.ext
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· + ·) (e.left_inv x) (e.left_inv y)))
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y)))
  right_inv _ := Semiring.ext
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)))
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)))

/-- `NonUnitalCommSemiring` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev NonUnitalCommSemiring.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (NonUnitalCommSemiring α) (NonUnitalCommSemiring β) where
  toFun i :=
    letI := (Zero.canonicalCongr e).toFun i.toZero
    letI := (Add.canonicalCongr e).toFun i.toAdd
    letI := (Mul.canonicalCongr e).toFun i.toMul
    letI : SMul ℕ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    Function.Injective.nonUnitalCommSemiring e.invFun e.right_inv.injective (e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i :=
    letI := (Zero.canonicalCongr e).invFun i.toZero
    letI := (Add.canonicalCongr e).invFun i.toAdd
    letI := (Mul.canonicalCongr e).invFun i.toMul
    letI : SMul ℕ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    Function.Injective.nonUnitalCommSemiring e.toFun e.left_inv.injective (e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv _ := NonUnitalCommSemiring.ext
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· + ·) (e.left_inv x) (e.left_inv y)))
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y)))
  right_inv _ := NonUnitalCommSemiring.ext
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)))
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)))

/-- `CommSemiring` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev CommSemiring.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (CommSemiring α) (CommSemiring β) where
  toFun i :=
    letI := (Zero.canonicalCongr e).toFun i.toZero
    letI := (One.canonicalCongr e).toFun i.toOne
    letI := (Add.canonicalCongr e).toFun i.toAdd
    letI := (Mul.canonicalCongr e).toFun i.toMul
    letI : SMul ℕ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    letI : Pow β ℕ := ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩
    letI := (NatCast.canonicalCongr e).toFun i.toNatCast
    Function.Injective.commSemiring e.invFun e.right_inv.injective (e.left_inv _) (e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _)
      (fun _ _ ↦ e.left_inv _) fun _ ↦ e.left_inv _
  invFun i :=
    letI := (Zero.canonicalCongr e).invFun i.toZero
    letI := (One.canonicalCongr e).invFun i.toOne
    letI := (Add.canonicalCongr e).invFun i.toAdd
    letI := (Mul.canonicalCongr e).invFun i.toMul
    letI : SMul ℕ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    letI : Pow α ℕ := ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩
    letI := (NatCast.canonicalCongr e).invFun i.toNatCast
    Function.Injective.commSemiring e.toFun e.left_inv.injective (e.right_inv _) (e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _)
      (fun _ _ ↦ e.right_inv _) fun _ ↦ e.right_inv _
  left_inv _ := CommSemiring.ext
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· + ·) (e.left_inv x) (e.left_inv y)))
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y)))
  right_inv _ := CommSemiring.ext
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)))
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)))

/-- `NonUnitalNonAssocRing` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev NonUnitalNonAssocRing.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (NonUnitalNonAssocRing α) (NonUnitalNonAssocRing β) where
  toFun i :=
    letI := (Zero.canonicalCongr e).toFun i.toZero
    letI := (Add.canonicalCongr e).toFun i.toAdd
    letI := (Mul.canonicalCongr e).toFun i.toMul
    letI := (Neg.canonicalCongr e).toFun i.toNeg
    letI := (Sub.canonicalCongr e).toFun i.toSub
    letI : SMul ℕ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    letI : SMul ℤ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    Function.Injective.nonUnitalNonAssocRing e.invFun e.right_inv.injective (e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ ↦ e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i :=
    letI := (Zero.canonicalCongr e).invFun i.toZero
    letI := (Add.canonicalCongr e).invFun i.toAdd
    letI := (Mul.canonicalCongr e).invFun i.toMul
    letI := (Neg.canonicalCongr e).invFun i.toNeg
    letI := (Sub.canonicalCongr e).invFun i.toSub
    letI : SMul ℕ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    letI : SMul ℤ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    Function.Injective.nonUnitalNonAssocRing e.toFun e.left_inv.injective (e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ ↦ e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv _ := NonUnitalNonAssocRing.ext
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· + ·) (e.left_inv x) (e.left_inv y)))
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y)))
  right_inv _ := NonUnitalNonAssocRing.ext
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)))
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)))

/-- `NonUnitalRing` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev NonUnitalRing.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (NonUnitalRing α) (NonUnitalRing β) where
  toFun i :=
    letI := (Zero.canonicalCongr e).toFun i.toZero
    letI := (Add.canonicalCongr e).toFun i.toAdd
    letI := (Mul.canonicalCongr e).toFun i.toMul
    letI := (Neg.canonicalCongr e).toFun i.toNeg
    letI := (Sub.canonicalCongr e).toFun i.toSub
    letI : SMul ℕ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    letI : SMul ℤ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    Function.Injective.nonUnitalRing e.invFun e.right_inv.injective (e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ ↦ e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i :=
    letI := (Zero.canonicalCongr e).invFun i.toZero
    letI := (Add.canonicalCongr e).invFun i.toAdd
    letI := (Mul.canonicalCongr e).invFun i.toMul
    letI := (Neg.canonicalCongr e).invFun i.toNeg
    letI := (Sub.canonicalCongr e).invFun i.toSub
    letI : SMul ℕ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    letI : SMul ℤ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    Function.Injective.nonUnitalRing e.toFun e.left_inv.injective (e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ ↦ e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv _ := NonUnitalRing.ext
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· + ·) (e.left_inv x) (e.left_inv y)))
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y)))
  right_inv _ := NonUnitalRing.ext
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)))
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)))

/-- `NonAssocRing` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev NonAssocRing.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (NonAssocRing α) (NonAssocRing β) where
  toFun i :=
    letI := (Zero.canonicalCongr e).toFun i.toZero
    letI := (One.canonicalCongr e).toFun i.toOne
    letI := (Add.canonicalCongr e).toFun i.toAdd
    letI := (Mul.canonicalCongr e).toFun i.toMul
    letI := (Neg.canonicalCongr e).toFun i.toNeg
    letI := (Sub.canonicalCongr e).toFun i.toSub
    letI : SMul ℕ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    letI : SMul ℤ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    letI := (NatCast.canonicalCongr e).toFun i.toNatCast
    letI := (IntCast.canonicalCongr e).toFun i.toIntCast
    Function.Injective.nonAssocRing e.invFun e.right_inv.injective (e.left_inv _) (e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ ↦ e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _)
      (fun _ ↦ e.left_inv _) fun _ ↦ e.left_inv _
  invFun i :=
    letI := (Zero.canonicalCongr e).invFun i.toZero
    letI := (One.canonicalCongr e).invFun i.toOne
    letI := (Add.canonicalCongr e).invFun i.toAdd
    letI := (Mul.canonicalCongr e).invFun i.toMul
    letI := (Neg.canonicalCongr e).invFun i.toNeg
    letI := (Sub.canonicalCongr e).invFun i.toSub
    letI : SMul ℕ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    letI : SMul ℤ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    letI := (NatCast.canonicalCongr e).invFun i.toNatCast
    letI := (IntCast.canonicalCongr e).invFun i.toIntCast
    Function.Injective.nonAssocRing e.toFun e.left_inv.injective (e.right_inv _) (e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ ↦ e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _)
      (fun _ ↦ e.right_inv _) fun _ ↦ e.right_inv _
  left_inv _ := NonAssocRing.ext
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· + ·) (e.left_inv x) (e.left_inv y)))
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y)))
  right_inv _ := NonAssocRing.ext
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)))
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)))

/-- `Ring` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev Ring.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (Ring α) (Ring β) where
  toFun i :=
    letI := (Zero.canonicalCongr e).toFun i.toZero
    letI := (One.canonicalCongr e).toFun i.toOne
    letI := (Add.canonicalCongr e).toFun i.toAdd
    letI := (Mul.canonicalCongr e).toFun i.toMul
    letI := (Neg.canonicalCongr e).toFun i.toNeg
    letI := (Sub.canonicalCongr e).toFun i.toSub
    letI : SMul ℕ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    letI : SMul ℤ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    letI : Pow β ℕ := ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩
    letI := (NatCast.canonicalCongr e).toFun i.toNatCast
    letI := (IntCast.canonicalCongr e).toFun i.toIntCast
    Function.Injective.ring e.invFun e.right_inv.injective (e.left_inv _) (e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ ↦ e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ ↦ e.left_inv _) fun _ ↦ e.left_inv _
  invFun i :=
    letI := (Zero.canonicalCongr e).invFun i.toZero
    letI := (One.canonicalCongr e).invFun i.toOne
    letI := (Add.canonicalCongr e).invFun i.toAdd
    letI := (Mul.canonicalCongr e).invFun i.toMul
    letI := (Neg.canonicalCongr e).invFun i.toNeg
    letI := (Sub.canonicalCongr e).invFun i.toSub
    letI : SMul ℕ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    letI : SMul ℤ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    letI : Pow α ℕ := ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩
    letI := (NatCast.canonicalCongr e).invFun i.toNatCast
    letI := (IntCast.canonicalCongr e).invFun i.toIntCast
    Function.Injective.ring e.toFun e.left_inv.injective (e.right_inv _) (e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ ↦ e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ ↦ e.right_inv _) fun _ ↦ e.right_inv _
  left_inv _ := Ring.ext
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· + ·) (e.left_inv x) (e.left_inv y)))
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y)))
  right_inv _ := Ring.ext
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)))
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)))

/-- `NonUnitalCommRing` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev NonUnitalCommRing.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (NonUnitalCommRing α) (NonUnitalCommRing β) where
  toFun i :=
    letI := (Zero.canonicalCongr e).toFun i.toZero
    letI := (Add.canonicalCongr e).toFun i.toAdd
    letI := (Mul.canonicalCongr e).toFun i.toMul
    letI := (Neg.canonicalCongr e).toFun i.toNeg
    letI := (Sub.canonicalCongr e).toFun i.toSub
    letI : SMul ℕ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    letI : SMul ℤ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    Function.Injective.nonUnitalCommRing e.invFun e.right_inv.injective (e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ ↦ e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) fun _ _ ↦ e.left_inv _
  invFun i :=
    letI := (Zero.canonicalCongr e).invFun i.toZero
    letI := (Add.canonicalCongr e).invFun i.toAdd
    letI := (Mul.canonicalCongr e).invFun i.toMul
    letI := (Neg.canonicalCongr e).invFun i.toNeg
    letI := (Sub.canonicalCongr e).invFun i.toSub
    letI : SMul ℕ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    letI : SMul ℤ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    Function.Injective.nonUnitalCommRing e.toFun e.left_inv.injective (e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ ↦ e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) fun _ _ ↦ e.right_inv _
  left_inv _ := NonUnitalCommRing.ext
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· + ·) (e.left_inv x) (e.left_inv y)))
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y)))
  right_inv _ := NonUnitalCommRing.ext
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)))
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)))

/-- `CommRing` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev CommRing.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (CommRing α) (CommRing β) where
  toFun i :=
    letI := (Zero.canonicalCongr e).toFun i.toZero
    letI := (One.canonicalCongr e).toFun i.toOne
    letI := (Add.canonicalCongr e).toFun i.toAdd
    letI := (Mul.canonicalCongr e).toFun i.toMul
    letI := (Neg.canonicalCongr e).toFun i.toNeg
    letI := (Sub.canonicalCongr e).toFun i.toSub
    letI : SMul ℕ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    letI : SMul ℤ β := ⟨fun n x ↦ e.toFun (n • e.invFun x)⟩
    letI : Pow β ℕ := ⟨fun x n ↦ e.toFun (e.invFun x ^ n)⟩
    letI := (NatCast.canonicalCongr e).toFun i.toNatCast
    letI := (IntCast.canonicalCongr e).toFun i.toIntCast
    Function.Injective.commRing e.invFun e.right_inv.injective (e.left_inv _) (e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ ↦ e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _) (fun _ _ ↦ e.left_inv _)
      (fun _ _ ↦ e.left_inv _) (fun _ ↦ e.left_inv _) fun _ ↦ e.left_inv _
  invFun i :=
    letI := (Zero.canonicalCongr e).invFun i.toZero
    letI := (One.canonicalCongr e).invFun i.toOne
    letI := (Add.canonicalCongr e).invFun i.toAdd
    letI := (Mul.canonicalCongr e).invFun i.toMul
    letI := (Neg.canonicalCongr e).invFun i.toNeg
    letI := (Sub.canonicalCongr e).invFun i.toSub
    letI : SMul ℕ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    letI : SMul ℤ α := ⟨fun n x ↦ e.invFun (n • e.toFun x)⟩
    letI : Pow α ℕ := ⟨fun x n ↦ e.invFun (e.toFun x ^ n)⟩
    letI := (NatCast.canonicalCongr e).invFun i.toNatCast
    letI := (IntCast.canonicalCongr e).invFun i.toIntCast
    Function.Injective.commRing e.toFun e.left_inv.injective (e.right_inv _) (e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ ↦ e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _) (fun _ _ ↦ e.right_inv _)
      (fun _ _ ↦ e.right_inv _) (fun _ ↦ e.right_inv _) fun _ ↦ e.right_inv _
  left_inv _ := CommRing.ext
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· + ·) (e.left_inv x) (e.left_inv y)))
    (funext₂ fun x y ↦ (e.left_inv _).trans (congrArg₂ (· * ·) (e.left_inv x) (e.left_inv y)))
  right_inv _ := CommRing.ext
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· + ·) (e.right_inv x) (e.right_inv y)))
    (funext₂ fun x y ↦ (e.right_inv _).trans (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)))

/-- `IsDomain` holds on both sides of a canonical equivalence, for the transported semiring
structure. -/
@[transport]
protected abbrev IsDomain.canonicalCongr (e : Lean.CanonicalEquivalence α β) [i : Semiring β]
    {i' : Semiring α} (hi : i' = (Semiring.canonicalCongr e).invFun i) :
    Lean.CanonicalEquivalence (IsDomain α) (IsDomain β) := by
  subst hi
  letI := (Semiring.canonicalCongr e).invFun i
  exact {
    toFun _ :=
      { toIsCancelMulZero := Function.Injective.isCancelMulZero e.invFun e.right_inv.injective
          rfl fun x y ↦
            congrArg e.invFun (congrArg₂ (· * ·) (e.right_inv x) (e.right_inv y)).symm
        toNontrivial := (Nontrivial.canonicalCongr e).toFun inferInstance }
    invFun _ :=
      { toIsCancelMulZero := Function.Injective.isCancelMulZero e.toFun e.left_inv.injective
          (e.right_inv _) fun _ _ ↦ e.right_inv _
        toNontrivial := (Nontrivial.canonicalCongr e).invFun inferInstance }
    left_inv _ := rfl
    right_inv _ := rfl }
