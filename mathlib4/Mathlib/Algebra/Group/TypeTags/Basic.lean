/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Logic.Equiv.Defs

/-!
# Type tags that turn additive structures into multiplicative, and vice versa

We define two type tags:

* `Additive α`: turns any multiplicative structure on `α` into the corresponding
  additive structure on `Additive α`;
* `Multiplicative α`: turns any additive structure on `α` into the corresponding
  multiplicative structure on `Multiplicative α`.

We also define instances `Additive.*` and `Multiplicative.*` that actually transfer the structures.

## See also

This file is similar to `Mathlib/Order/Synonym.lean`.

-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered MonoidHom Finite

universe u v

variable {α : Type u} {β : Type v}

/-- If `α` carries some multiplicative structure, then `Additive α` carries the corresponding
additive structure.

`Additive α` and `α` are different types: convert between them with `Additive.ofMul` and
`Additive.toMul`. -/
newtype Additive (α : Type*) where
  /-- Reinterpret `x : α` as an element of `Additive α`. This is the raw constructor; the bundled
  equivalence `Additive.ofMul` should be preferred. -/
  ofMul' ::
  /-- Reinterpret `x : Additive α` as an element of `α`. This is the raw projection; the bundled
  equivalence `Additive.toMul` should be preferred. -/
  toMul' : α

/-- If `α` carries some additive structure, then `Multiplicative α` carries the corresponding
multiplicative structure.

`Multiplicative α` and `α` are different types: convert between them with `Multiplicative.ofAdd`
and `Multiplicative.toAdd`. -/
newtype Multiplicative (α : Type*) where
  /-- Reinterpret `x : α` as an element of `Multiplicative α`. This is the raw constructor; the
  bundled equivalence `Multiplicative.ofAdd` should be preferred. -/
  ofAdd' ::
  /-- Reinterpret `x : Multiplicative α` as an element of `α`. This is the raw projection; the
  bundled equivalence `Multiplicative.toAdd` should be preferred. -/
  toAdd' : α

namespace Additive

/-- Reinterpret `x : α` as an element of `Additive α`. -/
@[implicit_reducible]
def ofMul : α ≃ Additive α :=
  ⟨ofMul', toMul', fun _ => rfl, fun _ => rfl⟩

/-- Reinterpret `x : Additive α` as an element of `α`. -/
@[implicit_reducible]
def toMul : Additive α ≃ α := ofMul.symm

@[simp]
theorem ofMul_symm_eq : (@ofMul α).symm = toMul :=
  rfl

@[simp]
theorem toMul_symm_eq : (@toMul α).symm = ofMul :=
  rfl

@[ext] lemma ext {a b : Additive α} (hab : a.toMul = b.toMul) : a = b := toMul.injective hab

@[simp]
protected lemma «forall» {p : Additive α → Prop} : (∀ a, p a) ↔ ∀ a, p (ofMul a) :=
  ofMul.forall_congr_right.symm

@[simp]
protected lemma «exists» {p : Additive α → Prop} : (∃ a, p a) ↔ ∃ a, p (ofMul a) :=
  ofMul.exists_congr_right.symm

/-- Recursion principle for `Additive`, supported by `cases` and `induction`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def rec {motive : Additive α → Sort*} (ofMul : ∀ a, motive (ofMul a)) : ∀ a, motive a :=
  fun a => ofMul (a.toMul)

end Additive

namespace Multiplicative

/-- Reinterpret `x : α` as an element of `Multiplicative α`. -/
@[implicit_reducible]
def ofAdd : α ≃ Multiplicative α :=
  ⟨ofAdd', toAdd', fun _ => rfl, fun _ => rfl⟩

/-- Reinterpret `x : Multiplicative α` as an element of `α`. -/
@[implicit_reducible]
def toAdd : Multiplicative α ≃ α := ofAdd.symm

@[simp]
theorem ofAdd_symm_eq : (@ofAdd α).symm = toAdd :=
  rfl

@[simp]
theorem toAdd_symm_eq : (@toAdd α).symm = ofAdd :=
  rfl

@[ext] lemma ext {a b : Multiplicative α} (hab : a.toAdd = b.toAdd) : a = b :=
  toAdd.injective hab

@[simp]
protected lemma «forall» {p : Multiplicative α → Prop} : (∀ a, p a) ↔ ∀ a, p (ofAdd a) :=
  ofAdd.forall_congr_right.symm

@[simp]
protected lemma «exists» {p : Multiplicative α → Prop} : (∃ a, p a) ↔ ∃ a, p (ofAdd a) :=
  ofAdd.exists_congr_right.symm

/-- Recursion principle for `Multiplicative`, supported by `cases` and `induction`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def rec {motive : Multiplicative α → Sort*} (ofAdd : ∀ a, motive (ofAdd a)) : ∀ a, motive a :=
  fun a => ofAdd (a.toAdd)

end Multiplicative

open Additive (ofMul toMul)
open Multiplicative (ofAdd toAdd)

@[simp]
theorem toAdd_ofAdd (x : α) : (ofAdd x).toAdd = x :=
  rfl

@[simp]
theorem ofAdd_toAdd (x : Multiplicative α) : ofAdd x.toAdd = x :=
  rfl

@[simp]
theorem toMul_ofMul (x : α) : (ofMul x).toMul = x :=
  rfl

@[simp]
theorem ofMul_toMul (x : Additive α) : ofMul x.toMul = x :=
  rfl

instance [Subsingleton α] : Subsingleton (Additive α) := toMul.injective.subsingleton
instance [Subsingleton α] : Subsingleton (Multiplicative α) := toAdd.injective.subsingleton

instance [Inhabited α] : Inhabited (Additive α) :=
  ⟨ofMul default⟩

instance [Inhabited α] : Inhabited (Multiplicative α) :=
  ⟨ofAdd default⟩

instance [Unique α] : Unique (Additive α) := toMul.unique
instance [Unique α] : Unique (Multiplicative α) := toAdd.unique

instance [DecidableEq α] : DecidableEq (Multiplicative α) := inferInstanceAs (DecidableEq α)

instance [DecidableEq α] : DecidableEq (Additive α) := inferInstanceAs (DecidableEq α)

instance Additive.instNontrivial [Nontrivial α] : Nontrivial (Additive α) :=
  ofMul.injective.nontrivial

instance Multiplicative.instNontrivial [Nontrivial α] : Nontrivial (Multiplicative α) :=
  ofAdd.injective.nontrivial

instance Additive.add [Mul α] : Add (Additive α) where
  add x y := ofMul (x.toMul * y.toMul)

instance Multiplicative.mul [Add α] : Mul (Multiplicative α) where
  mul x y := ofAdd (x.toAdd + y.toAdd)

@[simp]
theorem ofAdd_add [Add α] (x y : α) : ofAdd (x + y) = ofAdd x * ofAdd y := rfl

@[simp]
theorem toAdd_mul [Add α] (x y : Multiplicative α) : (x * y).toAdd = x.toAdd + y.toAdd := rfl

@[simp]
theorem ofMul_mul [Mul α] (x y : α) : ofMul (x * y) = ofMul x + ofMul y := rfl

@[simp]
theorem toMul_add [Mul α] (x y : Additive α) : (x + y).toMul = x.toMul * y.toMul := rfl

instance Additive.addSemigroup [Semigroup α] : AddSemigroup (Additive α) :=
  { Additive.add with add_assoc a b c := Additive.ext (mul_assoc a.toMul b.toMul c.toMul) }

instance Multiplicative.semigroup [AddSemigroup α] : Semigroup (Multiplicative α) :=
  { Multiplicative.mul with
    mul_assoc a b c := Multiplicative.ext (add_assoc a.toAdd b.toAdd c.toAdd) }

instance Additive.addCommSemigroup [CommSemigroup α] : AddCommSemigroup (Additive α) :=
  { Additive.addSemigroup with add_comm a b := Additive.ext (mul_comm a.toMul b.toMul) }

instance Multiplicative.commSemigroup [AddCommSemigroup α] : CommSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup with mul_comm a b := Multiplicative.ext (add_comm a.toAdd b.toAdd) }

instance Additive.isLeftCancelAdd [Mul α] [IsLeftCancelMul α] : IsLeftCancelAdd (Additive α) :=
  ⟨fun _ _ _ h ↦ Additive.ext (mul_left_cancel (congrArg (⇑toMul) h))⟩

instance Multiplicative.isLeftCancelMul [Add α] [IsLeftCancelAdd α] :
    IsLeftCancelMul (Multiplicative α) :=
  ⟨fun _ _ _ h ↦ Multiplicative.ext (add_left_cancel (congrArg (⇑toAdd) h))⟩

instance Additive.isRightCancelAdd [Mul α] [IsRightCancelMul α] : IsRightCancelAdd (Additive α) :=
  ⟨fun _ _ _ h ↦ Additive.ext (mul_right_cancel (congrArg (⇑toMul) h))⟩

instance Multiplicative.isRightCancelMul [Add α] [IsRightCancelAdd α] :
    IsRightCancelMul (Multiplicative α) :=
  ⟨fun _ _ _ h ↦ Multiplicative.ext (add_right_cancel (congrArg (⇑toAdd) h))⟩

instance Additive.isCancelAdd [Mul α] [IsCancelMul α] : IsCancelAdd (Additive α) :=
  ⟨⟩

instance Multiplicative.isCancelMul [Add α] [IsCancelAdd α] : IsCancelMul (Multiplicative α) :=
  ⟨⟩

instance Additive.addLeftCancelSemigroup [LeftCancelSemigroup α] :
    AddLeftCancelSemigroup (Additive α) :=
  { Additive.addSemigroup, Additive.isLeftCancelAdd with }

instance Multiplicative.leftCancelSemigroup [AddLeftCancelSemigroup α] :
    LeftCancelSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup, Multiplicative.isLeftCancelMul with }

instance Additive.addRightCancelSemigroup [RightCancelSemigroup α] :
    AddRightCancelSemigroup (Additive α) :=
  { Additive.addSemigroup, Additive.isRightCancelAdd with }

instance Multiplicative.rightCancelSemigroup [AddRightCancelSemigroup α] :
    RightCancelSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup, Multiplicative.isRightCancelMul with }

instance [One α] : Zero (Additive α) :=
  ⟨Additive.ofMul 1⟩

@[simp]
theorem ofMul_one [One α] : @Additive.ofMul α 1 = 0 := rfl

@[simp]
theorem ofMul_eq_zero {A : Type*} [One A] {x : A} : Additive.ofMul x = 0 ↔ x = 1 :=
  ⟨fun h ↦ ofMul.injective h, fun h ↦ h ▸ rfl⟩

@[simp]
theorem toMul_zero [One α] : (0 : Additive α).toMul = 1 := rfl

@[simp]
lemma toMul_eq_one {α : Type*} [One α] {x : Additive α} :
    x.toMul = 1 ↔ x = 0 :=
  ⟨fun h ↦ Additive.ext h, fun h ↦ h ▸ rfl⟩

instance [Zero α] : One (Multiplicative α) :=
  ⟨Multiplicative.ofAdd 0⟩

@[simp]
theorem ofAdd_zero [Zero α] : @Multiplicative.ofAdd α 0 = 1 :=
  rfl

@[simp]
theorem ofAdd_eq_one {A : Type*} [Zero A] {x : A} : Multiplicative.ofAdd x = 1 ↔ x = 0 :=
  ⟨fun h ↦ ofAdd.injective h, fun h ↦ h ▸ rfl⟩

@[simp]
theorem toAdd_one [Zero α] : (1 : Multiplicative α).toAdd = 0 :=
  rfl

@[simp]
lemma toAdd_eq_zero {α : Type*} [Zero α] {x : Multiplicative α} :
    x.toAdd = 0 ↔ x = 1 :=
  ⟨fun h ↦ Multiplicative.ext h, fun h ↦ h ▸ rfl⟩

instance Additive.addZeroClass [MulOneClass α] : AddZeroClass (Additive α) where
  zero_add a := Additive.ext (one_mul a.toMul)
  add_zero a := Additive.ext (mul_one a.toMul)

instance Multiplicative.mulOneClass [AddZeroClass α] : MulOneClass (Multiplicative α) where
  one_mul a := Multiplicative.ext (zero_add a.toAdd)
  mul_one a := Multiplicative.ext (add_zero a.toAdd)

instance Additive.addMonoid [h : Monoid α] : AddMonoid (Additive α) where
  nsmul n a := ofMul (a.toMul ^ n)
  nsmul_zero a := Additive.ext (h.npow_zero a.toMul)
  nsmul_succ n a := Additive.ext (h.npow_succ n a.toMul)

instance Multiplicative.monoid [h : AddMonoid α] : Monoid (Multiplicative α) where
  npow n a := ofAdd (n • a.toAdd)
  npow_zero a := Multiplicative.ext (h.nsmul_zero a.toAdd)
  npow_succ n a := Multiplicative.ext (h.nsmul_succ n a.toAdd)

@[simp]
theorem ofMul_pow [Monoid α] (n : ℕ) (a : α) : ofMul (a ^ n) = n • ofMul a :=
  rfl

@[simp]
theorem toMul_nsmul [Monoid α] (n : ℕ) (a : Additive α) : (n • a).toMul = a.toMul ^ n :=
  rfl

@[simp]
theorem ofAdd_nsmul [AddMonoid α] (n : ℕ) (a : α) : ofAdd (n • a) = ofAdd a ^ n :=
  rfl

@[simp]
theorem toAdd_pow [AddMonoid α] (a : Multiplicative α) (n : ℕ) : (a ^ n).toAdd = n • a.toAdd :=
  rfl

section Monoid
variable [Monoid α]

@[simp]
lemma isAddLeftRegular_ofMul {a : α} : IsAddLeftRegular (Additive.ofMul a) ↔ IsLeftRegular a :=
  ⟨fun h _ _ hxy ↦ ofMul.injective (h (congrArg (⇑ofMul) hxy)),
    fun h _ _ hxy ↦ toMul.injective (h (congrArg (⇑toMul) hxy))⟩

@[simp]
lemma isLeftRegular_toMul {a : Additive α} : IsLeftRegular a.toMul ↔ IsAddLeftRegular a :=
  isAddLeftRegular_ofMul.symm

@[simp]
lemma isAddRightRegular_ofMul {a : α} : IsAddRightRegular (Additive.ofMul a) ↔ IsRightRegular a :=
  ⟨fun h _ _ hxy ↦ ofMul.injective (h (congrArg (⇑ofMul) hxy)),
    fun h _ _ hxy ↦ toMul.injective (h (congrArg (⇑toMul) hxy))⟩

@[simp]
lemma isRightRegular_toMul {a : Additive α} : IsRightRegular a.toMul ↔ IsAddRightRegular a :=
  isAddRightRegular_ofMul.symm

@[simp] lemma isAddRegular_ofMul {a : α} : IsAddRegular (Additive.ofMul a) ↔ IsRegular a := by
  simp [isAddRegular_iff, isRegular_iff]

@[simp] lemma isRegular_toMul {a : Additive α} : IsRegular a.toMul ↔ IsAddRegular a := by
  simp [isAddRegular_iff, isRegular_iff]

end Monoid

section AddMonoid
variable [AddMonoid α]

@[simp]
lemma isLeftRegular_ofAdd {a : α} : IsLeftRegular (Multiplicative.ofAdd a) ↔ IsAddLeftRegular a :=
  ⟨fun h _ _ hxy ↦ ofAdd.injective (h (congrArg (⇑ofAdd) hxy)),
    fun h _ _ hxy ↦ toAdd.injective (h (congrArg (⇑toAdd) hxy))⟩

@[simp]
lemma isAddLeftRegular_toAdd {a : Multiplicative α} : IsAddLeftRegular a.toAdd ↔ IsLeftRegular a :=
  isLeftRegular_ofAdd.symm

@[simp]
lemma isRightRegular_ofAdd {a : α} :
    IsRightRegular (Multiplicative.ofAdd a) ↔ IsAddRightRegular a :=
  ⟨fun h _ _ hxy ↦ ofAdd.injective (h (congrArg (⇑ofAdd) hxy)),
    fun h _ _ hxy ↦ toAdd.injective (h (congrArg (⇑toAdd) hxy))⟩

@[simp] lemma isAddRightRegular_toAdd {a : Multiplicative α} :
    IsAddRightRegular a.toAdd ↔ IsRightRegular a :=
  isRightRegular_ofAdd.symm

@[simp] lemma isRegular_ofAdd {a : α} : IsRegular (Multiplicative.ofAdd a) ↔ IsAddRegular a := by
  simp [isAddRegular_iff, isRegular_iff]

@[simp] lemma isAddRegular_toAdd {a : Multiplicative α} : IsAddRegular a.toAdd ↔ IsRegular a := by
  simp [isAddRegular_iff, isRegular_iff]

end AddMonoid

instance Additive.addLeftCancelMonoid [LeftCancelMonoid α] : AddLeftCancelMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addLeftCancelSemigroup with }

instance Multiplicative.leftCancelMonoid [AddLeftCancelMonoid α] :
    LeftCancelMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.leftCancelSemigroup with }

instance Additive.addRightCancelMonoid [RightCancelMonoid α] : AddRightCancelMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addRightCancelSemigroup with }

instance Multiplicative.rightCancelMonoid [AddRightCancelMonoid α] :
    RightCancelMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.rightCancelSemigroup with }

instance Additive.addCommMonoid [CommMonoid α] : AddCommMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addCommSemigroup with }

instance Multiplicative.commMonoid [AddCommMonoid α] : CommMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.commSemigroup with }

instance Additive.instAddCancelCommMonoid [CancelCommMonoid α] :
    AddCancelCommMonoid (Additive α) where

instance Multiplicative.instCancelCommMonoid [AddCancelCommMonoid α] :
    CancelCommMonoid (Multiplicative α) where

instance Additive.neg [Inv α] : Neg (Additive α) :=
  ⟨fun x => ofMul x.toMul⁻¹⟩

@[simp]
theorem ofMul_inv [Inv α] (x : α) : ofMul x⁻¹ = -ofMul x :=
  rfl

@[simp]
theorem toMul_neg [Inv α] (x : Additive α) : (-x).toMul = x.toMul⁻¹ :=
  rfl

instance Multiplicative.inv [Neg α] : Inv (Multiplicative α) :=
  ⟨fun x => ofAdd (-x.toAdd)⟩

@[simp]
theorem ofAdd_neg [Neg α] (x : α) : ofAdd (-x) = (ofAdd x)⁻¹ :=
  rfl

@[simp]
theorem toAdd_inv [Neg α] (x : Multiplicative α) : x⁻¹.toAdd = -x.toAdd :=
  rfl

instance Additive.sub [Div α] : Sub (Additive α) where
  sub x y := ofMul (x.toMul / y.toMul)

instance Multiplicative.div [Sub α] : Div (Multiplicative α) where
  div x y := ofAdd (x.toAdd - y.toAdd)

@[simp]
theorem ofAdd_sub [Sub α] (x y : α) : ofAdd (x - y) = ofAdd x / ofAdd y :=
  rfl

@[simp]
theorem toAdd_div [Sub α] (x y : Multiplicative α) : (x / y).toAdd = x.toAdd - y.toAdd :=
  rfl

@[simp]
theorem ofMul_div [Div α] (x y : α) : ofMul (x / y) = ofMul x - ofMul y :=
  rfl

@[simp]
theorem toMul_sub [Div α] (x y : Additive α) : (x - y).toMul = x.toMul / y.toMul :=
  rfl

instance Additive.involutiveNeg [InvolutiveInv α] : InvolutiveNeg (Additive α) :=
  { Additive.neg with neg_neg a := Additive.ext (inv_inv a.toMul) }

instance Multiplicative.involutiveInv [InvolutiveNeg α] : InvolutiveInv (Multiplicative α) :=
  { Multiplicative.inv with inv_inv a := Multiplicative.ext (neg_neg a.toAdd) }

instance Additive.subNegMonoid [h : DivInvMonoid α] : SubNegMonoid (Additive α) where
  sub_eq_add_neg a b := Additive.ext (h.div_eq_mul_inv a.toMul b.toMul)
  zsmul n a := ofMul (a.toMul ^ n)
  zsmul_zero' a := Additive.ext (h.zpow_zero' a.toMul)
  zsmul_succ' n a := Additive.ext (h.zpow_succ' n a.toMul)
  zsmul_neg' n a := Additive.ext (h.zpow_neg' n a.toMul)

instance Multiplicative.divInvMonoid [h : SubNegMonoid α] : DivInvMonoid (Multiplicative α) where
  div_eq_mul_inv a b := Multiplicative.ext (h.sub_eq_add_neg a.toAdd b.toAdd)
  zpow n a := ofAdd (n • a.toAdd)
  zpow_zero' a := Multiplicative.ext (h.zsmul_zero' a.toAdd)
  zpow_succ' n a := Multiplicative.ext (h.zsmul_succ' n a.toAdd)
  zpow_neg' n a := Multiplicative.ext (h.zsmul_neg' n a.toAdd)

@[simp]
theorem ofMul_zpow [DivInvMonoid α] (z : ℤ) (a : α) : ofMul (a ^ z) = z • ofMul a :=
  rfl

@[simp]
theorem toMul_zsmul [DivInvMonoid α] (z : ℤ) (a : Additive α) : (z • a).toMul = a.toMul ^ z :=
  rfl

@[simp]
theorem ofAdd_zsmul [SubNegMonoid α] (z : ℤ) (a : α) : ofAdd (z • a) = ofAdd a ^ z :=
  rfl

@[simp]
theorem toAdd_zpow [SubNegMonoid α] (a : Multiplicative α) (z : ℤ) : (a ^ z).toAdd = z • a.toAdd :=
  rfl

instance Additive.subtractionMonoid [DivisionMonoid α] : SubtractionMonoid (Additive α) :=
  { Additive.subNegMonoid, Additive.involutiveNeg with
    neg_add_rev a b := Additive.ext (mul_inv_rev a.toMul b.toMul)
    neg_eq_of_add _ _ h := Additive.ext (inv_eq_of_mul_eq_one_right (congrArg (⇑toMul) h)) }

instance Multiplicative.divisionMonoid [SubtractionMonoid α] : DivisionMonoid (Multiplicative α) :=
  { Multiplicative.divInvMonoid, Multiplicative.involutiveInv with
    mul_inv_rev a b := Multiplicative.ext (neg_add_rev a.toAdd b.toAdd)
    inv_eq_of_mul _ _ h := Multiplicative.ext (neg_eq_of_add_eq_zero_right (congrArg (⇑toAdd) h)) }

instance Additive.subtractionCommMonoid [DivisionCommMonoid α] :
    SubtractionCommMonoid (Additive α) :=
  { Additive.subtractionMonoid, Additive.addCommSemigroup with }

instance Multiplicative.divisionCommMonoid [SubtractionCommMonoid α] :
    DivisionCommMonoid (Multiplicative α) :=
  { Multiplicative.divisionMonoid, Multiplicative.commSemigroup with }

instance Additive.addGroup [Group α] : AddGroup (Additive α) :=
  { Additive.subNegMonoid with neg_add_cancel a := Additive.ext (inv_mul_cancel a.toMul) }

instance Multiplicative.group [AddGroup α] : Group (Multiplicative α) :=
  { Multiplicative.divInvMonoid with
    inv_mul_cancel a := Multiplicative.ext (neg_add_cancel a.toAdd) }

instance Additive.addCommGroup [CommGroup α] : AddCommGroup (Additive α) :=
  { Additive.addGroup, Additive.addCommMonoid with }

instance Multiplicative.commGroup [AddCommGroup α] : CommGroup (Multiplicative α) :=
  { Multiplicative.group, Multiplicative.commMonoid with }

instance [Monoid α] [IsMulTorsionFree α] : IsAddTorsionFree (Additive α) where
  nsmul_right_injective _ hn _ _ h := Additive.ext (pow_left_injective hn (congrArg (⇑toMul) h))

instance [AddMonoid α] [IsAddTorsionFree α] : IsMulTorsionFree (Multiplicative α) where
  pow_left_injective _ hn _ _ h :=
    Multiplicative.ext (nsmul_right_injective hn (congrArg (⇑toAdd) h))

/-- If `α` has some multiplicative structure and coerces to a function,
then `Additive α` should also coerce to the same function.

This allows `Additive` to be used on bundled function types with a multiplicative structure, which
is often used for composition, without affecting the behavior of the function itself.
-/
instance Additive.coeToFun {α : Type*} {β : α → Sort*} [CoeFun α β] :
    CoeFun (Additive α) fun a => β a.toMul :=
  ⟨fun a => CoeFun.coe a.toMul⟩

/-- If `α` has some additive structure and coerces to a function,
then `Multiplicative α` should also coerce to the same function.

This allows `Multiplicative` to be used on bundled function types with an additive structure, which
is often used for composition, without affecting the behavior of the function itself.
-/
instance Multiplicative.coeToFun {α : Type*} {β : α → Sort*} [CoeFun α β] :
    CoeFun (Multiplicative α) fun a => β a.toAdd :=
  ⟨fun a => CoeFun.coe a.toAdd⟩

lemma Pi.mulSingle_multiplicativeOfAdd_eq {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [(i : ι) → AddMonoid (M i)] (i : ι) (a : M i) (j : ι) :
    Pi.mulSingle (M := fun i ↦ Multiplicative (M i)) i (.ofAdd a) j = .ofAdd (Pi.single i a j) := by
  rcases eq_or_ne j i with rfl | h
  · simp only [mulSingle_eq_same, single_eq_same]
  · simp only [mulSingle, ne_eq, h, not_false_eq_true, Function.update_of_ne, one_apply, single,
      zero_apply, ofAdd_zero]

lemma Pi.single_additiveOfMul_eq {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [(i : ι) → Monoid (M i)] (i : ι) (a : M i) (j : ι) :
    Pi.single (M := fun i ↦ Additive (M i)) i (.ofMul a) j = .ofMul (Pi.mulSingle i a j) := by
  rcases eq_or_ne j i with rfl | h
  · simp only [mulSingle_eq_same, single_eq_same]
  · simp only [single, ne_eq, h, not_false_eq_true, Function.update_of_ne, zero_apply, mulSingle,
      one_apply, ofMul_one]
