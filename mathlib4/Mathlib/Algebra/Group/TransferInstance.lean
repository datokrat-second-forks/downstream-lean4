/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Ext
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Data.Fintype.Basic

/-!
# Transfer algebraic structures across `Equiv`s

In this file we prove lemmas of the following form: if `β` has a group structure and `α ≃ β`
then `α` has a group structure, and similarly for monoids, semigroups and so on.

### Implementation details

When adding new definitions that transfer type-classes across an equivalence, please use
`abbrev`. See note [reducible non-instances].
-/

@[expose] public section

assert_not_exists MonoidWithZero MulAction

library_note «instance transfer via equivalence» /--
For many type classes, we have a definition that lets us transfer instances from one type to another
using an equivalence, such as `Equiv.mul` for `Mul`.
Constructing data instances in this way is discouraged because the resulting data is inefficient
to unfold. To somewhat mitigate this problem, in these definitions we don't write the
projections on `Equiv` in the usual way using `Equiv.symm` and `DFunLike.coe`, and instead use
`Equiv.toFun` and `Equiv.invFun` directly. As a result, unification has to do less unfolding.

Note also that when constructing data instances in this way, it usually helps to use
`fast_instance%` to get a faster instance.
-/

namespace Equiv
variable {M α β : Type*} (e : α ≃ β)

-- See note [instance transfer via equivalence]
/-- Transfer `One` across an `Equiv` -/
@[to_additive /-- Transfer `Zero` across an `Equiv` -/]
protected abbrev one [One β] : One α where one := e.invFun 1

@[to_additive]
lemma one_def [One β] :
    letI := e.one
    1 = e.symm 1 := rfl

/-- Transfer `Mul` across an `Equiv` -/
@[to_additive /-- Transfer `Add` across an `Equiv` -/]
protected abbrev mul [Mul β] : Mul α where mul x y := e.invFun (e.toFun x * e.toFun y)

@[to_additive]
lemma mul_def [Mul β] (x y : α) :
    letI := Equiv.mul e
    x * y = e.symm (e x * e y) := rfl

/-- Transfer `Div` across an `Equiv` -/
@[to_additive /-- Transfer `Sub` across an `Equiv` -/]
protected abbrev div [Div β] : Div α :=
  ⟨fun x y => e.invFun (e.toFun x / e.toFun y)⟩

@[to_additive]
lemma div_def [Div β] (x y : α) :
    letI := Equiv.div e
    x / y = e.symm (e x / e y) := rfl

-- Porting note: this should be called `inv`,
-- but we already have an `Equiv.inv` (which perhaps should move to `Perm.inv`?)
/-- Transfer `Inv` across an `Equiv` -/
@[to_additive /-- Transfer `Neg` across an `Equiv` -/]
protected abbrev Inv [Inv β] : Inv α where inv x := e.invFun (e.toFun x)⁻¹

@[to_additive]
lemma inv_def [Inv β] (x : α) :
    letI := e.Inv
    x⁻¹ = e.symm (e x)⁻¹ := rfl

variable (M) in
/-- Transfer `Pow` across an `Equiv` -/
@[to_additive (attr := to_additive /-- Transfer `VAdd` across an `Equiv` -/) smul
/-- Transfer `SMul` across an `Equiv` -/]
protected abbrev pow [Pow β M] : Pow α M where pow x n := e.invFun (e.toFun x ^ n)

@[to_additive (attr := to_additive) smul_def]
lemma pow_def [Pow β M] (n : M) (x : α) :
    letI := e.pow M
    x ^ n = e.symm (e x ^ n) := rfl

/-- An equivalence `e : α ≃ β` gives a multiplicative equivalence `α ≃* β` where
the multiplicative structure on `α` is the one obtained by transporting a multiplicative structure
on `β` back along `e`. -/
@[to_additive /-- An equivalence `e : α ≃ β` gives an additive equivalence `α ≃+ β` where
the additive structure on `α` is the one obtained by transporting an additive structure
on `β` back along `e`. -/]
def mulEquiv (e : α ≃ β) [Mul β] :
    let _ := Equiv.mul e
    α ≃* β := by
  intros
  exact
    { e with
      map_mul' := fun x y => by
        simp [mul_def] }

@[to_additive (attr := simp)]
lemma mulEquiv_apply (e : α ≃ β) [Mul β] (a : α) : (mulEquiv e) a = e a := rfl

@[to_additive (attr := simp)]
lemma mulEquiv_symm_apply (e : α ≃ β) [Mul β] (b : β) :
    letI := Equiv.mul e
    (mulEquiv e).symm b = e.symm b := rfl

/-- Transfer `Semigroup` across an `Equiv` -/
@[to_additive /-- Transfer `add_semigroup` across an `Equiv` -/]
protected abbrev semigroup [Semigroup β] : Semigroup α := by
  let mul := e.mul
  apply e.injective.semigroup _; intros; exact e.apply_symm_apply _

/-- Transfer `CommSemigroup` across an `Equiv` -/
@[to_additive /-- Transfer `AddCommSemigroup` across an `Equiv` -/]
protected abbrev commSemigroup [CommSemigroup β] : CommSemigroup α := by
  let mul := e.mul
  apply e.injective.commSemigroup _; intros; exact e.apply_symm_apply _

/-- Transfer `IsLeftCancelMul` across an `Equiv` -/
@[to_additive /-- Transfer `IsLeftCancelAdd` across an `Equiv` -/]
protected lemma isLeftCancelMul [Mul β] [IsLeftCancelMul β] :
    letI := e.mul
    IsLeftCancelMul α := by
  let := e.mul; exact e.injective.isLeftCancelMul _ fun _ _ ↦ e.apply_symm_apply _

/-- Transfer `IsRightCancelMul` across an `Equiv` -/
@[to_additive /-- Transfer `IsRightCancelAdd` across an `Equiv` -/]
protected lemma isRightCancelMul [Mul β] [IsRightCancelMul β] :
    letI := e.mul
    IsRightCancelMul α := by
  let := e.mul; exact e.injective.isRightCancelMul _ fun _ _ ↦ e.apply_symm_apply _

/-- Transfer `IsCancelMul` across an `Equiv` -/
@[to_additive /-- Transfer `IsCancelAdd` across an `Equiv` -/]
protected lemma isCancelMul [Mul β] [IsCancelMul β] :
    letI := e.mul
    IsCancelMul α := by
  let := e.mul; exact e.injective.isCancelMul _ fun _ _ ↦ e.apply_symm_apply _

/-- Transfer `MulOneClass` across an `Equiv` -/
@[to_additive /-- Transfer `AddZeroClass` across an `Equiv` -/]
protected abbrev mulOneClass [MulOneClass β] : MulOneClass α := by
  let one := e.one
  let mul := e.mul
  apply e.injective.mulOneClass _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `Monoid` across an `Equiv` -/
@[to_additive /-- Transfer `AddMonoid` across an `Equiv` -/]
protected abbrev monoid [Monoid β] : Monoid α := by
  let one := e.one
  let mul := e.mul
  let pow := e.pow ℕ
  apply e.injective.monoid _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `CommMonoid` across an `Equiv` -/
@[to_additive /-- Transfer `AddCommMonoid` across an `Equiv` -/]
protected abbrev commMonoid [CommMonoid β] : CommMonoid α := by
  let one := e.one
  let mul := e.mul
  let pow := e.pow ℕ
  apply e.injective.commMonoid _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `Group` across an `Equiv` -/
@[to_additive /-- Transfer `AddGroup` across an `Equiv` -/]
protected abbrev group [Group β] : Group α := by
  let one := e.one
  let mul := e.mul
  let inv := e.Inv
  let div := e.div
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  apply e.injective.group _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `CommGroup` across an `Equiv` -/
@[to_additive /-- Transfer `AddCommGroup` across an `Equiv` -/]
protected abbrev commGroup [CommGroup β] : CommGroup α := by
  let one := e.one
  let mul := e.mul
  let inv := e.Inv
  let div := e.div
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  apply e.injective.commGroup _ <;> intros <;> exact e.apply_symm_apply _

end Equiv

variable {α β : Type*}

/-- `CommMonoid` instances correspond along a canonical equivalence. The operations are those of
`Mul.canonicalCongr` and `One.canonicalCongr`, so that transport unfolds them. -/
@[to_additive (attr := transport)
  /-- `AddCommMonoid` instances correspond along a canonical equivalence. The operations are those
  of `Add.canonicalCongr` and `Zero.canonicalCongr`, so that transport unfolds them. -/]
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

/-- `CommGroup` instances correspond along a canonical equivalence. The operations are those of
`Mul.canonicalCongr`, `One.canonicalCongr`, `Inv.canonicalCongr` and `Div.canonicalCongr`, so that
transport unfolds them. -/
@[to_additive (attr := transport)
  /-- `AddCommGroup` instances correspond along a canonical equivalence. The operations are those
  of `Add.canonicalCongr`, `Zero.canonicalCongr`, `Neg.canonicalCongr` and `Sub.canonicalCongr`, so
  that transport unfolds them. -/]
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

namespace Finite

/-- Any finite group in universe `u` is equivalent to some finite group in universe `v`. -/
@[to_additive
/-- Any finite group in universe `u` is equivalent to some finite group in universe `v`. -/]
lemma exists_type_univ_nonempty_mulEquiv.{u, v} (G : Type u) [Group G] [Finite G] :
    ∃ (G' : Type v) (_ : Group G') (_ : Fintype G'), Nonempty (G ≃* G') := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin G
  let f : Fin n ≃ ULift (Fin n) := Equiv.ulift.symm
  let e : G ≃ ULift (Fin n) := e.trans f
  let groupH : Group (ULift (Fin n)) := e.symm.group
  exact ⟨ULift (Fin n), groupH, inferInstance, ⟨MulEquiv.symm <| e.symm.mulEquiv⟩⟩

end Finite
