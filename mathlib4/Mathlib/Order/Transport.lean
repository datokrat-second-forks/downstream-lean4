/-
Copyright (c) 2026 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import Mathlib.Order.BoundedOrder.Basic

/-!
# Transporting order structures

`@[transport]` congruences for the order classes, so that `inferInstanceAs` and `deriving` carry
them across a `+defeq` structure whose order is that of its representation, such as `Additive α`.
The relations are those of `LE.canonicalCongr` and `LT.canonicalCongr`, so that transport unfolds
them, and diamonds between separately transported instances close by unfolding.

A synonym with a different order, such as `αᵒᵈ`, defines its instances by hand instead.
-/

public section

variable {α β : Type*}

/-- `Preorder` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev Preorder.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (Preorder α) (Preorder β) where
  toFun i :=
    { (LE.canonicalCongr e).toFun i.toLE, (LT.canonicalCongr e).toFun i.toLT with
      le_refl x := i.le_refl (e.invFun x)
      le_trans x y z := i.le_trans (e.invFun x) (e.invFun y) (e.invFun z)
      lt_iff_le_not_ge x y := i.lt_iff_le_not_ge (e.invFun x) (e.invFun y) }
  invFun i :=
    { (LE.canonicalCongr e).invFun i.toLE, (LT.canonicalCongr e).invFun i.toLT with
      le_refl x := i.le_refl (e.toFun x)
      le_trans x y z := i.le_trans (e.toFun x) (e.toFun y) (e.toFun z)
      lt_iff_le_not_ge x y := i.lt_iff_le_not_ge (e.toFun x) (e.toFun y) }
  left_inv i := Preorder.toLE_injective ((LE.canonicalCongr e).left_inv i.toLE)
  right_inv i := Preorder.toLE_injective ((LE.canonicalCongr e).right_inv i.toLE)

/-- `PartialOrder` instances correspond along a canonical equivalence. -/
@[transport]
protected abbrev PartialOrder.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (PartialOrder α) (PartialOrder β) where
  toFun i :=
    { (Preorder.canonicalCongr e).toFun i.toPreorder with
      le_antisymm _ _ hxy hyx := e.invFun_injective (i.le_antisymm _ _ hxy hyx) }
  invFun i :=
    { (Preorder.canonicalCongr e).invFun i.toPreorder with
      le_antisymm _ _ hxy hyx := e.toFun_injective (i.le_antisymm _ _ hxy hyx) }
  left_inv i := PartialOrder.toPreorder_injective <|
    (Preorder.canonicalCongr e).left_inv i.toPreorder
  right_inv i := PartialOrder.toPreorder_injective <|
    (Preorder.canonicalCongr e).right_inv i.toPreorder

/-- `LinearOrder` instances correspond along a canonical equivalence. `min` and `max` are computed
on the other side, like the operations of the algebraic congruences. -/
@[transport]
protected abbrev LinearOrder.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (LinearOrder α) (LinearOrder β) where
  toFun i :=
    letI := (PartialOrder.canonicalCongr e).toFun i.toPartialOrder
    letI : DecidableLE β := fun x y ↦ i.toDecidableLE (e.invFun x) (e.invFun y)
    letI : DecidableLT β := fun x y ↦ i.toDecidableLT (e.invFun x) (e.invFun y)
    letI : DecidableEq β := fun x y ↦
      decidable_of_iff (e.invFun x = e.invFun y) e.invFun_injective.eq_iff
    { (Ord.canonicalCongr e).toFun i.toOrd with
      toDecidableLE := inferInstance
      toDecidableLT := inferInstance
      toDecidableEq := inferInstance
      min x y := e.toFun (i.min (e.invFun x) (e.invFun y))
      max x y := e.toFun (i.max (e.invFun x) (e.invFun y))
      le_total x y := i.le_total (e.invFun x) (e.invFun y)
      min_def x y := by
        refine (congrArg e.toFun (i.min_def _ _)).trans ((apply_ite e.toFun _ _ _).trans ?_)
        rw [e.right_inv, e.right_inv]
        rfl
      max_def x y := by
        refine (congrArg e.toFun (i.max_def _ _)).trans ((apply_ite e.toFun _ _ _).trans ?_)
        rw [e.right_inv, e.right_inv]
        rfl
      compare_eq_compareOfLessAndEq x y := by
        refine (i.compare_eq_compareOfLessAndEq _ _).trans ?_
        simp only [compareOfLessAndEq, e.invFun_injective.eq_iff]
        rfl }
  invFun i :=
    letI := (PartialOrder.canonicalCongr e).invFun i.toPartialOrder
    letI : DecidableLE α := fun x y ↦ i.toDecidableLE (e.toFun x) (e.toFun y)
    letI : DecidableLT α := fun x y ↦ i.toDecidableLT (e.toFun x) (e.toFun y)
    letI : DecidableEq α := fun x y ↦
      decidable_of_iff (e.toFun x = e.toFun y) e.toFun_injective.eq_iff
    { (Ord.canonicalCongr e).invFun i.toOrd with
      toDecidableLE := inferInstance
      toDecidableLT := inferInstance
      toDecidableEq := inferInstance
      min x y := e.invFun (i.min (e.toFun x) (e.toFun y))
      max x y := e.invFun (i.max (e.toFun x) (e.toFun y))
      le_total x y := i.le_total (e.toFun x) (e.toFun y)
      min_def x y := by
        refine (congrArg e.invFun (i.min_def _ _)).trans ((apply_ite e.invFun _ _ _).trans ?_)
        rw [e.left_inv, e.left_inv]
        rfl
      max_def x y := by
        refine (congrArg e.invFun (i.max_def _ _)).trans ((apply_ite e.invFun _ _ _).trans ?_)
        rw [e.left_inv, e.left_inv]
        rfl
      compare_eq_compareOfLessAndEq x y := by
        refine (i.compare_eq_compareOfLessAndEq _ _).trans ?_
        simp only [compareOfLessAndEq, e.toFun_injective.eq_iff]
        rfl }
  left_inv i := LinearOrder.toPartialOrder_injective <|
    (PartialOrder.canonicalCongr e).left_inv i.toPartialOrder
  right_inv i := LinearOrder.toPartialOrder_injective <|
    (PartialOrder.canonicalCongr e).right_inv i.toPartialOrder

/-- `Top` instances correspond along a canonical equivalence. -/
@[to_dual (attr := transport) /-- `Bot` instances correspond along a canonical equivalence. -/]
protected abbrev Top.canonicalCongr (e : Lean.CanonicalEquivalence α β) :
    Lean.CanonicalEquivalence (Top α) (Top β) where
  toFun i := ⟨e.toFun i.top⟩
  invFun i := ⟨e.invFun i.top⟩
  left_inv i := congrArg Top.mk (e.left_inv i.top)
  right_inv i := congrArg Top.mk (e.right_inv i.top)

@[to_dual]
theorem OrderTop.toTop_injective [LE α] :
    Function.Injective fun i : OrderTop α ↦ i.toTop := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

/-- `OrderTop` instances correspond along a canonical equivalence, for the transported order. -/
@[to_dual (attr := transport)
  /-- `OrderBot` instances correspond along a canonical equivalence, for the transported order. -/]
protected abbrev OrderTop.canonicalCongr (e : Lean.CanonicalEquivalence α β) [iβ : LE β]
    {iα : LE α} (hi : iα = (LE.canonicalCongr e).invFun iβ) :
    Lean.CanonicalEquivalence (OrderTop α) (OrderTop β) where
  toFun i :=
    { (Top.canonicalCongr e).toFun i.toTop with
      le_top x := by
        subst hi
        let := (LE.canonicalCongr e).invFun iβ
        have h : e.invFun x ≤ ⊤ := _root_.le_top
        change iβ.le (e.toFun (e.invFun x)) (e.toFun ⊤) at h
        rwa [e.right_inv] at h }
  invFun i :=
    { (Top.canonicalCongr e).invFun i.toTop with
      le_top x := by
        subst hi
        change iβ.le (e.toFun x) (e.toFun (e.invFun ⊤))
        rw [e.right_inv]
        exact _root_.le_top }
  left_inv i := OrderTop.toTop_injective ((Top.canonicalCongr e).left_inv i.toTop)
  right_inv i := OrderTop.toTop_injective ((Top.canonicalCongr e).right_inv i.toTop)

theorem BoundedOrder.toOrderTop_toOrderBot_injective [LE α] {i j : BoundedOrder α}
    (htop : i.toOrderTop = j.toOrderTop) (hbot : i.toOrderBot = j.toOrderBot) : i = j := by
  cases i; cases j; cases htop; cases hbot; rfl

/-- `BoundedOrder` instances correspond along a canonical equivalence, for the transported
order. -/
@[transport]
protected abbrev BoundedOrder.canonicalCongr (e : Lean.CanonicalEquivalence α β) [iβ : LE β]
    {iα : LE α} (hi : iα = (LE.canonicalCongr e).invFun iβ) :
    Lean.CanonicalEquivalence (BoundedOrder α) (BoundedOrder β) where
  toFun i :=
    { (OrderTop.canonicalCongr e hi).toFun i.toOrderTop,
      (OrderBot.canonicalCongr e hi).toFun i.toOrderBot with }
  invFun i :=
    { (OrderTop.canonicalCongr e hi).invFun i.toOrderTop,
      (OrderBot.canonicalCongr e hi).invFun i.toOrderBot with }
  left_inv i := BoundedOrder.toOrderTop_toOrderBot_injective
    ((OrderTop.canonicalCongr e hi).left_inv i.toOrderTop)
    ((OrderBot.canonicalCongr e hi).left_inv i.toOrderBot)
  right_inv i := BoundedOrder.toOrderTop_toOrderBot_injective
    ((OrderTop.canonicalCongr e hi).right_inv i.toOrderTop)
    ((OrderBot.canonicalCongr e hi).right_inv i.toOrderBot)
