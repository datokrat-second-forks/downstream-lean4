/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-! # Bundled ordered monoid structures on `Multiplicative α` and `Additive α`. -/

public section

variable {α : Type*}

instance Multiplicative.isOrderedMonoid [AddCommMonoid α] [Preorder α] [IsOrderedAddMonoid α] :
    IsOrderedMonoid (Multiplicative α) where
  mul_le_mul_left a b h c := IsOrderedAddMonoid.add_le_add_left a.toAdd b.toAdd h c.toAdd

instance Additive.isOrderedAddMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] :
    IsOrderedAddMonoid (Additive α) where
  add_le_add_left a b h c := IsOrderedMonoid.mul_le_mul_left a.toMul b.toMul h c.toMul

instance Multiplicative.isOrderedCancelMonoid
    [AddCommMonoid α] [Preorder α] [IsOrderedCancelAddMonoid α] :
    IsOrderedCancelMonoid (Multiplicative α) where
  le_of_mul_le_mul_left a b c h :=
    IsOrderedCancelAddMonoid.le_of_add_le_add_left a.toAdd b.toAdd c.toAdd h

instance Additive.isOrderedCancelAddMonoid
    [CommMonoid α] [Preorder α] [IsOrderedCancelMonoid α] :
    IsOrderedCancelAddMonoid (Additive α) where
  le_of_add_le_add_left a b c h :=
    IsOrderedCancelMonoid.le_of_mul_le_mul_left a.toMul b.toMul c.toMul h

instance Multiplicative.canonicallyOrderedMul
    [AddMonoid α] [Preorder α] [CanonicallyOrderedAdd α] :
    CanonicallyOrderedMul (Multiplicative α) where
  le_mul_self _ _ := le_add_self (α := α)
  le_self_mul _ _ := le_self_add (α := α)

instance Additive.canonicallyOrderedAdd
    [Monoid α] [Preorder α] [CanonicallyOrderedMul α] :
    CanonicallyOrderedAdd (Additive α) where
  le_add_self _ _ := le_mul_self (α := α)
  le_self_add _ _ := le_self_mul (α := α)
