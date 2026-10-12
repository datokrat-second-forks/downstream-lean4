/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Order.Hom.Basic

/-!
# Order isomorphisms for the type tags

`Additive α` and `Multiplicative α` carry the order transported from `α`. This file bundles
that transport as an `OrderIso`, which is what the various order-theoretic constructions
(`SuccOrder`, `LocallyFiniteOrder`, ...) need in order to be carried across.

This material cannot live in `Mathlib/Algebra/Order/Monoid/Unbundled/TypeTags.lean`, where the
order structures themselves are defined, because `≃o` is not available there.
-/

public section

variable {X : Type*}

namespace Additive

/-- `Additive.ofMul` as an order isomorphism. -/
@[expose]
def ofMulOrderIso [Preorder X] : X ≃o Additive X where
  toEquiv := ofMul
  map_rel_iff' := Iff.rfl

/-- `Additive.toMul` as an order isomorphism. -/
@[expose]
def toMulOrderIso [Preorder X] : Additive X ≃o X where
  toEquiv := toMul
  map_rel_iff' := Iff.rfl

end Additive

namespace Multiplicative

/-- `Multiplicative.ofAdd` as an order isomorphism. -/
@[expose]
def ofAddOrderIso [Preorder X] : X ≃o Multiplicative X where
  toEquiv := ofAdd
  map_rel_iff' := Iff.rfl

/-- `Multiplicative.toAdd` as an order isomorphism. -/
@[expose]
def toAddOrderIso [Preorder X] : Multiplicative X ≃o X where
  toEquiv := toAdd
  map_rel_iff' := Iff.rfl

end Multiplicative
