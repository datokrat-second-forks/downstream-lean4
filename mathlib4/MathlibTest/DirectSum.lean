import Mathlib.Algebra.DirectSum.Module

/-!
Tests for the `newtype`-sealed `DirectSum`: its transported instances reduce to the constructor and
projector, and the algebraic diamonds close with `with_reducible_and_instances rfl`.
-/

open DirectSum

variable {ι R : Type*} {β : ι → Type*}

section AddCommMonoid

variable [∀ i, AddCommMonoid (β i)]

example (x y : ⨁ i, β i) : x + y = ofDFinsupp (x.toDFinsupp + y.toDFinsupp) := by
  with_reducible_and_instances rfl
example : (0 : ⨁ i, β i) = ofDFinsupp 0 := by with_reducible_and_instances rfl
example (n : ℕ) (x : ⨁ i, β i) : n • x = ofDFinsupp (n • x.toDFinsupp) := by
  with_reducible_and_instances rfl
example (x : ⨁ i, β i) (i : ι) : x i = x.toDFinsupp i := by with_reducible_and_instances rfl

example : (NSMul.toSMul : SMul ℕ (⨁ i, β i)) = DirectSum.instSMulOfModule := by
  with_reducible_and_instances rfl

variable [Semiring R] [∀ i, Module R (β i)]

example (r : R) (x : ⨁ i, β i) : r • x = ofDFinsupp (r • x.toDFinsupp) := by
  with_reducible_and_instances rfl
example : (Module.toDistribMulAction.toMulAction.toSMul : SMul R (⨁ i, β i)) =
    DirectSum.instSMulOfModule := by
  with_reducible_and_instances rfl

end AddCommMonoid

section AddCommGroup

variable [∀ i, AddCommGroup (β i)]

example (x y : ⨁ i, β i) : x - y = ofDFinsupp (x.toDFinsupp - y.toDFinsupp) := by
  with_reducible_and_instances rfl
example (x : ⨁ i, β i) : -x = ofDFinsupp (-x.toDFinsupp) := by with_reducible_and_instances rfl

example : (AddCommGroup.toAddCommMonoid : AddCommMonoid (⨁ i, β i)) =
    instAddCommMonoidDirectSum ι β := by
  with_reducible_and_instances rfl

end AddCommGroup
