import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Algebra.Monoid

/-!
Tests for the `newtype`-sealed `Additive` and `Multiplicative`: `Additive α` is a type of its own,
distinct from `α`; the conversions are inverse by `rfl`; the operations reduce to the ones of `α`;
and the transported order, topology and metric agree with the ones the algebra builds on.
-/

open Additive Multiplicative

variable {α : Type*}

/-! Crossing the seal needs the conversions. -/

example (x : α) : Additive α := by
  fail_if_success exact x
  exact ofMul x
example (x : Additive α) : α := by
  fail_if_success exact x
  exact x.toMul
example (x : α) : Multiplicative α := by
  fail_if_success exact x
  exact ofAdd x
example (x : Multiplicative α) : α := by
  fail_if_success exact x
  exact x.toAdd
example (x : Multiplicative (Additive α)) : α := by
  fail_if_success exact x
  exact x.toAdd.toMul

example (x : α) : (ofMul x).toMul = x := rfl
example (x : Additive α) : ofMul x.toMul = x := rfl
example (x : α) : (ofAdd x).toAdd = x := rfl
example (x : Multiplicative α) : ofAdd x.toAdd = x := rfl

/-! The operations are the ones of `α`. -/

example [Mul α] (x y : α) : ofMul x + ofMul y = ofMul (x * y) := rfl
example [One α] : (0 : Additive α) = ofMul 1 := rfl
example [Add α] (x y : α) : ofAdd x * ofAdd y = ofAdd (x + y) := rfl
example [Monoid α] (n : ℕ) (x : α) : n • ofMul x = ofMul (x ^ n) := rfl
example [AddMonoid α] (n : ℕ) (x : α) : ofAdd x ^ n = ofAdd (n • x) := rfl

/-! The transported order and topology reduce to the ones of `α`. -/

example [LE α] (x y : Additive α) : x ≤ y ↔ x.toMul ≤ y.toMul := Iff.rfl
example [LT α] (x y : Multiplicative α) : x < y ↔ x.toAdd < y.toAdd := Iff.rfl
example [LinearOrder α] (x y : Additive α) : min x y = ofMul (min x.toMul y.toMul) := rfl
example [LinearOrder α] (x y : Multiplicative α) : max x y = ofAdd (max x.toAdd y.toAdd) := rfl

example [TopologicalSpace α] (s : Set (Additive α)) : IsOpen (ofMul ⁻¹' s) ↔ IsOpen s := Iff.rfl
example [TopologicalSpace α] (s : Set (Multiplicative α)) :
    IsOpen (ofAdd ⁻¹' s) ↔ IsOpen s := Iff.rfl

/-! Diamonds: the metric and topology that the algebra builds on are the transported ones. -/

section Diamonds

variable {E : Type*}

example [SeminormedGroup E] :
    (SeminormedAddGroup.toPseudoMetricSpace : PseudoMetricSpace (Additive E)) =
      inferInstanceAs (PseudoMetricSpace E) := by
  with_reducible_and_instances rfl
example [SeminormedAddGroup E] :
    (SeminormedGroup.toPseudoMetricSpace : PseudoMetricSpace (Multiplicative E)) =
      inferInstanceAs (PseudoMetricSpace E) := by
  with_reducible_and_instances rfl
example [SeminormedGroup E] :
    (PseudoMetricSpace.toUniformSpace.toTopologicalSpace : TopologicalSpace (Additive E)) =
      inferInstanceAs (TopologicalSpace E) := by
  with_reducible_and_instances rfl
example [SeminormedCommGroup E] :
    (SeminormedAddCommGroup.toSeminormedAddGroup : SeminormedAddGroup (Additive E)) =
      Additive.seminormedAddGroup := by
  with_reducible_and_instances rfl
example [NormedGroup E] :
    (NormedAddGroup.toSeminormedAddGroup : SeminormedAddGroup (Additive E)) =
      Additive.seminormedAddGroup := by
  with_reducible_and_instances rfl
example [LinearOrder α] :
    (LinearOrder.toPartialOrder.toPreorder.toLE : LE (Additive α)) =
      inferInstanceAs (LE α) := by
  with_reducible_and_instances rfl

end Diamonds
