/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Action.TransferInstance
public import Mathlib.Logic.Small.Defs

/-!
# Transfer group structures from `α` to `Shrink α`
-/

@[expose] public noncomputable section

universe v
variable {M α : Type*} [Small.{v} α]

namespace Shrink

@[to_additive] instance [One α] : One (Shrink.{v} α) := (equivShrink α).symm.one
@[to_additive] instance [Mul α] : Mul (Shrink.{v} α) := (equivShrink α).symm.mul
@[to_additive] instance [Div α] : Div (Shrink.{v} α) := (equivShrink α).symm.div
@[to_additive] instance [Inv α] : Inv (Shrink.{v} α) := (equivShrink α).symm.Inv
@[to_additive] instance [Pow α M] : Pow (Shrink.{v} α) M := (equivShrink α).symm.pow M

end Shrink

@[to_additive (attr := simp)]
lemma equivShrink_symm_one [One α] : (equivShrink α).symm 1 = 1 :=
  (equivShrink α).symm_apply_apply 1

@[to_additive (attr := simp)]
lemma equivShrink_symm_mul [Mul α] (x y : Shrink α) :
    (equivShrink α).symm (x * y) = (equivShrink α).symm x * (equivShrink α).symm y := by
  simp [Equiv.mul_def]

@[to_additive (attr := simp)]
lemma equivShrink_mul [Mul α] (x y : α) :
    equivShrink α (x * y) = equivShrink α x * equivShrink α y := by
  simp [Equiv.mul_def]

@[simp]
lemma equivShrink_symm_smul {M : Type*} [SMul M α] (m : M) (x : Shrink α) :
    (equivShrink α).symm (m • x) = m • (equivShrink α).symm x := by
  simp [Equiv.smul_def]

@[simp]
lemma equivShrink_smul {M : Type*} [SMul M α] (m : M) (x : α) :
    equivShrink α (m • x) = m • equivShrink α x := by
  simp [Equiv.smul_def]
@[to_additive (attr := simp)]
lemma equivShrink_symm_div [Div α] (x y : Shrink α) :
    (equivShrink α).symm (x / y) = (equivShrink α).symm x / (equivShrink α).symm y := by
  simp [Equiv.div_def]

@[to_additive (attr := simp)]
lemma equivShrink_div [Div α] (x y : α) :
    equivShrink α (x / y) = equivShrink α x / equivShrink α y := by
  simp [Equiv.div_def]

@[to_additive (attr := simp)]
lemma equivShrink_symm_inv [Inv α] (x : Shrink α) :
    (equivShrink α).symm x⁻¹ = ((equivShrink α).symm x)⁻¹ := by
  simp [Equiv.inv_def]

@[to_additive (attr := simp)]
lemma equivShrink_inv [Inv α] (x : α) : equivShrink α x⁻¹ = (equivShrink α x)⁻¹ := by
  simp [Equiv.inv_def]

namespace Shrink

/-- Shrink `α` to a smaller universe preserves multiplication. -/
@[to_additive (attr := simps!) /-- Shrink `α` to a smaller universe preserves addition. -/]
def mulEquiv [Mul α] : Shrink.{v} α ≃* α := (equivShrink α).symm.mulEquiv

@[to_additive]
instance [Semigroup α] : Semigroup (Shrink.{v} α) := fast_instance% (equivShrink α).symm.semigroup

@[to_additive]
instance [CommSemigroup α] : CommSemigroup (Shrink.{v} α) :=
  fast_instance% (equivShrink α).symm.commSemigroup

@[to_additive]
instance [Mul α] [IsLeftCancelMul α] : IsLeftCancelMul (Shrink.{v} α) :=
  (equivShrink α).symm.isLeftCancelMul

@[to_additive]
instance [Mul α] [IsRightCancelMul α] : IsRightCancelMul (Shrink.{v} α) :=
  (equivShrink α).symm.isRightCancelMul

@[to_additive]
instance [Mul α] [IsCancelMul α] : IsCancelMul (Shrink.{v} α) := (equivShrink α).symm.isCancelMul

@[to_additive]
instance [MulOneClass α] : MulOneClass (Shrink.{v} α) :=
  fast_instance% (equivShrink α).symm.mulOneClass

@[to_additive]
instance [Monoid α] : Monoid (Shrink.{v} α) :=
  fast_instance% (equivShrink α).symm.monoid

@[to_additive]
instance [CommMonoid α] : CommMonoid (Shrink.{v} α) :=
  fast_instance% (equivShrink α).symm.commMonoid

@[to_additive]
instance [Group α] : Group (Shrink.{v} α) :=
  fast_instance% (equivShrink α).symm.group

/-- Pack congruence for `Shrink.mulEquiv`. -/
@[dsimp_congr] theorem _root_.Shrink.mulEquiv_pack_congr.{va, ua} {α α' : Type ua}
    [s : Small.{va} α] [s' : Small.{va} α'] [i : Mul α] [i' : Mul α']
    (h : @ClassPack.mk Mul α i = @ClassPack.mk Mul α' i') :
    HEq (Shrink.mulEquiv.{va} (α := α)) (Shrink.mulEquiv.{va} (α := α')) := by
  cases h; rfl

/-- Lens: the `Mul` pack of `Shrink α` follows the `Mul` pack of `α`. -/
@[dsimp_congr] theorem _root_.Shrink.instMul.packLens.{va, ua} {α α' : Type ua}
    [s : Small.{va} α] [s' : Small.{va} α'] [i : Mul α] [i' : Mul α']
    (h : @ClassPack.mk Mul α i = @ClassPack.mk Mul α' i') :
    @ClassPack.mk Mul (Shrink.{va} α) Shrink.instMul =
      @ClassPack.mk Mul (Shrink.{va} α') Shrink.instMul := by
  cases h; rfl

/-- Lens: the `MulOneClass` pack of `Shrink α` follows the `MulOneClass` pack of `α`. -/
@[dsimp_congr] theorem _root_.Shrink.instMulOneClass.packLens.{va, ua} {α α' : Type ua}
    [s : Small.{va} α] [s' : Small.{va} α'] [i : MulOneClass α] [i' : MulOneClass α']
    (h : @ClassPack.mk MulOneClass α i = @ClassPack.mk MulOneClass α' i') :
    @ClassPack.mk MulOneClass (Shrink.{va} α) Shrink.instMulOneClass =
      @ClassPack.mk MulOneClass (Shrink.{va} α') Shrink.instMulOneClass := by
  cases h; rfl

/-- Lens: the `Group` pack of `Shrink α` follows the `Group` pack of `α`. -/
@[dsimp_congr] theorem _root_.Shrink.instGroup.packLens.{va, ua} {α α' : Type ua}
    [s : Small.{va} α] [s' : Small.{va} α'] [i : Group α] [i' : Group α']
    (h : @ClassPack.mk Group α i = @ClassPack.mk Group α' i') :
    @ClassPack.mk Group (Shrink.{va} α) Shrink.instGroup =
      @ClassPack.mk Group (Shrink.{va} α') Shrink.instGroup := by
  cases h; rfl

@[to_additive]
instance [CommGroup α] : CommGroup (Shrink.{v} α) :=
  fast_instance% (equivShrink α).symm.commGroup

@[to_additive]
instance [Monoid M] [MulAction M α] : MulAction M (Shrink.{v} α) :=
  (equivShrink α).symm.mulAction M

end Shrink
