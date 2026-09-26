/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Data.Fintype.Basic

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

public section

assert_not_exists MonoidWithZero

namespace Equiv
variable {M N O α β : Type*}

variable (M) [Monoid M] in
/-- Transfer `MulAction` across an `Equiv` -/
@[to_additive /-- Transfer `AddAction` across an `Equiv` -/]
protected abbrev mulAction (e : α ≃ β) [MulAction M β] : MulAction M α where
  __ := e.smul M
  one_smul := by simp [smul_def]
  mul_smul := by simp [smul_def, mul_smul]

variable (M N) [SMul M β] [SMul N β] in
/-- Transfer `SMulCommClass` across an `Equiv` -/
@[to_additive /-- Transfer `VAddCommClass` across an `Equiv` -/]
protected lemma smulCommClass (e : α ≃ β) [SMulCommClass M N β] :
    letI := e.smul M
    letI := e.smul N
    SMulCommClass M N α :=
  letI := e.smul M
  letI := e.smul N
  { smul_comm := by simp [smul_def, smul_comm] }

variable (M N) [SMul M N] [SMul M β] [SMul N β] in
/-- Transfer `IsScalarTower` across an `Equiv` -/
@[to_additive /-- Transfer `VAddAssocClass` across an `Equiv` -/]
protected lemma isScalarTower (e : α ≃ β) [IsScalarTower M N β] :
    letI := e.smul M
    letI := e.smul N
    IsScalarTower M N α :=
  letI := e.smul M
  letI := e.smul N
  { smul_assoc := by simp [smul_def, smul_assoc] }

variable (M) [SMul M β] [SMul Mᵐᵒᵖ β] in
/-- Transfer `IsCentralScalar` across an `Equiv` -/
@[to_additive /-- Transfer `IsCentralVAdd` across an `Equiv` -/]
protected lemma isCentralScalar (e : α ≃ β) [IsCentralScalar M β] :
    letI := e.smul M
    letI := e.smul Mᵐᵒᵖ
    IsCentralScalar M α :=
  letI := e.smul M
  letI := e.smul Mᵐᵒᵖ
  { op_smul_eq_smul := by simp [smul_def, op_smul_eq_smul] }

variable (M) [Monoid M] [Monoid O] in
/-- Transfer `MulDistribMulAction` across an `Equiv` -/
protected abbrev mulDistribMulAction (e : N ≃ O) [MulDistribMulAction M O] :
    letI := e.monoid
    MulDistribMulAction M N :=
  letI := e.monoid
  { e.mulAction M with
    smul_one := by simp [one_def, smul_def, smul_one]
    smul_mul := by simp [mul_def, smul_def, smul_mul'] }

variable (M) [SMul M β] in
/-- Transfer `FaithfulSMul` across an `Equiv`.

See `FaithfulSMul.of_injective` for the general statement not about transferring. -/
@[to_additive /-- Transfer `FaithfulVAdd` across an `Equiv`

See `FaithfulVAdd.of_injective` for the general statement not about transferring. -/]
protected lemma faithfulSMul (e : α ≃ β) [FaithfulSMul M β] :
    letI := e.smul M
    FaithfulSMul M α :=
  letI := e.smul M
  { eq_of_smul_eq_smul {m₁ m₂} := by
      simpa [← e.forall_congr_right, smul_def] using eq_of_smul_eq_smul (α := β) }

end Equiv

variable {M N α β : Type*}

/-- `SMulCommClass` holds on both sides of a canonical equivalence, for the transported actions. -/
@[to_additive (attr := transport) /-- `VAddCommClass` holds on both sides of a canonical
equivalence, for the transported actions. -/]
protected abbrev SMulCommClass.canonicalCongr (e : Lean.CanonicalEquivalence α β)
    [iM : SMul M β] [iN : SMul N β] {iM' : SMul M α} {iN' : SMul N α}
    (hM : iM' = (SMul.canonicalCongr e).invFun iM) (hN : iN' = (SMul.canonicalCongr e).invFun iN) :
    Lean.CanonicalEquivalence (SMulCommClass M N α) (SMulCommClass M N β) := by
  subst hM hN
  letI := (SMul.canonicalCongr e).invFun iM
  letI := (SMul.canonicalCongr e).invFun iN
  exact {
    toFun _ := by
      rw [← (SMul.canonicalCongr e).right_inv iM, ← (SMul.canonicalCongr e).right_inv iN]
      exact e.toEquiv.symm.smulCommClass M N
    invFun _ := e.toEquiv.smulCommClass M N
    left_inv _ := rfl
    right_inv _ := rfl }

/-- `IsScalarTower` holds on both sides of a canonical equivalence, for the transported actions. -/
@[to_additive (attr := transport) /-- `VAddAssocClass` holds on both sides of a canonical
equivalence, for the transported actions. -/]
protected abbrev IsScalarTower.canonicalCongr [SMul M N] (e : Lean.CanonicalEquivalence α β)
    [iN : SMul N β] [iM : SMul M β] {iN' : SMul N α} {iM' : SMul M α}
    (hN : iN' = (SMul.canonicalCongr e).invFun iN) (hM : iM' = (SMul.canonicalCongr e).invFun iM) :
    Lean.CanonicalEquivalence (IsScalarTower M N α) (IsScalarTower M N β) := by
  subst hM hN
  letI := (SMul.canonicalCongr e).invFun iM
  letI := (SMul.canonicalCongr e).invFun iN
  exact {
    toFun _ := by
      rw [← (SMul.canonicalCongr e).right_inv iM, ← (SMul.canonicalCongr e).right_inv iN]
      exact e.toEquiv.symm.isScalarTower M N
    invFun _ := e.toEquiv.isScalarTower M N
    left_inv _ := rfl
    right_inv _ := rfl }

/-- `IsCentralScalar` holds on both sides of a canonical equivalence, for the transported
actions. -/
@[to_additive (attr := transport) /-- `IsCentralVAdd` holds on both sides of a canonical
equivalence, for the transported actions. -/]
protected abbrev IsCentralScalar.canonicalCongr (e : Lean.CanonicalEquivalence α β)
    [iM : SMul M β] [iM' : SMul Mᵐᵒᵖ β] {jM : SMul M α} {jM' : SMul Mᵐᵒᵖ α}
    (hM : jM = (SMul.canonicalCongr e).invFun iM) (hM' : jM' = (SMul.canonicalCongr e).invFun iM') :
    Lean.CanonicalEquivalence (IsCentralScalar M α) (IsCentralScalar M β) := by
  subst hM hM'
  letI := (SMul.canonicalCongr e).invFun iM
  letI := (SMul.canonicalCongr e).invFun iM'
  exact {
    toFun _ := by
      rw [← (SMul.canonicalCongr e).right_inv iM, ← (SMul.canonicalCongr e).right_inv iM']
      exact e.toEquiv.symm.isCentralScalar M
    invFun _ := e.toEquiv.isCentralScalar M
    left_inv _ := rfl
    right_inv _ := rfl }
