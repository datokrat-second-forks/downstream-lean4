/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.TransferInstance
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs

/-!
# Transfer algebraic structures across `Equiv`s or `AddEquiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

@[expose] public section

assert_not_exists Algebra

universe u v
variable {R α β : Type*} [Semiring R]

namespace Equiv
variable (e : α ≃ β)

variable (R : Type*) [Zero R] in
/-- Transfer `NoZeroSMulDivisors` across an `Equiv` -/
protected lemma noZeroSMulDivisors [Zero α] [Zero β] [SMul R β] [NoZeroSMulDivisors R β]
    (e : α ≃ β) (map_zero : e 0 = 0) :
    letI := e.smul R
    NoZeroSMulDivisors R α := by
  let := e.smul R
  refine ⟨fun {r} m ↦ ?_⟩
  simp_rw [e.eq_symm_apply.2 map_zero, eq_symm_apply, smul_def, apply_symm_apply]
  exact eq_zero_or_eq_zero_of_smul_eq_zero

end Equiv

/-- `Module` instances correspond along a canonical equivalence, over the transported additive
monoid. The action is that of `SMul.canonicalCongr`, so that transport unfolds it. -/
@[transport]
protected abbrev Module.canonicalCongr (e : Lean.CanonicalEquivalence α β) [iβ : AddCommMonoid β]
    {iα : AddCommMonoid α} (hi : iα = (AddCommMonoid.canonicalCongr e).invFun iβ) :
    Lean.CanonicalEquivalence (Module R α) (Module R β) where
  toFun i := @Function.Injective.module R α β _ iα i iβ ((SMul.canonicalCongr e).toFun i.toSMul)
    { toFun := e.invFun
      map_zero' := by subst hi; rfl
      map_add' x y := by
        subst hi
        change e.invFun (x + y) = e.invFun (e.toFun (e.invFun x) + e.toFun (e.invFun y))
        rw [e.toFun_invFun, e.toFun_invFun] }
    e.right_inv.injective fun _ _ ↦ e.left_inv _
  invFun i := @Function.Injective.module R β α _ iβ i iα ((SMul.canonicalCongr e).invFun i.toSMul)
    { toFun := e.toFun
      map_zero' := by subst hi; exact e.right_inv _
      map_add' _ _ := by subst hi; exact e.right_inv _ }
    e.left_inv.injective fun _ _ ↦ e.right_inv _
  left_inv _ := Module.ext' _ _ fun r x ↦
    show e.invFun (e.toFun (r • e.invFun (e.toFun x))) = r • x by rw [e.left_inv, e.left_inv]
  right_inv _ := Module.ext' _ _ fun r x ↦
    show e.toFun (e.invFun (r • e.toFun (e.invFun x))) = r • x by rw [e.right_inv, e.right_inv]

variable (R) in
/-- A canonical equivalence is linear for the module structure transported along it. -/
def Lean.CanonicalEquivalence.linearEquiv (e : Lean.CanonicalEquivalence α β) [AddCommMonoid β]
    [_root_.Module R β] :
    letI := (AddCommMonoid.canonicalCongr e).invFun ‹AddCommMonoid β›
    letI := (_root_.Module.canonicalCongr e rfl).invFun ‹_root_.Module R β›
    α ≃ₗ[R] β :=
  letI := (AddCommMonoid.canonicalCongr e).invFun ‹AddCommMonoid β›
  letI := (_root_.Module.canonicalCongr e rfl).invFun ‹_root_.Module R β›
  { toFun := e.toFun
    invFun := e.invFun
    map_add' _ _ := e.right_inv _
    map_smul' _ _ := e.right_inv _
    left_inv := e.left_inv
    right_inv := e.right_inv }

variable [AddCommMonoid α] [AddCommMonoid β] [Module R β]

namespace AddEquiv

variable (e : α ≃+ β)

variable (R) in
/-- Transfer `Module` across an `Equiv` -/
protected abbrev module : Module R α where
  __ := e.distribMulAction R
  zero_smul := by simp [e.smul_def, zero_smul]
  add_smul := by simp [e.smul_def, add_smul]

variable (R) in
/-- When `α` is equipped with the `A`-module structure transferred via `e : α ≃+ β`,
this isomorphism is `A`-linear. -/
def linearEquiv :
    letI := e.module R
    α ≃ₗ[R] β :=
  letI := e.module R
  { e with
    map_smul' := fun r x => by
      apply e.symm.injective
      simp only [RingHom.id_apply, EmbeddingLike.apply_eq_iff_eq]
      exact Iff.mp (eq_symm_apply _) rfl }

@[simp]
lemma linearEquiv_apply (a : α) : e.linearEquiv R a = e a := rfl

@[simp]
lemma linearEquiv_symm_apply (b : β) : (e.linearEquiv R).symm b = e.symm b := rfl

variable (R) in
/-- Transfer `Module.IsTorsionFree` across an `Equiv` -/
protected lemma moduleIsTorsionFree [Module.IsTorsionFree R β] :
    letI := e.module R
    Module.IsTorsionFree R α :=
  letI := e.module R
  (e.linearEquiv R).injective.moduleIsTorsionFree _ (by simp)

end AddEquiv

@[deprecated (since := "2026-08-10")] alias Equiv.module := AddEquiv.module
@[deprecated (since := "2026-08-10")] alias Equiv.linearEquiv := AddEquiv.linearEquiv
@[deprecated (since := "2026-08-10")] alias Equiv.linearEquiv_apply := AddEquiv.linearEquiv_apply
@[deprecated (since := "2026-08-10")]
alias Equiv.linearEquiv_symm_apply := AddEquiv.linearEquiv_symm_apply
@[deprecated (since := "2026-08-10")]
alias Equiv.moduleIsTorsionFree := AddEquiv.moduleIsTorsionFree

variable [Module R α] (A : Type*) [Semiring A] [Module R A] [Module A β]

/-- The module instance from `AddEquiv.module` is compatible with the `R`-module structures,
if the `AddEquiv` is induced by an `R`-module isomorphism. -/
lemma LinearEquiv.isScalarTower [IsScalarTower R A β] (e : α ≃ₗ[R] β) :
    letI := e.toAddEquiv.module A
    IsScalarTower R A α := by
  let := e.toAddEquiv.module A
  constructor
  intro x y z
  simp only [Equiv.smul_def, smul_assoc]
  apply e.symm.map_smul
