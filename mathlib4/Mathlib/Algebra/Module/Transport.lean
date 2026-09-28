/-
Copyright (c) 2026 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Transport
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Transport

/-!
# Transporting modules

A `@[transport]` congruence for `Module`, so that `inferInstanceAs` and `deriving` carry module
structures across a `newtype`, in the scalars and in the module.

This file is kept light, so that the order synonyms can import it.
-/

public section

variable {α β : Type*}

/-- `Module` instances correspond along canonical equivalences of the scalars and of the acted-on
types, over the transported semiring and additive monoid. The action is that of
`SMul.canonicalCongr`, so that transport unfolds it. -/
@[transport]
protected abbrev Module.canonicalCongr {S S' : Type*} (e₁ : Lean.CanonicalEquivalence S S')
    (e₂ : Lean.CanonicalEquivalence α β) [iS' : Semiring S'] {iS : Semiring S}
    (hS : iS = (Semiring.canonicalCongr e₁).invFun iS') [iβ : AddCommMonoid β]
    {iα : AddCommMonoid α} (hα : iα = (AddCommMonoid.canonicalCongr e₂).invFun iβ) :
    Lean.CanonicalEquivalence (Module S α) (Module S' β) where
  toFun i :=
    { toSMul := (SMul.canonicalCongr e₁ e₂).toFun i.toSMul
      one_smul := ((MulAction.canonicalCongr e₁ e₂ (congrArg (·.toMonoid) hS :
        _ = (Monoid.canonicalCongr e₁).invFun _)).toFun
          i.toMulAction).one_smul
      mul_smul := ((MulAction.canonicalCongr e₁ e₂ (congrArg (·.toMonoid) hS :
        _ = (Monoid.canonicalCongr e₁).invFun _)).toFun
          i.toMulAction).mul_smul
      smul_zero := ((DistribSMul.canonicalCongr e₁ e₂ (congrArg (·.toAddZeroClass) hα :
        _ = (AddZeroClass.canonicalCongr e₂).invFun _)).toFun
          i.toDistribMulAction.toDistribSMul).smul_zero
      smul_add := ((DistribSMul.canonicalCongr e₁ e₂ (congrArg (·.toAddZeroClass) hα :
        _ = (AddZeroClass.canonicalCongr e₂).invFun _)).toFun
          i.toDistribMulAction.toDistribSMul).smul_add
      add_smul r s x := by
        subst hS hα
        let := (Semiring.canonicalCongr e₁).invFun iS'
        let := (AddCommMonoid.canonicalCongr e₂).invFun iβ
        apply e₂.invFun_injective
        change e₂.invFun (e₂.toFun (e₁.invFun (r + s) • e₂.invFun x)) =
          e₁.invFun r • e₂.invFun x + e₁.invFun s • e₂.invFun x
        rw [e₂.invFun_toFun, ← add_smul]
        change _ = e₁.invFun (e₁.toFun (e₁.invFun r) + e₁.toFun (e₁.invFun s)) • _
        rw [e₁.toFun_invFun, e₁.toFun_invFun]
      zero_smul x := by
        subst hS hα
        let := (Semiring.canonicalCongr e₁).invFun iS'
        let := (AddCommMonoid.canonicalCongr e₂).invFun iβ
        change e₂.toFun (e₁.invFun 0 • e₂.invFun x) = 0
        rw [show e₁.invFun 0 = (0 : S) from rfl, zero_smul]
        exact e₂.toFun_invFun 0 }
  invFun i :=
    { toSMul := (SMul.canonicalCongr e₁ e₂).invFun i.toSMul
      one_smul := ((MulAction.canonicalCongr e₁ e₂ (congrArg (·.toMonoid) hS :
        _ = (Monoid.canonicalCongr e₁).invFun _)).invFun
          i.toMulAction).one_smul
      mul_smul := ((MulAction.canonicalCongr e₁ e₂ (congrArg (·.toMonoid) hS :
        _ = (Monoid.canonicalCongr e₁).invFun _)).invFun
          i.toMulAction).mul_smul
      smul_zero := ((DistribSMul.canonicalCongr e₁ e₂ (congrArg (·.toAddZeroClass) hα :
        _ = (AddZeroClass.canonicalCongr e₂).invFun _)).invFun
          i.toDistribMulAction.toDistribSMul).smul_zero
      smul_add := ((DistribSMul.canonicalCongr e₁ e₂ (congrArg (·.toAddZeroClass) hα :
        _ = (AddZeroClass.canonicalCongr e₂).invFun _)).invFun
          i.toDistribMulAction.toDistribSMul).smul_add
      add_smul r s x := by
        subst hS hα
        change e₂.invFun (e₁.toFun (e₁.invFun (e₁.toFun r + e₁.toFun s)) • e₂.toFun x) =
          e₂.invFun (e₂.toFun (e₂.invFun (e₁.toFun r • e₂.toFun x)) +
            e₂.toFun (e₂.invFun (e₁.toFun s • e₂.toFun x)))
        simp only [Lean.CanonicalEquivalence.toFun_invFun, add_smul]
      zero_smul x := by
        subst hS hα
        change e₂.invFun (e₁.toFun (e₁.invFun 0) • e₂.toFun x) = e₂.invFun 0
        rw [e₁.toFun_invFun, zero_smul] }
  left_inv i := Module.ext' _ _ fun r x ↦ congrFun (congrFun
    (congrArg (@SMul.smul _ _) ((SMul.canonicalCongr e₁ e₂).left_inv i.toSMul)) r) x
  right_inv i := Module.ext' _ _ fun r x ↦ congrFun (congrFun
    (congrArg (@SMul.smul _ _) ((SMul.canonicalCongr e₁ e₂).right_inv i.toSMul)) r) x
