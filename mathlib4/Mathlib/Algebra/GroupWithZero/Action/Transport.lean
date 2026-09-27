/-
Copyright (c) 2026 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import Mathlib.Algebra.Group.Action.Transport
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Transport

/-!
# Transporting actions preserving zero and addition

`@[transport]` congruences for `SMulZeroClass`, `SMulWithZero`, `DistribSMul`, `DistribMulAction`
and `MulActionWithZero`, so that `inferInstanceAs` and `deriving` carry these structures across a
`newtype`. Each takes an equivalence for the scalars and one for the acted-on types. The actions are
those of `SMul.canonicalCongr`, so that transport unfolds them.
-/

public section

variable {M N α β : Type*}

theorem SMulZeroClass.toSMul_injective [Zero α] :
    Function.Injective fun i : SMulZeroClass M α ↦ i.toSMul := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

/-- `SMulZeroClass` instances correspond along canonical equivalences of the scalars and of the
acted-on types, over the transported zero. -/
@[transport]
protected abbrev SMulZeroClass.canonicalCongr (e₁ : Lean.CanonicalEquivalence M N)
    (e₂ : Lean.CanonicalEquivalence α β) [iβ : Zero β] {iα : Zero α}
    (hα : iα = (Zero.canonicalCongr e₂).invFun iβ) :
    Lean.CanonicalEquivalence (SMulZeroClass M α) (SMulZeroClass N β) where
  toFun i :=
    { toSMul := (SMul.canonicalCongr e₁ e₂).toFun i.toSMul
      smul_zero n := by
        subst hα
        let := (Zero.canonicalCongr e₂).invFun iβ
        change e₂.toFun (e₁.invFun n • e₂.invFun 0) = 0
        rw [show e₂.invFun 0 = (0 : α) from rfl, smul_zero]
        exact e₂.toFun_invFun 0 }
  invFun i :=
    { toSMul := (SMul.canonicalCongr e₁ e₂).invFun i.toSMul
      smul_zero m := by
        subst hα
        change e₂.invFun (e₁.toFun m • e₂.toFun (e₂.invFun 0)) = e₂.invFun 0
        rw [e₂.toFun_invFun, smul_zero] }
  left_inv i := SMulZeroClass.toSMul_injective ((SMul.canonicalCongr e₁ e₂).left_inv i.toSMul)
  right_inv i := SMulZeroClass.toSMul_injective ((SMul.canonicalCongr e₁ e₂).right_inv i.toSMul)

theorem SMulWithZero.toSMulZeroClass_injective [Zero M] [Zero α] :
    Function.Injective fun i : SMulWithZero M α ↦ i.toSMulZeroClass := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

/-- `SMulWithZero` instances correspond along canonical equivalences of the scalars and of the
acted-on types, over the transported zeros. -/
@[transport]
protected abbrev SMulWithZero.canonicalCongr (e₁ : Lean.CanonicalEquivalence M N)
    (e₂ : Lean.CanonicalEquivalence α β) [iN : Zero N] {iM : Zero M}
    (hM : iM = (Zero.canonicalCongr e₁).invFun iN) [iβ : Zero β] {iα : Zero α}
    (hα : iα = (Zero.canonicalCongr e₂).invFun iβ) :
    Lean.CanonicalEquivalence (SMulWithZero M α) (SMulWithZero N β) where
  toFun i :=
    { toSMul := (SMul.canonicalCongr e₁ e₂).toFun i.toSMul
      smul_zero := ((SMulZeroClass.canonicalCongr e₁ e₂ hα).toFun i.toSMulZeroClass).smul_zero
      zero_smul b := by
        subst hM hα
        let := (Zero.canonicalCongr e₁).invFun iN
        change e₂.toFun (e₁.invFun 0 • e₂.invFun b) = 0
        rw [show e₁.invFun 0 = (0 : M) from rfl, zero_smul]
        exact e₂.toFun_invFun 0 }
  invFun i :=
    { toSMul := (SMul.canonicalCongr e₁ e₂).invFun i.toSMul
      smul_zero := ((SMulZeroClass.canonicalCongr e₁ e₂ hα).invFun i.toSMulZeroClass).smul_zero
      zero_smul a := by
        subst hM hα
        change e₂.invFun (e₁.toFun (e₁.invFun 0) • e₂.toFun a) = e₂.invFun 0
        rw [e₁.toFun_invFun, zero_smul] }
  left_inv i := SMulWithZero.toSMulZeroClass_injective <|
    (SMulZeroClass.canonicalCongr e₁ e₂ hα).left_inv i.toSMulZeroClass
  right_inv i := SMulWithZero.toSMulZeroClass_injective <|
    (SMulZeroClass.canonicalCongr e₁ e₂ hα).right_inv i.toSMulZeroClass

/-- `DistribSMul` instances correspond along canonical equivalences of the scalars and of the
acted-on types, over the transported additive structure. -/
@[transport]
protected abbrev DistribSMul.canonicalCongr (e₁ : Lean.CanonicalEquivalence M N)
    (e₂ : Lean.CanonicalEquivalence α β) [iβ : AddZeroClass β] {iα : AddZeroClass α}
    (hα : iα = (AddZeroClass.canonicalCongr e₂).invFun iβ) :
    Lean.CanonicalEquivalence (DistribSMul M α) (DistribSMul N β) where
  toFun i :=
    { toSMul := (SMul.canonicalCongr e₁ e₂).toFun i.toSMul
      smul_zero := ((SMulZeroClass.canonicalCongr e₁ e₂
        (congrArg (·.toZero) hα : _ = (Zero.canonicalCongr e₂).invFun _)).toFun
          i.toSMulZeroClass).smul_zero
      smul_add n x y := by
        subst hα
        let := (AddZeroClass.canonicalCongr e₂).invFun iβ
        apply e₂.invFun_injective
        change e₂.invFun (e₂.toFun (e₁.invFun n • e₂.invFun (x + y))) =
          e₁.invFun n • e₂.invFun x + e₁.invFun n • e₂.invFun y
        rw [e₂.invFun_toFun, ← smul_add]
        change _ = e₁.invFun n • e₂.invFun (e₂.toFun (e₂.invFun x) + e₂.toFun (e₂.invFun y))
        rw [e₂.toFun_invFun, e₂.toFun_invFun] }
  invFun i :=
    { toSMul := (SMul.canonicalCongr e₁ e₂).invFun i.toSMul
      smul_zero := ((SMulZeroClass.canonicalCongr e₁ e₂
        (congrArg (·.toZero) hα : _ = (Zero.canonicalCongr e₂).invFun _)).invFun
          i.toSMulZeroClass).smul_zero
      smul_add m x y := by
        subst hα
        change e₂.invFun (e₁.toFun m • e₂.toFun (e₂.invFun (e₂.toFun x + e₂.toFun y))) =
          e₂.invFun (e₂.toFun (e₂.invFun (e₁.toFun m • e₂.toFun x)) +
            e₂.toFun (e₂.invFun (e₁.toFun m • e₂.toFun y)))
        simp only [Lean.CanonicalEquivalence.toFun_invFun, smul_add] }
  left_inv i :=
    DistribSMul.ext (congrArg (@SMul.smul _ _) ((SMul.canonicalCongr e₁ e₂).left_inv i.toSMul))
  right_inv i :=
    DistribSMul.ext (congrArg (@SMul.smul _ _) ((SMul.canonicalCongr e₁ e₂).right_inv i.toSMul))

/-- `DistribMulAction` instances correspond along canonical equivalences of the scalars and of the
acted-on types, over the transported monoid and additive monoid. -/
@[transport]
protected abbrev DistribMulAction.canonicalCongr (e₁ : Lean.CanonicalEquivalence M N)
    (e₂ : Lean.CanonicalEquivalence α β) [iN : Monoid N] {iM : Monoid M}
    (hM : iM = (Monoid.canonicalCongr e₁).invFun iN) [iβ : AddMonoid β] {iα : AddMonoid α}
    (hα : iα = (AddMonoid.canonicalCongr e₂).invFun iβ) :
    Lean.CanonicalEquivalence (DistribMulAction M α) (DistribMulAction N β) where
  toFun i :=
    { toMulAction := (MulAction.canonicalCongr e₁ e₂ hM).toFun i.toMulAction
      smul_zero := ((DistribSMul.canonicalCongr e₁ e₂ (congrArg (·.toAddZeroClass) hα :
        _ = (AddZeroClass.canonicalCongr e₂).invFun _)).toFun i.toDistribSMul).smul_zero
      smul_add := ((DistribSMul.canonicalCongr e₁ e₂ (congrArg (·.toAddZeroClass) hα :
        _ = (AddZeroClass.canonicalCongr e₂).invFun _)).toFun i.toDistribSMul).smul_add }
  invFun i :=
    { toMulAction := (MulAction.canonicalCongr e₁ e₂ hM).invFun i.toMulAction
      smul_zero := ((DistribSMul.canonicalCongr e₁ e₂ (congrArg (·.toAddZeroClass) hα :
        _ = (AddZeroClass.canonicalCongr e₂).invFun _)).invFun i.toDistribSMul).smul_zero
      smul_add := ((DistribSMul.canonicalCongr e₁ e₂ (congrArg (·.toAddZeroClass) hα :
        _ = (AddZeroClass.canonicalCongr e₂).invFun _)).invFun i.toDistribSMul).smul_add }
  left_inv i := DistribMulAction.ext <|
    congrArg (@SMul.smul _ _) ((SMul.canonicalCongr e₁ e₂).left_inv i.toSMul)
  right_inv i := DistribMulAction.ext <|
    congrArg (@SMul.smul _ _) ((SMul.canonicalCongr e₁ e₂).right_inv i.toSMul)

theorem MulActionWithZero.toMulAction_injective [MonoidWithZero M] [Zero α] :
    Function.Injective fun i : MulActionWithZero M α ↦ i.toMulAction := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

/-- `MulActionWithZero` instances correspond along canonical equivalences of the scalars and of the
acted-on types, over the transported monoid with zero and zero. -/
@[transport]
protected abbrev MulActionWithZero.canonicalCongr (e₁ : Lean.CanonicalEquivalence M N)
    (e₂ : Lean.CanonicalEquivalence α β) [iN : MonoidWithZero N] {iM : MonoidWithZero M}
    (hM : iM = (MonoidWithZero.canonicalCongr e₁).invFun iN) [iβ : Zero β] {iα : Zero α}
    (hα : iα = (Zero.canonicalCongr e₂).invFun iβ) :
    Lean.CanonicalEquivalence (MulActionWithZero M α) (MulActionWithZero N β) where
  toFun i :=
    { toMulAction := (MulAction.canonicalCongr e₁ e₂ (congrArg (·.toMonoid) hM :
        _ = (Monoid.canonicalCongr e₁).invFun _)).toFun i.toMulAction
      smul_zero := ((SMulWithZero.canonicalCongr e₁ e₂ (congrArg (·.toZero) hM :
        _ = (Zero.canonicalCongr e₁).invFun _) hα).toFun i.toSMulWithZero).smul_zero
      zero_smul := ((SMulWithZero.canonicalCongr e₁ e₂ (congrArg (·.toZero) hM :
        _ = (Zero.canonicalCongr e₁).invFun _) hα).toFun i.toSMulWithZero).zero_smul }
  invFun i :=
    { toMulAction := (MulAction.canonicalCongr e₁ e₂ (congrArg (·.toMonoid) hM :
        _ = (Monoid.canonicalCongr e₁).invFun _)).invFun i.toMulAction
      smul_zero := ((SMulWithZero.canonicalCongr e₁ e₂ (congrArg (·.toZero) hM :
        _ = (Zero.canonicalCongr e₁).invFun _) hα).invFun i.toSMulWithZero).smul_zero
      zero_smul := ((SMulWithZero.canonicalCongr e₁ e₂ (congrArg (·.toZero) hM :
        _ = (Zero.canonicalCongr e₁).invFun _) hα).invFun i.toSMulWithZero).zero_smul }
  left_inv i := MulActionWithZero.toMulAction_injective <|
    (MulAction.canonicalCongr e₁ e₂ (congrArg (·.toMonoid) hM :
      _ = (Monoid.canonicalCongr e₁).invFun _)).left_inv i.toMulAction
  right_inv i := MulActionWithZero.toMulAction_injective <|
    (MulAction.canonicalCongr e₁ e₂ (congrArg (·.toMonoid) hM :
      _ = (Monoid.canonicalCongr e₁).invFun _)).right_inv i.toMulAction
