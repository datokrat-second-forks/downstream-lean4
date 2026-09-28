/-
Copyright (c) 2026 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Transport

/-!
# Transporting monoid actions

`@[transport]` congruences for `MulAction`, `SMulCommClass`, `IsScalarTower` and `IsCentralScalar`,
so that `inferInstanceAs` and `deriving` carry these structures across a `newtype`. Each takes an
equivalence for every type argument; the search fills the unchanged ones with
`Lean.CanonicalEquivalence.refl`. The actions are those of `SMul.canonicalCongr`, so that transport
unfolds them.

This file is kept light, so that the order synonyms can import it.
-/

public section

variable {M M' N N' α β : Type*}

/-- `MulAction` instances correspond along canonical equivalences of the scalars and of the
acted-on types, over the transported monoid. -/
@[to_additive (attr := transport) /-- `AddAction` instances correspond along canonical
equivalences of the scalars and of the acted-on types, over the transported additive monoid. -/]
protected abbrev MulAction.canonicalCongr (e₁ : Lean.CanonicalEquivalence M N)
    (e₂ : Lean.CanonicalEquivalence α β) [iN : Monoid N] {iM : Monoid M}
    (hM : iM = (Monoid.canonicalCongr e₁).invFun iN) :
    Lean.CanonicalEquivalence (MulAction M α) (MulAction N β) where
  toFun i :=
    { toSMul := (SMul.canonicalCongr e₁ e₂).toFun i.toSMul
      one_smul b := by
        subst hM
        let := (Monoid.canonicalCongr e₁).invFun iN
        change e₂.toFun ((1 : M) • e₂.invFun b) = b
        rw [one_smul, e₂.toFun_invFun]
      mul_smul a b x := by
        subst hM
        let := (Monoid.canonicalCongr e₁).invFun iN
        change e₂.toFun (e₁.invFun (a * b) • e₂.invFun x) =
          e₂.toFun (e₁.invFun a • e₂.invFun (e₂.toFun (e₁.invFun b • e₂.invFun x)))
        rw [e₂.invFun_toFun, ← mul_smul]
        change _ = e₂.toFun (e₁.invFun (e₁.toFun (e₁.invFun a) * e₁.toFun (e₁.invFun b)) • _)
        rw [e₁.toFun_invFun, e₁.toFun_invFun] }
  invFun i :=
    { toSMul := (SMul.canonicalCongr e₁ e₂).invFun i.toSMul
      one_smul a := by
        subst hM
        change e₂.invFun (e₁.toFun (e₁.invFun 1) • e₂.toFun a) = a
        rw [e₁.toFun_invFun, one_smul, e₂.invFun_toFun]
      mul_smul a b x := by
        subst hM
        change e₂.invFun (e₁.toFun (e₁.invFun (e₁.toFun a * e₁.toFun b)) • e₂.toFun x) =
          e₂.invFun (e₁.toFun a • e₂.toFun (e₂.invFun (e₁.toFun b • e₂.toFun x)))
        rw [e₁.toFun_invFun, e₂.toFun_invFun, mul_smul] }
  left_inv i :=
    MulAction.ext (congrArg (@SMul.smul _ _) ((SMul.canonicalCongr e₁ e₂).left_inv i.toSMul))
  right_inv i :=
    MulAction.ext (congrArg (@SMul.smul _ _) ((SMul.canonicalCongr e₁ e₂).right_inv i.toSMul))

/-- `SMulCommClass` holds on both sides of canonical equivalences of both scalars and of the
acted-on types, for the transported actions. -/
@[to_additive (attr := transport) /-- `VAddCommClass` holds on both sides of canonical
equivalences of both scalars and of the acted-on types, for the transported actions. -/]
protected abbrev SMulCommClass.canonicalCongr (e₁ : Lean.CanonicalEquivalence M M')
    (e₂ : Lean.CanonicalEquivalence N N') (e₃ : Lean.CanonicalEquivalence α β)
    [iM : SMul M' β] [iN : SMul N' β] {jM : SMul M α} {jN : SMul N α}
    (hM : jM = (SMul.canonicalCongr e₁ e₃).invFun iM)
    (hN : jN = (SMul.canonicalCongr e₂ e₃).invFun iN) :
    Lean.CanonicalEquivalence (SMulCommClass M N α) (SMulCommClass M' N' β) := by
  subst hM hN
  letI := (SMul.canonicalCongr e₁ e₃).invFun iM
  letI := (SMul.canonicalCongr e₂ e₃).invFun iN
  exact {
    toFun _ := ⟨fun m n b ↦ e₃.invFun_injective <| by
      have := smul_comm (e₁.invFun m) (e₂.invFun n) (e₃.invFun b)
      change e₃.invFun (e₁.toFun (e₁.invFun m) • e₃.toFun (e₃.invFun
          (e₂.toFun (e₂.invFun n) • e₃.toFun (e₃.invFun b)))) =
        e₃.invFun (e₂.toFun (e₂.invFun n) • e₃.toFun (e₃.invFun
          (e₁.toFun (e₁.invFun m) • e₃.toFun (e₃.invFun b)))) at this
      simpa only [Lean.CanonicalEquivalence.toFun_invFun] using this⟩
    invFun _ := ⟨fun m n a ↦ by
      change e₃.invFun (e₁.toFun m • e₃.toFun (e₃.invFun (e₂.toFun n • e₃.toFun a))) =
        e₃.invFun (e₂.toFun n • e₃.toFun (e₃.invFun (e₁.toFun m • e₃.toFun a)))
      rw [e₃.toFun_invFun, e₃.toFun_invFun, smul_comm]⟩
    left_inv _ := rfl
    right_inv _ := rfl }

/-- `IsScalarTower` holds on both sides of canonical equivalences of both scalars and of the
acted-on types, for the transported actions. -/
@[to_additive (attr := transport) /-- `VAddAssocClass` holds on both sides of canonical
equivalences of both scalars and of the acted-on types, for the transported actions. -/]
protected abbrev IsScalarTower.canonicalCongr (e₁ : Lean.CanonicalEquivalence M M')
    (e₂ : Lean.CanonicalEquivalence N N') (e₃ : Lean.CanonicalEquivalence α β)
    [iMN : SMul M' N'] [iN : SMul N' β] [iM : SMul M' β]
    {jMN : SMul M N} {jN : SMul N α} {jM : SMul M α}
    (hMN : jMN = (SMul.canonicalCongr e₁ e₂).invFun iMN)
    (hN : jN = (SMul.canonicalCongr e₂ e₃).invFun iN)
    (hM : jM = (SMul.canonicalCongr e₁ e₃).invFun iM) :
    Lean.CanonicalEquivalence (IsScalarTower M N α) (IsScalarTower M' N' β) := by
  subst hMN hN hM
  letI := (SMul.canonicalCongr e₁ e₂).invFun iMN
  letI := (SMul.canonicalCongr e₂ e₃).invFun iN
  letI := (SMul.canonicalCongr e₁ e₃).invFun iM
  exact {
    toFun _ := ⟨fun m n b ↦ e₃.invFun_injective <| by
      have := smul_assoc (e₁.invFun m) (e₂.invFun n) (e₃.invFun b)
      change e₃.invFun (e₂.toFun (e₂.invFun (e₁.toFun (e₁.invFun m) • e₂.toFun (e₂.invFun n))) •
          e₃.toFun (e₃.invFun b)) =
        e₃.invFun (e₁.toFun (e₁.invFun m) • e₃.toFun (e₃.invFun
          (e₂.toFun (e₂.invFun n) • e₃.toFun (e₃.invFun b)))) at this
      simpa only [Lean.CanonicalEquivalence.toFun_invFun] using this⟩
    invFun _ := ⟨fun m n a ↦ by
      change e₃.invFun (e₂.toFun (e₂.invFun (e₁.toFun m • e₂.toFun n)) • e₃.toFun a) =
        e₃.invFun (e₁.toFun m • e₃.toFun (e₃.invFun (e₂.toFun n • e₃.toFun a)))
      rw [e₂.toFun_invFun, e₃.toFun_invFun, smul_assoc]⟩
    left_inv _ := rfl
    right_inv _ := rfl }

/-- `IsCentralScalar` holds on both sides of canonical equivalences of the scalars and of the
acted-on types, for the transported actions. The search supplies `e₁'`
(`Lean.CanonicalEquivalence.refl` if the scalars do not change), and `hop` ties it to `e₁`. -/
@[to_additive (attr := transport) /-- `IsCentralVAdd` holds on both sides of canonical
equivalences of the scalars and of the acted-on types, for the transported actions. -/]
protected abbrev IsCentralScalar.canonicalCongr (e₁ : Lean.CanonicalEquivalence M N)
    (e₁' : Lean.CanonicalEquivalence Mᵐᵒᵖ Nᵐᵒᵖ) (e₂ : Lean.CanonicalEquivalence α β)
    (hop : (fun m : M ↦ e₁'.toFun (MulOpposite.op m)) = fun m ↦ MulOpposite.op (e₁.toFun m))
    [iN : SMul N β] [iN' : SMul Nᵐᵒᵖ β] {jM : SMul M α} {jM' : SMul Mᵐᵒᵖ α}
    (hM : jM = (SMul.canonicalCongr e₁ e₂).invFun iN)
    (hM' : jM' = (SMul.canonicalCongr e₁' e₂).invFun iN') :
    Lean.CanonicalEquivalence (IsCentralScalar M α) (IsCentralScalar N β) := by
  subst hM hM'
  letI := (SMul.canonicalCongr e₁ e₂).invFun iN
  letI := (SMul.canonicalCongr e₁' e₂).invFun iN'
  have hop' (m : M) : e₁'.toFun (MulOpposite.op m) = MulOpposite.op (e₁.toFun m) :=
    congrFun hop m
  exact {
    toFun _ := ⟨fun n b ↦ e₂.invFun_injective <| by
      have := op_smul_eq_smul (e₁.invFun n) (e₂.invFun b)
      change e₂.invFun (e₁'.toFun (MulOpposite.op (e₁.invFun n)) • e₂.toFun (e₂.invFun b)) =
        e₂.invFun (e₁.toFun (e₁.invFun n) • e₂.toFun (e₂.invFun b)) at this
      simpa only [hop', Lean.CanonicalEquivalence.toFun_invFun] using this⟩
    invFun _ := ⟨fun m a ↦ by
      change e₂.invFun (e₁'.toFun (MulOpposite.op m) • e₂.toFun a) =
        e₂.invFun (e₁.toFun m • e₂.toFun a)
      rw [hop', op_smul_eq_smul]⟩
    left_inv _ := rfl
    right_inv _ := rfl }
