/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Data.DFinsupp.Sigma
public import Mathlib.Data.DFinsupp.Submonoid

/-!
# Direct sum

This file defines the direct sum of abelian groups, indexed by a discrete type.

## Notation

`⨁ i, β i` is the n-ary direct sum `DirectSum`.
This notation is in the `DirectSum` locale, accessible after `open DirectSum`.

## References

* https://en.wikipedia.org/wiki/Direct_sum
-/

@[expose] public section

open Function

universe u v w u₁

variable (ι : Type v) (β : ι → Type w)

/-- `DirectSum ι β` is the direct sum of a family of additive commutative monoids `β i`.

Note: `open DirectSum` will enable the notation `⨁ i, β i` for `DirectSum ι β`. -/
newtype DirectSum [∀ i, AddCommMonoid (β i)] where
  /-- Converts a finitely supported dependent function to an element of the direct sum. -/
  ofDFinsupp ::
  /-- Converts an element of the direct sum to a finitely supported dependent function. -/
  toDFinsupp : Π₀ i, β i
deriving AddCommMonoid, Inhabited, DFunLike

/-- `⨁ i, f i` is notation for `DirectSum _ f` and equals the direct sum of `fun i ↦ f i`.
Taking the direct sum over multiple arguments is possible, e.g. `⨁ (i) (j), f i j`. -/
scoped[DirectSum] notation3 "⨁ "(...)", "r:(scoped f => DirectSum _ f) => r

-- Porting note: The below recreates some of the lean3 notation, not fully yet
-- section
-- open Batteries.ExtendedBinder
-- syntax (name := bigdirectsum) "⨁ " extBinders ", " term : term
-- macro_rules (kind := bigdirectsum)
--   | `(⨁ $_:ident, $y:ident → $z:ident) => `(DirectSum _ (fun $y ↦ $z))
--   | `(⨁ $x:ident, $p) => `(DirectSum _ (fun $x ↦ $p))
--   | `(⨁ $_:ident : $t:ident, $p) => `(DirectSum _ (fun $t ↦ $p))
--   | `(⨁ ($x:ident) ($y:ident), $p) => `(DirectSum _ (fun $x ↦ fun $y ↦ $p))
-- end

namespace DirectSum

variable {ι β}

-- This instance exists to avoid nsmul and zsmul diamonds.
instance {R : Type u} [Semiring R] [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)] :
    SMul R (⨁ i, β i) := inferInstanceAs <| SMul R (Π₀ (i : ι), β i)

instance [DecidableEq ι] [∀ i, AddCommMonoid (β i)] [∀ i, DecidableEq (β i)] :
    DecidableEq (DirectSum ι β) :=
  inferInstanceAs <| DecidableEq (Π₀ i, β i)

variable (β) in
/-- Coercion from a `DirectSum` to a pi type is an `AddMonoidHom`. -/
def coeFnAddMonoidHom [∀ i, AddCommMonoid (β i)] : (⨁ i, β i) →+ (Π i, β i) where
  toFun x := x
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma coeFnAddMonoidHom_apply [∀ i, AddCommMonoid (β i)] (v : ⨁ i, β i) :
    coeFnAddMonoidHom β v = v :=
  rfl

section AddCommGroup

variable [∀ i, AddCommGroup (β i)]

instance : AddCommGroup (DirectSum ι β) :=
  inferInstanceAs (AddCommGroup (Π₀ i, β i))

@[simp]
theorem sub_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i :=
  rfl

@[simp] lemma toDFinsupp_neg (x : ⨁ i, β i) : (-x).toDFinsupp = -x.toDFinsupp := rfl
@[simp] lemma ofDFinsupp_neg (f : Π₀ i, β i) : ofDFinsupp (-f) = -ofDFinsupp f := rfl

@[simp] lemma toDFinsupp_sub (x y : ⨁ i, β i) :
    (x - y).toDFinsupp = x.toDFinsupp - y.toDFinsupp := rfl
@[simp] lemma ofDFinsupp_sub (f g : Π₀ i, β i) :
    ofDFinsupp (f - g) = ofDFinsupp f - ofDFinsupp g := rfl

end AddCommGroup

variable [∀ i, AddCommMonoid (β i)]

@[ext] theorem ext {x y : DirectSum ι β} (w : ∀ i, x i = y i) : x = y :=
  DFunLike.ext _ _ w

/-! ### The underlying finitely supported functions -/

@[simp] lemma toDFinsupp_ofDFinsupp (f : Π₀ i, β i) : (ofDFinsupp f : ⨁ i, β i).toDFinsupp = f :=
  rfl
@[simp] lemma ofDFinsupp_toDFinsupp (x : ⨁ i, β i) : ofDFinsupp x.toDFinsupp = x := rfl

@[simp] lemma toDFinsupp_apply (x : ⨁ i, β i) (i : ι) : x.toDFinsupp i = x i := rfl
@[simp] lemma ofDFinsupp_apply (f : Π₀ i, β i) (i : ι) : (ofDFinsupp f : ⨁ i, β i) i = f i := rfl

lemma toDFinsupp_injective : Injective (toDFinsupp : (⨁ i, β i) → Π₀ i, β i) :=
  LeftInverse.injective ofDFinsupp_toDFinsupp

lemma ofDFinsupp_injective : Injective (ofDFinsupp : (Π₀ i, β i) → ⨁ i, β i) :=
  LeftInverse.injective toDFinsupp_ofDFinsupp

lemma toDFinsupp_surjective : Surjective (toDFinsupp : (⨁ i, β i) → Π₀ i, β i) :=
  RightInverse.surjective toDFinsupp_ofDFinsupp

lemma ofDFinsupp_surjective : Surjective (ofDFinsupp : (Π₀ i, β i) → ⨁ i, β i) :=
  RightInverse.surjective ofDFinsupp_toDFinsupp

lemma toDFinsupp_bijective : Bijective (toDFinsupp : (⨁ i, β i) → Π₀ i, β i) :=
  ⟨toDFinsupp_injective, toDFinsupp_surjective⟩

lemma ofDFinsupp_bijective : Bijective (ofDFinsupp : (Π₀ i, β i) → ⨁ i, β i) :=
  ⟨ofDFinsupp_injective, ofDFinsupp_surjective⟩

@[simp] lemma toDFinsupp_inj {x y : ⨁ i, β i} : x.toDFinsupp = y.toDFinsupp ↔ x = y :=
  toDFinsupp_injective.eq_iff

@[simp] lemma ofDFinsupp_inj {f g : Π₀ i, β i} :
    (ofDFinsupp f : ⨁ i, β i) = ofDFinsupp g ↔ f = g :=
  ofDFinsupp_injective.eq_iff

@[simp] lemma toDFinsupp_zero : (0 : ⨁ i, β i).toDFinsupp = 0 := rfl
@[simp] lemma ofDFinsupp_zero : (ofDFinsupp 0 : ⨁ i, β i) = 0 := rfl

@[simp] lemma toDFinsupp_add (x y : ⨁ i, β i) :
    (x + y).toDFinsupp = x.toDFinsupp + y.toDFinsupp := rfl
@[simp] lemma ofDFinsupp_add (f g : Π₀ i, β i) :
    (ofDFinsupp (f + g) : ⨁ i, β i) = ofDFinsupp f + ofDFinsupp g := rfl

@[simp] lemma toDFinsupp_eq_zero {x : ⨁ i, β i} : x.toDFinsupp = 0 ↔ x = 0 :=
  toDFinsupp_injective.eq_iff' toDFinsupp_zero
@[simp] lemma ofDFinsupp_eq_zero {f : Π₀ i, β i} : (ofDFinsupp f : ⨁ i, β i) = 0 ↔ f = 0 :=
  ofDFinsupp_injective.eq_iff' ofDFinsupp_zero

@[simp] lemma toDFinsupp_smul {R : Type*} [Semiring R] [∀ i, Module R (β i)] (r : R)
    (x : ⨁ i, β i) : (r • x).toDFinsupp = r • x.toDFinsupp := rfl
@[simp] lemma ofDFinsupp_smul {R : Type*} [Semiring R] [∀ i, Module R (β i)] (r : R)
    (f : Π₀ i, β i) : (ofDFinsupp (r • f) : ⨁ i, β i) = r • ofDFinsupp f := rfl

variable (β) in
/-- `DirectSum.toDFinsupp` and `DirectSum.ofDFinsupp` as an equivalence. -/
@[simps]
protected def equiv : (⨁ i, β i) ≃ Π₀ i, β i where
  toFun := toDFinsupp
  invFun := ofDFinsupp

variable (β) in
/-- `DirectSum.equiv` as an additive isomorphism. -/
@[simps apply symm_apply]
protected def addEquiv : (⨁ i, β i) ≃+ Π₀ i, β i where
  toFun := toDFinsupp
  invFun := ofDFinsupp
  map_add' _ _ := rfl

lemma coe_addEquiv : ⇑(DirectSum.addEquiv β) = toDFinsupp := rfl

lemma coe_symm_addEquiv : ⇑(DirectSum.addEquiv β).symm = ofDFinsupp := rfl

/-- An additive map between the underlying finitely supported functions, as a map between the
direct sums. -/
def ofDFinsuppHom {κ : Type*} {γ : κ → Type*} [∀ k, AddCommMonoid (γ k)]
    (f : (Π₀ i, β i) →+ Π₀ k, γ k) : (⨁ i, β i) →+ ⨁ k, γ k :=
  (DirectSum.addEquiv γ).symm.toAddMonoidHom.comp (f.comp (DirectSum.addEquiv β).toAddMonoidHom)

@[simp]
lemma toDFinsupp_ofDFinsuppHom {κ : Type*} {γ : κ → Type*} [∀ k, AddCommMonoid (γ k)]
    (f : (Π₀ i, β i) →+ Π₀ k, γ k) (x : ⨁ i, β i) :
    (ofDFinsuppHom f x).toDFinsupp = f x.toDFinsupp :=
  rfl

lemma mker_ofDFinsuppHom {κ : Type*} {γ : κ → Type*} [∀ k, AddCommMonoid (γ k)]
    (f : (Π₀ i, β i) →+ Π₀ k, γ k) :
    AddMonoidHom.mker (ofDFinsuppHom f) =
      (AddMonoidHom.mker f).comap (DirectSum.addEquiv β).toAddMonoidHom :=
  AddSubmonoid.ext fun _ ↦ ofDFinsupp_eq_zero

lemma mrange_ofDFinsuppHom {κ : Type*} {γ : κ → Type*} [∀ k, AddCommMonoid (γ k)]
    (f : (Π₀ i, β i) →+ Π₀ k, γ k) :
    AddMonoidHom.mrange (ofDFinsuppHom f) =
      (AddMonoidHom.mrange f).comap (DirectSum.addEquiv γ).toAddMonoidHom :=
  AddSubmonoid.ext fun _ ↦
    ofDFinsupp_surjective.exists.trans (exists_congr fun _ ↦ toDFinsupp_inj.symm)

/-- The finite set of indices at which an element of the direct sum is nonzero. -/
def support [DecidableEq ι] [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (x : ⨁ i, β i) :
    Finset ι :=
  x.toDFinsupp.support

@[simp]
lemma support_toDFinsupp [DecidableEq ι] [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (x : ⨁ i, β i) :
    x.toDFinsupp.support = x.support :=
  rfl

@[simp]
lemma mem_support_iff [DecidableEq ι] [∀ (i : ι) (x : β i), Decidable (x ≠ 0)]
    {x : ⨁ i, β i} {i : ι} : i ∈ x.support ↔ x i ≠ 0 :=
  DFinsupp.mem_support_iff

lemma notMem_support_iff [DecidableEq ι] [∀ (i : ι) (x : β i), Decidable (x ≠ 0)]
    {x : ⨁ i, β i} {i : ι} : i ∉ x.support ↔ x i = 0 :=
  DFinsupp.notMem_support_iff

@[simp]
theorem zero_apply (i : ι) : (0 : ⨁ i, β i) i = 0 :=
  rfl

@[simp]
theorem add_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ + g₂) i = g₁ i + g₂ i :=
  rfl

@[simp]
theorem sum_apply {α} (s : Finset α) (g : α → ⨁ i, β i) (i : ι) :
    (∑ a ∈ s, g a) i = ∑ a ∈ s, g a i :=
  (congrFun (map_sum (coeFnAddMonoidHom β) g s) i).trans (Finset.sum_apply i s _)

section DecidableEq

variable [DecidableEq ι]

variable (β)

/-- `mk β s x` is the element of `⨁ i, β i` that is zero outside `s`
and has coefficient `x i` for `i` in `s`. -/
def mk (s : Finset ι) : (∀ i : (↑s : Set ι), β i.1) →+ ⨁ i, β i :=
  (DirectSum.addEquiv β).symm.toAddMonoidHom.comp
    { toFun := DFinsupp.mk s, map_zero' := DFinsupp.mk_zero, map_add' _ _ := DFinsupp.mk_add }

/-- `of i` is the natural inclusion map from `β i` to `⨁ i, β i`. -/
def of (i : ι) : β i →+ ⨁ i, β i :=
  (DirectSum.addEquiv β).symm.toAddMonoidHom.comp (DFinsupp.singleAddHom β i)

variable {β}

@[simp]
lemma toDFinsupp_mk (s : Finset ι) (x : ∀ i : (↑s : Set ι), β i.1) :
    (mk β s x).toDFinsupp = DFinsupp.mk s x :=
  rfl

@[simp]
lemma toDFinsupp_of (i : ι) (x : β i) : (of β i x).toDFinsupp = DFinsupp.single i x :=
  rfl

@[simp]
lemma ofDFinsupp_single (i : ι) (x : β i) : ofDFinsupp (DFinsupp.single i x) = of β i x :=
  rfl

@[simp]
theorem of_eq_same (i : ι) (x : β i) : (of _ i x) i = x :=
  DFinsupp.single_eq_same

theorem of_eq_of_ne (i j : ι) (x : β i) (h : j ≠ i) : (of _ i x) j = 0 :=
  DFinsupp.single_eq_of_ne h

lemma of_apply {i : ι} (j : ι) (x : β i) : of β i x j = if h : i = j then Eq.recOn h x else 0 :=
  DFinsupp.single_apply

theorem mk_apply_of_mem {s : Finset ι} {f : ∀ i : (↑s : Set ι), β i.val} {n : ι} (hn : n ∈ s) :
    mk β s f n = f ⟨n, hn⟩ :=
  DFinsupp.mk_of_mem hn

theorem mk_apply_of_notMem {s : Finset ι} {f : ∀ i : (↑s : Set ι), β i.val} {n : ι} (hn : n ∉ s) :
    mk β s f n = 0 :=
  DFinsupp.mk_of_notMem hn

@[simp]
theorem support_zero [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] : (0 : ⨁ i, β i).support = ∅ :=
  DFinsupp.support_zero

@[simp]
theorem support_of [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (i : ι) (x : β i) (h : x ≠ 0) :
    (of _ i x).support = {i} :=
  DFinsupp.support_single h

theorem support_of_subset [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] {i : ι} {b : β i} :
    (of _ i b).support ⊆ {i} :=
  DFinsupp.support_single_subset

theorem sum_support_of [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (x : ⨁ i, β i) :
    (∑ i ∈ x.support, of β i (x i)) = x :=
  (DirectSum.addEquiv β).injective <|
    (map_sum (DirectSum.addEquiv β) _ _).trans (DFinsupp.sum_single (f := x.toDFinsupp))

theorem sum_univ_of [Fintype ι] (x : ⨁ i, β i) :
    ∑ i ∈ Finset.univ, of β i (x i) = x := by
  ext i
  simp [of_apply]

theorem mk_injective (s : Finset ι) : Function.Injective (mk β s) :=
  ofDFinsupp_injective.comp (DFinsupp.mk_injective s)

theorem of_injective (i : ι) : Function.Injective (of β i) :=
  ofDFinsupp_injective.comp DFinsupp.single_injective

@[elab_as_elim]
protected theorem induction_on {motive : (⨁ i, β i) → Prop} (x : ⨁ i, β i) (zero : motive 0)
    (of : ∀ (i : ι) (x : β i), motive (of β i x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive x := by
  rw [← ofDFinsupp_toDFinsupp x]
  induction x.toDFinsupp using DFinsupp.induction with
  | h0 => exact zero
  | ha i b f _ _ ih => exact add _ _ (of i b) ih

/-- An alternative induction, where the addition assumption is restricted to singles. -/
@[elab_as_elim]
protected theorem induction_on' {motive : (⨁ i, β i) → Prop} (f : ⨁ i, β i) (h0 : motive 0)
    (hadd : ∀ (i b) (f : ⨁ i, β i), f i = 0 → b ≠ 0 → motive f → motive (of β i b + f)) :
    motive f := by
  rw [← ofDFinsupp_toDFinsupp f]
  induction f.toDFinsupp using DFinsupp.induction with
  | h0 => exact h0
  | ha i b f h1 h2 ih => exact hadd i b (ofDFinsupp f) h1 h2 ih

/-- If two additive homomorphisms from `⨁ i, β i` are equal on each `of β i y`,
then they are equal. -/
theorem addHom_ext {γ : Type*} [AddZeroClass γ] ⦃f g : (⨁ i, β i) →+ γ⦄
    (H : ∀ (i : ι) (y : β i), f (of _ i y) = g (of _ i y)) : f = g :=
  (AddMonoidHom.cancel_right (f := (DirectSum.addEquiv β).symm.toAddMonoidHom)
    (DirectSum.addEquiv β).symm.surjective).1 <| DFinsupp.addHom_ext H

/-- If two additive homomorphisms from `⨁ i, β i` are equal on each `of β i y`,
then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext high]
theorem addHom_ext' {γ : Type*} [AddZeroClass γ] ⦃f g : (⨁ i, β i) →+ γ⦄
    (H : ∀ i : ι, f.comp (of _ i) = g.comp (of _ i)) : f = g :=
  addHom_ext fun i => DFunLike.congr_fun <| H i

variable {γ : Type u₁} [AddCommMonoid γ]

section ToAddMonoid

variable (φ : ∀ i, β i →+ γ) (ψ : (⨁ i, β i) →+ γ)

-- Porting note: The elaborator is struggling with `liftAddHom`. Passing it `β` explicitly helps.
-- This applies to roughly the remainder of the file.

/-- `toAddMonoid φ` is the natural homomorphism from `⨁ i, β i` to `γ`
induced by a family `φ` of homomorphisms `β i → γ`. -/
def toAddMonoid : (⨁ i, β i) →+ γ :=
  (DFinsupp.liftAddHom (β := β) φ).comp (DirectSum.addEquiv β).toAddMonoidHom

@[simp]
theorem toAddMonoid_of (i) (x : β i) : toAddMonoid φ (of β i x) = φ i x :=
  DFinsupp.liftAddHom_apply_single φ i x

theorem toAddMonoid.unique (f : ⨁ i, β i) : ψ f = toAddMonoid (fun i => ψ.comp (of β i)) f :=
  DFunLike.congr_fun (addHom_ext (f := ψ) fun i x => by simp) f

lemma toAddMonoid_injective : Injective (toAddMonoid : (∀ i, β i →+ γ) → (⨁ i, β i) →+ γ) :=
  fun f g h => funext fun i => AddMonoidHom.ext fun x => by
    simpa using DFunLike.congr_fun h (of β i x)

@[simp] lemma toAddMonoid_inj {f g : ∀ i, β i →+ γ} : toAddMonoid f = toAddMonoid g ↔ f = g :=
  toAddMonoid_injective.eq_iff

end ToAddMonoid

section FromAddMonoid

/-- `fromAddMonoid φ` is the natural homomorphism from `γ` to `⨁ i, β i`
induced by a family `φ` of homomorphisms `γ → β i`.

Note that this is not an isomorphism. Not every homomorphism `γ →+ ⨁ i, β i` arises in this way. -/
def fromAddMonoid : (⨁ i, γ →+ β i) →+ γ →+ ⨁ i, β i :=
  toAddMonoid fun i => AddMonoidHom.compHom (of β i)

@[simp]
theorem fromAddMonoid_of (i : ι) (f : γ →+ β i) : fromAddMonoid (of _ i f) = (of _ i).comp f := by
  rw [fromAddMonoid, toAddMonoid_of]
  rfl

theorem fromAddMonoid_of_apply (i : ι) (f : γ →+ β i) (x : γ) :
    fromAddMonoid (of _ i f) x = of _ i (f x) := by
      rw [fromAddMonoid_of, AddMonoidHom.coe_comp, Function.comp]

end FromAddMonoid

variable (β)

-- TODO: generalize this to remove the assumption `S ⊆ T`.
/-- `setToSet β S T h` is the natural homomorphism `⨁ (i : S), β i → ⨁ (i : T), β i`,
where `h : S ⊆ T`. -/
def setToSet (S T : Set ι) (H : S ⊆ T) : (⨁ i : S, β i) →+ ⨁ i : T, β i :=
  toAddMonoid fun i => of (fun i : T => β i) ⟨↑i, H i.2⟩

end DecidableEq

instance unique [∀ i, Subsingleton (β i)] : Unique (⨁ i, β i) :=
  inferInstanceAs (Unique (Π₀ i, β i))

/-- A direct sum over an empty type is trivial. -/
instance uniqueOfIsEmpty [IsEmpty ι] : Unique (⨁ i, β i) :=
  inferInstanceAs (Unique (Π₀ i, β i))

/-- The natural equivalence between `⨁ _ : ι, M` and `M` when `Unique ι`. -/
protected def id (M : Type v) (ι : Type* := PUnit) [AddCommMonoid M] [Unique ι] :
    (⨁ _ : ι, M) ≃+ M :=
  { DirectSum.toAddMonoid fun _ => AddMonoidHom.id M with
    toFun := DirectSum.toAddMonoid fun _ => AddMonoidHom.id M
    invFun := of (fun _ => M) default
    left_inv x :=
      DirectSum.induction_on x
        (by rw [map_zero, map_zero])
        (fun p x => by rw [Unique.default_eq p, toAddMonoid_of, AddMonoidHom.id_apply])
        (fun x y ihx ihy => by grind)
    right_inv _ := toAddMonoid_of _ _ _ }

@[simp] lemma id_symm_apply {M : Type v} {ι : Type*} [AddCommMonoid M] [Unique ι] (x : M) :
    (DirectSum.id M ι).symm x = of _ default x :=
  rfl

@[simp] lemma id_apply {M : Type v} {ι : Type*} [AddCommMonoid M] [Unique ι] (x : ⨁ _ : ι, M) :
    DirectSum.id M ι x = x default := by
  rw [← AddEquiv.eq_symm_apply, id_symm_apply, eq_comm]
  induction x using DirectSum.induction_on <;> simp [Unique.eq_default, *]

section CongrLeft

variable {κ : Type*}

/-- Reindexing terms of a direct sum: change indexing type from `ι` to `κ` along an equivalence
`h : ι ≃ κ`. -/
def equivCongrLeft (h : ι ≃ κ) : (⨁ i, β i) ≃+ ⨁ k, β (h.symm k) :=
  (DirectSum.addEquiv β).trans <| AddEquiv.trans
    { DFinsupp.equivCongrLeft h with map_add' := DFinsupp.comapDomain'_add _ h.right_inv }
    (DirectSum.addEquiv _).symm

@[simp]
theorem equivCongrLeft_apply (h : ι ≃ κ) (f : ⨁ i, β i) (k : κ) :
    equivCongrLeft h f k = f (h.symm k) :=
  DFinsupp.comapDomain'_apply _ h.right_inv _ _

@[simp]
theorem equivCongrLeft_of [DecidableEq ι] [DecidableEq κ] (h : ι ≃ κ) (k : κ) (x : β (h.symm k)) :
    equivCongrLeft h (of β (h.symm k) x) = of (fun k ↦ β (h.symm k)) k x :=
  congrArg ofDFinsupp <| DFinsupp.comapDomain'_single h.symm h.right_inv _ _

end CongrLeft

section Option

variable {α : Option ι → Type w} [∀ i, AddCommMonoid (α i)]

/-- Isomorphism obtained by separating the term of index `none` of a direct sum over `Option ι`. -/
@[simps!]
noncomputable def addEquivProdDirectSum : (⨁ i, α i) ≃+ α none × ⨁ i, α (some i) :=
  { (DirectSum.equiv α).trans <| DFinsupp.equivProdDFinsupp.trans <|
      (Equiv.refl _).prodCongr (DirectSum.equiv _).symm with
    map_add' f g := congrArg (Prod.map id ofDFinsupp) <|
      DFinsupp.equivProdDFinsupp_add f.toDFinsupp g.toDFinsupp }

end Option

section Sigma

variable [DecidableEq ι] {α : ι → Type u} {δ : ∀ i, α i → Type w} [∀ i j, AddCommMonoid (δ i j)]

/-- The natural map between `⨁ (i : Σ i, α i), δ i.1 i.2` and `⨁ i (j : α i), δ i j`. -/
def sigmaCurry : (⨁ i : Σ _i, _, δ i.1 i.2) →+ ⨁ (i) (j), δ i j :=
  ofDFinsuppHom <|
    (DFinsupp.mapRange.addMonoidHom fun i ↦ (DirectSum.addEquiv (δ i)).symm.toAddMonoidHom).comp
      { toFun := DFinsupp.sigmaCurry (δ := δ)
        map_zero' := DFinsupp.sigmaCurry_zero
        map_add' := DFinsupp.sigmaCurry_add }

@[simp]
theorem sigmaCurry_apply (f : ⨁ i : Σ _i, _, δ i.1 i.2) (i : ι) (j : α i) :
    sigmaCurry f i j = f ⟨i, j⟩ :=
  DFinsupp.sigmaCurry_apply (δ := δ) _ i j

@[simp]
theorem sigmaCurry_of [∀ i : ι, DecidableEq (α i)] (k : (i : ι) × α i) (x : δ k.1 k.2) :
    sigmaCurry (of (fun k ↦ δ k.1 k.2) k x) =
      of (fun i' ↦ ⨁ (j' : α i'), δ i' j') k.1 (of (fun j' ↦ δ k.1 j') k.2 x) :=
  congrArg ofDFinsupp <| (congrArg _ (DFinsupp.sigmaCurry_single k x)).trans <|
    DFinsupp.mapRange_single (hf := fun _ ↦ map_zero _)

/-- The natural map between `⨁ i (j : α i), δ i j` and `Π₀ (i : Σ i, α i), δ i.1 i.2`, inverse of
`curry`. -/
def sigmaUncurry : (⨁ (i) (j), δ i j) →+ ⨁ i : Σ _i, _, δ i.1 i.2 :=
  ofDFinsuppHom <|
    AddMonoidHom.comp
      { toFun := DFinsupp.sigmaUncurry (δ := δ)
        map_zero' := DFinsupp.sigmaUncurry_zero
        map_add' := DFinsupp.sigmaUncurry_add }
      (DFinsupp.mapRange.addMonoidHom fun i ↦ (DirectSum.addEquiv (δ i)).toAddMonoidHom)

@[simp]
theorem sigmaUncurry_apply (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i) :
    sigmaUncurry f ⟨i, j⟩ = f i j :=
  DFinsupp.sigmaUncurry_apply _ i j

/-- The natural map between `⨁ (i : Σ i, α i), δ i.1 i.2` and `⨁ i (j : α i), δ i j`. -/
def sigmaCurryEquiv : (⨁ i : Σ _i, _, δ i.1 i.2) ≃+ ⨁ (i) (j), δ i j :=
  { sigmaCurry with
    invFun := sigmaUncurry
    left_inv f := by ext ⟨i, j⟩; simp
    right_inv f := by ext i j; simp }

end Sigma

section SigmaFiber

variable {ι₁ ι₂ : Type v} [DecidableEq ι₂] (f : ι₁ → ι₂)
variable {β : ι₁ → Type w} [Π i, AddCommMonoid (β i)]

/-- The equivalence between a direct sum indexed by a type `ι₁` and the double sum indexed by a type
`ι₂` together with the fibres of a map `f : ι₁ → ι₂`. -/
def sigmaFiberAddEquiv : (⨁ i, β i) ≃+ ⨁ (j : ι₂) (i : { i : ι₁ // f i = j}), β ↑i :=
  (equivCongrLeft (Equiv.sigmaFiberEquiv f).symm).trans
    (sigmaCurryEquiv (δ := fun j ↦ (fun (i : { i : ι₁ // f i = j}) ↦ β i)))

theorem sigmaFiberAddEquiv_apply (x : ⨁ i, β i) :
    sigmaFiberAddEquiv f x = sigmaCurry (equivCongrLeft (Equiv.sigmaFiberEquiv f).symm x) := rfl

@[simp]
theorem sigmaFiberAddEquiv_apply_apply (x : ⨁ i, β i) (j : ι₂) (i' : { i : ι₁ // f i = j}) :
    sigmaFiberAddEquiv f x j i' = x i' := rfl

@[simp]
theorem sigmaFiberAddEquiv_of [DecidableEq ι₁] (i : ι₁) (x : β i) :
    sigmaFiberAddEquiv f (of _ i x) = of _ (f i) (of _ ⟨i, rfl⟩ x) :=
  let h := Equiv.sigmaFiberEquiv f
  let k : (j : ι₂) × {i₁ : ι₁ // f i₁ = j} := ⟨f i, ⟨i, rfl⟩⟩
  calc sigmaFiberAddEquiv f (of β (h k) x)
    _ = sigmaCurry (of (fun k : (j' : ι₂) × {i // f i = j'} ↦ β k.2) k x) := by
      rw [sigmaFiberAddEquiv_apply]
      exact congrArg sigmaCurry (equivCongrLeft_of (h := h.symm) _ _)
    _ = of _ k.1 (of _ k.2 x) := by simp

end SigmaFiber

/-- The canonical embedding from `⨁ i, A i` to `M` where `A` is a collection of `AddSubmonoid M`
indexed by `ι`.

When `S = Submodule _ M`, this is available as a `LinearMap`, `DirectSum.coe_linearMap`. -/
protected def coeAddMonoidHom {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι → S) : (⨁ i, A i) →+ M :=
  toAddMonoid fun i => AddSubmonoidClass.subtype (A i)

theorem coeAddMonoidHom_eq_dfinsuppSum [DecidableEq ι]
    {M S : Type*} [DecidableEq M] [AddCommMonoid M]
    [SetLike S M] [AddSubmonoidClass S M] (A : ι → S) (x : DirectSum ι fun i => A i) :
    DirectSum.coeAddMonoidHom A x = x.toDFinsupp.sum fun i => (fun x : A i => ↑x) :=
  DFinsupp.sumAddHom_apply _ x.toDFinsupp

@[simp]
theorem coeAddMonoidHom_of {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι → S) (i : ι) (x : A i) :
    DirectSum.coeAddMonoidHom A (of (fun i => A i) i x) = x :=
  toAddMonoid_of _ _ _

theorem coe_of_apply {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] {A : ι → S} (i j : ι) (x : A i) :
    (of (fun i ↦ {x // x ∈ A i}) i x j : M) = if i = j then x else 0 := by
  obtain rfl | h := Decidable.eq_or_ne j i
  · rw [DirectSum.of_eq_same, ite_eq_left rfl]
  · rw [DirectSum.of_eq_of_ne _ _ _ h, ite_eq_right h.symm, ZeroMemClass.coe_zero,
      ZeroMemClass.coe_zero]

/-- The `DirectSum` formed by a collection of additive submonoids (or subgroups, or submodules) of
`M` is said to be internal if the canonical map `(⨁ i, A i) →+ M` is bijective.

For the alternate statement in terms of independence and spanning, see
`DirectSum.subgroup_isInternal_iff_iSupIndep_and_supr_eq_top` and
`DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`. -/
def IsInternal {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι → S) : Prop :=
  Function.Bijective (DirectSum.coeAddMonoidHom A)

theorem IsInternal.addSubmonoid_iSup_eq_top {M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (A : ι → AddSubmonoid M) (h : IsInternal A) : iSup A = ⊤ := by
  rw [AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom, AddMonoidHom.mrange_eq_top]
  exact h.surjective.of_comp (g := toDFinsupp)

variable {M S : Type*} [AddCommMonoid M] [SetLike S M] [AddSubmonoidClass S M]

theorem support_subset [DecidableEq ι] [DecidableEq M] (A : ι → S) (x : DirectSum ι fun i => A i) :
    (Function.support fun i => (x i : M)) ⊆ ↑x.support := by
  intro m
  simp only [Function.mem_support, Finset.mem_coe, mem_support_iff, ne_eq,
    ZeroMemClass.coe_eq_zero, imp_self]

theorem hasFiniteSupport (A : ι → S) (x : DirectSum ι fun i => A i) :
    (fun i => (x i : M)).HasFiniteSupport := by
  classical
  exact x.support.finite_toSet.subset (DirectSum.support_subset _ x)

@[deprecated (since := "2026-03-03")] alias finite_support := hasFiniteSupport

section map

variable {ι : Type*} {α : ι → Type*} {β : ι → Type*} [∀ i, AddCommMonoid (α i)]
variable [∀ i, AddCommMonoid (β i)] (f : ∀ (i : ι), α i →+ β i)

/-- create a homomorphism from `⨁ i, α i` to `⨁ i, β i` by giving the component-wise map `f`. -/
def map : (⨁ i, α i) →+ ⨁ i, β i :=
  ofDFinsuppHom (DFinsupp.mapRange.addMonoidHom f)

@[simp] lemma toDFinsupp_map (x : ⨁ i, α i) :
    (map f x).toDFinsupp = DFinsupp.mapRange.addMonoidHom f x.toDFinsupp :=
  rfl

@[simp] lemma map_of [DecidableEq ι] (i : ι) (x : α i) : map f (of α i x) = of β i (f i x) :=
  congrArg ofDFinsupp <| DFinsupp.mapRange_single (hf := fun _ => map_zero _)

@[simp] lemma map_apply (i : ι) (x : ⨁ i, α i) : map f x i = f i (x i) :=
  DFinsupp.mapRange_apply (hf := fun _ => map_zero _) _ _ _

@[simp] lemma map_id :
    (map (fun i ↦ AddMonoidHom.id (α i))) = AddMonoidHom.id (⨁ i, α i) :=
  AddMonoidHom.ext fun _ ↦ ext fun _ ↦ rfl

@[simp] lemma map_comp {γ : ι → Type*} [∀ i, AddCommMonoid (γ i)]
    (g : ∀ (i : ι), β i →+ γ i) :
    (map (fun i ↦ (g i).comp (f i))) = (map g).comp (map f) :=
  AddMonoidHom.ext fun _ ↦ ext fun _ ↦ rfl

lemma map_injective : Function.Injective (map f) ↔ ∀ i, Function.Injective (f i) := by
  change Injective ((DirectSum.equiv β).symm ∘ DFinsupp.mapRange.addMonoidHom f ∘
    DirectSum.equiv α) ↔ _
  rw [Equiv.comp_injective, Equiv.injective_comp]
  exact DFinsupp.mapRange_injective (hf := fun _ ↦ map_zero _)

lemma map_surjective : Function.Surjective (map f) ↔ (∀ i, Function.Surjective (f i)) := by
  change Surjective ((DirectSum.equiv β).symm ∘ DFinsupp.mapRange.addMonoidHom f ∘
    DirectSum.equiv α) ↔ _
  rw [Equiv.comp_surjective, Equiv.surjective_comp]
  exact DFinsupp.mapRange_surjective (hf := fun _ ↦ map_zero _)

lemma map_eq_iff (x y : ⨁ i, α i) :
    map f x = map f y ↔ ∀ i, f i (x i) = f i (y i) := by
  simp_rw [DirectSum.ext_iff, map_apply]

end map

end DirectSum

/-- The canonical isomorphism of a finite direct sum of additive commutative monoids
and the corresponding finite product. -/
def DirectSum.addEquivProd {ι : Type*} [Fintype ι] (G : ι → Type*) [(i : ι) → AddCommMonoid (G i)] :
    DirectSum ι G ≃+ ((i : ι) → G i) :=
  (DirectSum.addEquiv G).trans ⟨DFinsupp.equivFunOnFintype, fun g h ↦ funext fun _ ↦ by
    simp only [DFinsupp.equivFunOnFintype, Equiv.toFun_as_coe, Equiv.coe_fn_mk,
      ← DFinsupp.add_apply, Pi.add_apply]⟩
