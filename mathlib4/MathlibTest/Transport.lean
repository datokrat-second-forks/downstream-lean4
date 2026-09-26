import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Group.Action.TransferInstance
import Mathlib.Algebra.Group.Hom.Defs

/-!
Tests for the `@[transport]` congruences of Mathlib's classes: each instance is transported without
the warning that transport emits when it cannot unfold a congruence, its operations reduce to the
`newtype`'s constructor and projector, and diamonds between transported instances close with
`with_reducible_and_instances rfl`.
-/

newtype Wrap (M : Type*) where
  unwrap : M

namespace Wrap

variable {R S M : Type*}

#guard_msgs in
instance instVAdd [VAdd R M] : VAdd R (Wrap M) := inferInstanceAs (VAdd R M)
#guard_msgs in
instance instSMul [SMul R M] : SMul R (Wrap M) := inferInstanceAs (SMul R M)
#guard_msgs in
instance instCommMonoid [CommMonoid M] : CommMonoid (Wrap M) := inferInstanceAs (CommMonoid M)
#guard_msgs in
instance instAddCommMonoid [AddCommMonoid M] : AddCommMonoid (Wrap M) :=
  inferInstanceAs (AddCommMonoid M)
#guard_msgs in
instance instCommGroup [CommGroup M] : CommGroup (Wrap M) := inferInstanceAs (CommGroup M)
#guard_msgs in
instance instAddCommGroup [AddCommGroup M] : AddCommGroup (Wrap M) :=
  inferInstanceAs (AddCommGroup M)
#guard_msgs in
instance instModule [Semiring R] [AddCommMonoid M] [Module R M] : Module R (Wrap M) :=
  inferInstanceAs (Module R M)
#guard_msgs in
instance [SMul R M] [SMul S M] [SMulCommClass R S M] : SMulCommClass R S (Wrap M) :=
  inferInstanceAs (SMulCommClass R S M)
#guard_msgs in
instance [VAdd R M] [VAdd S M] [VAddCommClass R S M] : VAddCommClass R S (Wrap M) :=
  inferInstanceAs (VAddCommClass R S M)
#guard_msgs in
instance [SMul R S] [SMul S M] [SMul R M] [IsScalarTower R S M] : IsScalarTower R S (Wrap M) :=
  inferInstanceAs (IsScalarTower R S M)
#guard_msgs in
instance [SMul R M] [SMul Rᵐᵒᵖ M] [IsCentralScalar R M] : IsCentralScalar R (Wrap M) :=
  inferInstanceAs (IsCentralScalar R M)
#guard_msgs in
instance [Unique M] : Unique (Wrap M) := inferInstanceAs (Unique M)

example [AddCommMonoid M] (x y : Wrap M) : x + y = .mk (x.unwrap + y.unwrap) := by
  with_reducible_and_instances rfl
example [AddCommMonoid M] : (0 : Wrap M) = .mk 0 := by with_reducible_and_instances rfl
example [AddCommMonoid M] (n : ℕ) (x : Wrap M) : n • x = .mk (n • x.unwrap) := by
  with_reducible_and_instances rfl
example [CommGroup M] (x y : Wrap M) : x / y = .mk (x.unwrap / y.unwrap) := by
  with_reducible_and_instances rfl
example [CommGroup M] (x : Wrap M) : x⁻¹ = .mk x.unwrap⁻¹ := by with_reducible_and_instances rfl
example [Semiring R] [AddCommMonoid M] [Module R M] (r : R) (x : Wrap M) :
    r • x = .mk (r • x.unwrap) := by
  with_reducible_and_instances rfl
example [Unique M] : (default : Wrap M) = .mk default := by with_reducible_and_instances rfl

example [AddCommGroup M] :
    (AddCommGroup.toAddCommMonoid : AddCommMonoid (Wrap M)) = instAddCommMonoid := by
  with_reducible_and_instances rfl
example [CommGroup M] : (CommGroup.toCommMonoid : CommMonoid (Wrap M)) = instCommMonoid := by
  with_reducible_and_instances rfl
example [Semiring R] [AddCommMonoid M] [Module R M] :
    (Module.toDistribMulAction.toMulAction.toSMul : SMul R (Wrap M)) = instSMul := by
  with_reducible_and_instances rfl
example [AddCommMonoid M] : (NSMul.toSMul : SMul ℕ (Wrap M)) = instSMul := by
  with_reducible_and_instances rfl

end Wrap

/-! `DFunLike` moves along an equivalence of the bundled type. -/

newtype WrapHom (M N : Type*) [AddZeroClass M] [AddZeroClass N] where
  toHom : M →+ N

#guard_msgs in
instance {M N : Type*} [AddZeroClass M] [AddZeroClass N] : FunLike (WrapHom M N) M N :=
  inferInstanceAs (FunLike (M →+ N) M N)

example {M N : Type*} [AddZeroClass M] [AddZeroClass N] (f : WrapHom M N) (x : M) :
    f x = f.toHom x := by
  with_reducible_and_instances rfl
