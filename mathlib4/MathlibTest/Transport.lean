import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Action.TransferInstance
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Action.Transport
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Module.Synonym
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Fintype.Defs
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Logic.Small.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Bases
import Mathlib.Topology.Bornology.Constructions
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Separation.Hausdorff

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
#guard_msgs in
instance [Semiring R] [AddCommMonoid M] [Module R M] [Module.Finite R M] :
    Module.Finite R (Wrap M) :=
  inferInstanceAs (Module.Finite R M)
#guard_msgs in
instance [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M] : Module.Free R (Wrap M) :=
  inferInstanceAs (Module.Free R M)
#guard_msgs in
instance [Nontrivial M] : Nontrivial (Wrap M) := inferInstanceAs (Nontrivial M)
#guard_msgs in
instance instTopologicalSpace [TopologicalSpace M] : TopologicalSpace (Wrap M) :=
  inferInstanceAs (TopologicalSpace M)
#guard_msgs in
instance [TopologicalSpace M] [T2Space M] : T2Space (Wrap M) := inferInstanceAs (T2Space M)
#guard_msgs in
instance [TopologicalSpace M] [PathConnectedSpace M] : PathConnectedSpace (Wrap M) :=
  inferInstanceAs (PathConnectedSpace M)
#guard_msgs in
instance [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M] :
    IsTopologicalAddGroup (Wrap M) :=
  inferInstanceAs (IsTopologicalAddGroup M)
#guard_msgs in
instance [TopologicalSpace M] [CommGroup M] [IsTopologicalGroup M] : IsTopologicalGroup (Wrap M) :=
  inferInstanceAs (IsTopologicalGroup M)
#guard_msgs in
instance [TopologicalSpace R] [TopologicalSpace M] [SMul R M] [ContinuousSMul R M] :
    ContinuousSMul R (Wrap M) :=
  inferInstanceAs (ContinuousSMul R M)
#guard_msgs in
instance [TopologicalSpace M] [SMul R M] [ContinuousConstSMul R M] :
    ContinuousConstSMul R (Wrap M) :=
  inferInstanceAs (ContinuousConstSMul R M)

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
example [TopologicalSpace M] (s : Set (Wrap M)) :
    TopologicalSpace.IsOpen s ↔ TopologicalSpace.IsOpen (Wrap.mk ⁻¹' s) := by
  with_reducible_and_instances rfl

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

/-! The semigroup-to-group hierarchy, `Pow` on either side, and `Subsingleton`. -/

newtype WrapGroup (M : Type*) where
  unwrap : M

namespace WrapGroup

variable {M N : Type*}

#guard_msgs in
instance instPow [Pow M N] : Pow (WrapGroup M) N := inferInstanceAs (Pow M N)
#guard_msgs in
instance instPowRight [Pow M N] : Pow M (WrapGroup N) := inferInstanceAs (Pow M N)
#guard_msgs in
instance [Subsingleton M] : Subsingleton (WrapGroup M) := inferInstanceAs (Subsingleton M)
#guard_msgs in
instance instSemigroup [Semigroup M] : Semigroup (WrapGroup M) := inferInstanceAs (Semigroup M)
#guard_msgs in
instance [AddCommSemigroup M] : AddCommSemigroup (WrapGroup M) :=
  inferInstanceAs (AddCommSemigroup M)
#guard_msgs in
instance instMul [Mul M] : Mul (WrapGroup M) := inferInstanceAs (Mul M)
#guard_msgs in
instance [Mul M] [IsLeftCancelMul M] : IsLeftCancelMul (WrapGroup M) :=
  inferInstanceAs (IsLeftCancelMul M)
#guard_msgs in
instance [Mul M] [IsRightCancelMul M] : IsRightCancelMul (WrapGroup M) :=
  inferInstanceAs (IsRightCancelMul M)
#guard_msgs in
instance instMulOneClass [MulOneClass M] : MulOneClass (WrapGroup M) :=
  inferInstanceAs (MulOneClass M)
#guard_msgs in
instance instMonoid [Monoid M] : Monoid (WrapGroup M) := inferInstanceAs (Monoid M)
#guard_msgs in
instance [LeftCancelMonoid M] : LeftCancelMonoid (WrapGroup M) :=
  inferInstanceAs (LeftCancelMonoid M)
#guard_msgs in
instance [RightCancelMonoid M] : RightCancelMonoid (WrapGroup M) :=
  inferInstanceAs (RightCancelMonoid M)
#guard_msgs in
instance [CancelMonoid M] : CancelMonoid (WrapGroup M) := inferInstanceAs (CancelMonoid M)
#guard_msgs in
instance [AddCancelCommMonoid M] : AddCancelCommMonoid (WrapGroup M) :=
  inferInstanceAs (AddCancelCommMonoid M)
#guard_msgs in
instance [InvolutiveInv M] : InvolutiveInv (WrapGroup M) := inferInstanceAs (InvolutiveInv M)
#guard_msgs in
instance instDivInvMonoid [DivInvMonoid M] : DivInvMonoid (WrapGroup M) :=
  inferInstanceAs (DivInvMonoid M)
#guard_msgs in
instance instDivisionMonoid [DivisionMonoid M] : DivisionMonoid (WrapGroup M) :=
  inferInstanceAs (DivisionMonoid M)
#guard_msgs in
instance [DivisionCommMonoid M] : DivisionCommMonoid (WrapGroup M) :=
  inferInstanceAs (DivisionCommMonoid M)
#guard_msgs in
instance instGroup [Group M] : Group (WrapGroup M) := inferInstanceAs (Group M)
#guard_msgs in
instance [AddGroup M] : AddGroup (WrapGroup M) := inferInstanceAs (AddGroup M)

example [Pow M N] (x : WrapGroup M) (n : N) : x ^ n = .mk (x.unwrap ^ n) := by
  with_reducible_and_instances rfl
example [Pow M N] (x : M) (n : WrapGroup N) : x ^ n = x ^ n.unwrap := by
  with_reducible_and_instances rfl
example [Monoid M] (x : WrapGroup M) (n : ℕ) : x ^ n = .mk (x.unwrap ^ n) := by
  with_reducible_and_instances rfl
example [Group M] (x : WrapGroup M) (n : ℤ) : x ^ n = .mk (x.unwrap ^ n) := by
  with_reducible_and_instances rfl

example [Monoid M] : (Monoid.toSemigroup : Semigroup (WrapGroup M)) = instSemigroup := by
  with_reducible_and_instances rfl
example [Monoid M] : (Monoid.toMulOneClass : MulOneClass (WrapGroup M)) = instMulOneClass := by
  with_reducible_and_instances rfl
example [Monoid M] : (NPow.toPow : Pow (WrapGroup M) ℕ) = instPow := by
  with_reducible_and_instances rfl
example [Group M] : (Group.toDivisionMonoid : DivisionMonoid (WrapGroup M)) = instDivisionMonoid :=
  by with_reducible_and_instances rfl
example [Group M] : (Group.toDivInvMonoid : DivInvMonoid (WrapGroup M)) = instDivInvMonoid := by
  with_reducible_and_instances rfl
example [DivInvMonoid M] : (DivInvMonoid.toMonoid : Monoid (WrapGroup M)) = instMonoid := by
  with_reducible_and_instances rfl

end WrapGroup

/-!
Tests for the `@[transport]` congruences of the monoid-with-zero and group-with-zero classes and of
the action classes in the positions of the scalars and of the acted-on type: each instance is
transported without the warning that transport emits when it cannot unfold a congruence, its
operations reduce to the `newtype`'s constructor and projector, and diamonds between transported
instances close with `with_reducible_and_instances rfl`.
-/

newtype WrapGroupWithZero (M : Type*) where
  unwrap : M

namespace WrapGroupWithZero

variable {R S M : Type*}

/-! ### Monoids and groups with zero -/

#guard_msgs in
instance instZero [Zero M] : Zero (WrapGroupWithZero M) := inferInstanceAs (Zero M)
#guard_msgs in
instance instMul [Mul M] : Mul (WrapGroupWithZero M) := inferInstanceAs (Mul M)
#guard_msgs in
instance instMonoid [Monoid M] : Monoid (WrapGroupWithZero M) := inferInstanceAs (Monoid M)
#guard_msgs in
instance instDivInvMonoid [DivInvMonoid M] : DivInvMonoid (WrapGroupWithZero M) :=
  inferInstanceAs (DivInvMonoid M)
#guard_msgs in
instance instMulZeroClass [MulZeroClass M] : MulZeroClass (WrapGroupWithZero M) :=
  inferInstanceAs (MulZeroClass M)
#guard_msgs in
instance instMulZeroOneClass [MulZeroOneClass M] : MulZeroOneClass (WrapGroupWithZero M) :=
  inferInstanceAs (MulZeroOneClass M)
#guard_msgs in
instance instSemigroupWithZero [SemigroupWithZero M] : SemigroupWithZero (WrapGroupWithZero M) :=
  inferInstanceAs (SemigroupWithZero M)
#guard_msgs in
instance instMonoidWithZero [MonoidWithZero M] : MonoidWithZero (WrapGroupWithZero M) :=
  inferInstanceAs (MonoidWithZero M)
#guard_msgs in
instance instCommMonoidWithZero [CommMonoidWithZero M] : CommMonoidWithZero (WrapGroupWithZero M) :=
  inferInstanceAs (CommMonoidWithZero M)
#guard_msgs in
instance instGroupWithZero [GroupWithZero M] : GroupWithZero (WrapGroupWithZero M) :=
  inferInstanceAs (GroupWithZero M)
#guard_msgs in
instance instCommGroupWithZero [CommGroupWithZero M] : CommGroupWithZero (WrapGroupWithZero M) :=
  inferInstanceAs (CommGroupWithZero M)
#guard_msgs in
instance [Mul M] [Zero M] [NoZeroDivisors M] : NoZeroDivisors (WrapGroupWithZero M) :=
  inferInstanceAs (NoZeroDivisors M)
#guard_msgs in
instance [Mul M] [Zero M] [IsLeftCancelMulZero M] : IsLeftCancelMulZero (WrapGroupWithZero M) :=
  inferInstanceAs (IsLeftCancelMulZero M)
#guard_msgs in
instance [Mul M] [Zero M] [IsRightCancelMulZero M] : IsRightCancelMulZero (WrapGroupWithZero M) :=
  inferInstanceAs (IsRightCancelMulZero M)

example [MonoidWithZero M] (x y : WrapGroupWithZero M) : x * y = .mk (x.unwrap * y.unwrap) := by
  with_reducible_and_instances rfl
example [MonoidWithZero M] : (0 : WrapGroupWithZero M) = .mk 0 := by with_reducible_and_instances rfl
example [MonoidWithZero M] : (1 : WrapGroupWithZero M) = .mk 1 := by with_reducible_and_instances rfl
example [MonoidWithZero M] (x : WrapGroupWithZero M) (n : ℕ) : x ^ n = .mk (x.unwrap ^ n) := by
  with_reducible_and_instances rfl
example [CommGroupWithZero M] (x y : WrapGroupWithZero M) : x / y = .mk (x.unwrap / y.unwrap) := by
  with_reducible_and_instances rfl
example [CommGroupWithZero M] (x : WrapGroupWithZero M) : x⁻¹ = .mk x.unwrap⁻¹ := by
  with_reducible_and_instances rfl
example [CommGroupWithZero M] (x : WrapGroupWithZero M) (n : ℤ) : x ^ n = .mk (x.unwrap ^ n) := by
  with_reducible_and_instances rfl

example [MulZeroClass M] : (MulZeroClass.toMul : Mul (WrapGroupWithZero M)) = instMul := by
  with_reducible_and_instances rfl
example [MulZeroClass M] : (MulZeroClass.toZero : Zero (WrapGroupWithZero M)) = instZero := by
  with_reducible_and_instances rfl
example [MulZeroOneClass M] :
    (MulZeroOneClass.toMulZeroClass : MulZeroClass (WrapGroupWithZero M)) = instMulZeroClass := by
  with_reducible_and_instances rfl
example [SemigroupWithZero M] :
    (SemigroupWithZero.toMulZeroClass : MulZeroClass (WrapGroupWithZero M)) = instMulZeroClass := by
  with_reducible_and_instances rfl
example [MonoidWithZero M] : (MonoidWithZero.toMonoid : Monoid (WrapGroupWithZero M)) = instMonoid := by
  with_reducible_and_instances rfl
example [MonoidWithZero M] :
    (MonoidWithZero.toMulZeroOneClass : MulZeroOneClass (WrapGroupWithZero M)) = instMulZeroOneClass := by
  with_reducible_and_instances rfl
example [MonoidWithZero M] :
    (MonoidWithZero.toSemigroupWithZero : SemigroupWithZero (WrapGroupWithZero M)) =
      instSemigroupWithZero := by
  with_reducible_and_instances rfl
example [CommMonoidWithZero M] :
    (CommMonoidWithZero.toMonoidWithZero : MonoidWithZero (WrapGroupWithZero M)) = instMonoidWithZero := by
  with_reducible_and_instances rfl
example [GroupWithZero M] :
    (GroupWithZero.toMonoidWithZero : MonoidWithZero (WrapGroupWithZero M)) = instMonoidWithZero := by
  with_reducible_and_instances rfl
example [GroupWithZero M] :
    (GroupWithZero.toDivInvMonoid : DivInvMonoid (WrapGroupWithZero M)) = instDivInvMonoid := by
  with_reducible_and_instances rfl
example [CommGroupWithZero M] :
    (CommGroupWithZero.toGroupWithZero : GroupWithZero (WrapGroupWithZero M)) = instGroupWithZero := by
  with_reducible_and_instances rfl
example [CommGroupWithZero M] :
    (CommGroupWithZero.toCommMonoidWithZero : CommMonoidWithZero (WrapGroupWithZero M)) =
      instCommMonoidWithZero := by
  with_reducible_and_instances rfl

/-! ### Actions, on the acted-on type and on the scalars -/

#guard_msgs in
instance instAddZeroClass [AddZeroClass M] : AddZeroClass (WrapGroupWithZero M) :=
  inferInstanceAs (AddZeroClass M)
#guard_msgs in
instance instAddMonoid [AddMonoid M] : AddMonoid (WrapGroupWithZero M) := inferInstanceAs (AddMonoid M)
#guard_msgs in
instance instSMul [SMul R M] : SMul R (WrapGroupWithZero M) := inferInstanceAs (SMul R M)
#guard_msgs in
instance instSMulLeft [SMul R M] : SMul (WrapGroupWithZero R) M := inferInstanceAs (SMul R M)
#guard_msgs in
instance instVAdd [VAdd R M] : VAdd R (WrapGroupWithZero M) := inferInstanceAs (VAdd R M)
#guard_msgs in
instance instVAddLeft [VAdd R M] : VAdd (WrapGroupWithZero R) M := inferInstanceAs (VAdd R M)
#guard_msgs in
instance instAddMonoidR [AddMonoid R] : AddMonoid (WrapGroupWithZero R) := inferInstanceAs (AddMonoid R)
#guard_msgs in
instance instMulAction [Monoid R] [MulAction R M] : MulAction R (WrapGroupWithZero M) :=
  inferInstanceAs (MulAction R M)
#guard_msgs in
instance instMulActionLeft [Monoid R] [MulAction R M] : MulAction (WrapGroupWithZero R) M :=
  inferInstanceAs (MulAction R M)
#guard_msgs in
instance instAddAction [AddMonoid R] [AddAction R M] : AddAction R (WrapGroupWithZero M) :=
  inferInstanceAs (AddAction R M)
#guard_msgs in
instance instAddActionLeft [AddMonoid R] [AddAction R M] : AddAction (WrapGroupWithZero R) M :=
  inferInstanceAs (AddAction R M)
#guard_msgs in
instance [SMul R M] [SMul S M] [SMulCommClass R S M] : SMulCommClass (WrapGroupWithZero R) S M :=
  inferInstanceAs (SMulCommClass R S M)
#guard_msgs in
instance [SMul R M] [SMul S M] [SMulCommClass R S M] : SMulCommClass R (WrapGroupWithZero S) M :=
  inferInstanceAs (SMulCommClass R S M)
#guard_msgs in
instance [VAdd R M] [VAdd S M] [VAddCommClass R S M] : VAddCommClass (WrapGroupWithZero R) S M :=
  inferInstanceAs (VAddCommClass R S M)
#guard_msgs in
instance [VAdd R M] [VAdd S M] [VAddCommClass R S M] : VAddCommClass R (WrapGroupWithZero S) M :=
  inferInstanceAs (VAddCommClass R S M)
#guard_msgs in
instance [SMul R M] [SMul S M] [SMulCommClass R S M] : SMulCommClass R S (WrapGroupWithZero M) :=
  inferInstanceAs (SMulCommClass R S M)
#guard_msgs in
instance [VAdd R M] [VAdd S M] [VAddCommClass R S M] : VAddCommClass R S (WrapGroupWithZero M) :=
  inferInstanceAs (VAddCommClass R S M)
#guard_msgs in
instance [SMul R S] [SMul S M] [SMul R M] [IsScalarTower R S M] :
    IsScalarTower R S (WrapGroupWithZero M) :=
  inferInstanceAs (IsScalarTower R S M)
#guard_msgs in
instance [VAdd R S] [VAdd S M] [VAdd R M] [VAddAssocClass R S M] :
    VAddAssocClass R S (WrapGroupWithZero M) :=
  inferInstanceAs (VAddAssocClass R S M)
#guard_msgs in
instance [SMul R M] [SMul Rᵐᵒᵖ M] [IsCentralScalar R M] : IsCentralScalar R (WrapGroupWithZero M) :=
  inferInstanceAs (IsCentralScalar R M)
#guard_msgs in
instance [VAdd R M] [VAdd Rᵃᵒᵖ M] [IsCentralVAdd R M] : IsCentralVAdd R (WrapGroupWithZero M) :=
  inferInstanceAs (IsCentralVAdd R M)
#guard_msgs in
instance [SMul R S] [SMul S M] [SMul R M] [IsScalarTower R S M] :
    IsScalarTower (WrapGroupWithZero R) S M :=
  inferInstanceAs (IsScalarTower R S M)
#guard_msgs in
instance [SMul R S] [SMul S M] [SMul R M] [IsScalarTower R S M] :
    IsScalarTower R (WrapGroupWithZero S) M :=
  inferInstanceAs (IsScalarTower R S M)
#guard_msgs in
instance [VAdd R S] [VAdd S M] [VAdd R M] [VAddAssocClass R S M] :
    VAddAssocClass (WrapGroupWithZero R) S M :=
  inferInstanceAs (VAddAssocClass R S M)
#guard_msgs in
instance [VAdd R S] [VAdd S M] [VAdd R M] [VAddAssocClass R S M] :
    VAddAssocClass R (WrapGroupWithZero S) M :=
  inferInstanceAs (VAddAssocClass R S M)
#guard_msgs in
instance instSMulZeroClass [Zero M] [SMulZeroClass R M] : SMulZeroClass R (WrapGroupWithZero M) :=
  inferInstanceAs (SMulZeroClass R M)
#guard_msgs in
instance instSMulZeroClassLeft [Zero M] [SMulZeroClass R M] : SMulZeroClass (WrapGroupWithZero R) M :=
  inferInstanceAs (SMulZeroClass R M)
#guard_msgs in
instance instSMulWithZero [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero R (WrapGroupWithZero M) :=
  inferInstanceAs (SMulWithZero R M)
#guard_msgs in
instance instSMulWithZeroLeft [Zero R] [Zero M] [SMulWithZero R M] :
    SMulWithZero (WrapGroupWithZero R) M :=
  inferInstanceAs (SMulWithZero R M)
#guard_msgs in
instance instDistribSMul [AddZeroClass M] [DistribSMul R M] : DistribSMul R (WrapGroupWithZero M) :=
  inferInstanceAs (DistribSMul R M)
#guard_msgs in
instance instDistribSMulLeft [AddZeroClass M] [DistribSMul R M] : DistribSMul (WrapGroupWithZero R) M :=
  inferInstanceAs (DistribSMul R M)
#guard_msgs in
instance instDistribMulAction [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    DistribMulAction R (WrapGroupWithZero M) :=
  inferInstanceAs (DistribMulAction R M)
#guard_msgs in
instance instDistribMulActionLeft [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    DistribMulAction (WrapGroupWithZero R) M :=
  inferInstanceAs (DistribMulAction R M)
#guard_msgs in
instance instMulActionWithZero [MonoidWithZero R] [Zero M] [MulActionWithZero R M] :
    MulActionWithZero R (WrapGroupWithZero M) :=
  inferInstanceAs (MulActionWithZero R M)
#guard_msgs in
instance instMulActionWithZeroLeft [MonoidWithZero R] [Zero M] [MulActionWithZero R M] :
    MulActionWithZero (WrapGroupWithZero R) M :=
  inferInstanceAs (MulActionWithZero R M)

example [Monoid R] [MulAction R M] (r : R) (x : WrapGroupWithZero M) : r • x = .mk (r • x.unwrap) := by
  with_reducible_and_instances rfl
example [Monoid R] [MulAction R M] (r : WrapGroupWithZero R) (x : M) : r • x = r.unwrap • x := by
  with_reducible_and_instances rfl
example [AddMonoid R] [AddAction R M] (r : WrapGroupWithZero R) (x : M) : r +ᵥ x = r.unwrap +ᵥ x := by
  with_reducible_and_instances rfl
example [Monoid R] [AddMonoid M] [DistribMulAction R M] (r : WrapGroupWithZero R) (x : M) :
    r • x = r.unwrap • x := by
  with_reducible_and_instances rfl

example [Monoid R] [MulAction R M] :
    (SemigroupAction.toSMul : SMul R (WrapGroupWithZero M)) = instSMul := by
  with_reducible_and_instances rfl
example [Monoid R] [MulAction R M] :
    (SemigroupAction.toSMul : SMul (WrapGroupWithZero R) M) = instSMulLeft := by
  with_reducible_and_instances rfl
example [AddMonoid R] [AddAction R M] :
    (AddSemigroupAction.toVAdd : VAdd (WrapGroupWithZero R) M) = instVAddLeft := by
  with_reducible_and_instances rfl
example [Zero M] [SMulZeroClass R M] :
    (SMulZeroClass.toSMul : SMul (WrapGroupWithZero R) M) = instSMulLeft := by
  with_reducible_and_instances rfl
example [Zero R] [Zero M] [SMulWithZero R M] :
    (SMulWithZero.toSMulZeroClass : SMulZeroClass R (WrapGroupWithZero M)) = instSMulZeroClass := by
  with_reducible_and_instances rfl
example [Zero R] [Zero M] [SMulWithZero R M] :
    (SMulWithZero.toSMulZeroClass : SMulZeroClass (WrapGroupWithZero R) M) = instSMulZeroClassLeft := by
  with_reducible_and_instances rfl
example [AddZeroClass M] [DistribSMul R M] :
    (DistribSMul.toSMulZeroClass : SMulZeroClass R (WrapGroupWithZero M)) = instSMulZeroClass := by
  with_reducible_and_instances rfl
example [AddZeroClass M] [DistribSMul R M] :
    (DistribSMul.toSMulZeroClass : SMulZeroClass (WrapGroupWithZero R) M) = instSMulZeroClassLeft := by
  with_reducible_and_instances rfl
example [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    (DistribMulAction.toMulAction : MulAction R (WrapGroupWithZero M)) = instMulAction := by
  with_reducible_and_instances rfl
example [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    (DistribMulAction.toMulAction : MulAction (WrapGroupWithZero R) M) = instMulActionLeft := by
  with_reducible_and_instances rfl
example [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    (DistribMulAction.toDistribSMul : DistribSMul R (WrapGroupWithZero M)) = instDistribSMul := by
  with_reducible_and_instances rfl
example [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    (DistribMulAction.toDistribSMul : DistribSMul (WrapGroupWithZero R) M) = instDistribSMulLeft := by
  with_reducible_and_instances rfl
example [MonoidWithZero R] [Zero M] [MulActionWithZero R M] :
    (MulActionWithZero.toMulAction : MulAction R (WrapGroupWithZero M)) = instMulAction := by
  with_reducible_and_instances rfl
example [MonoidWithZero R] [Zero M] [MulActionWithZero R M] :
    (MulActionWithZero.toMulAction : MulAction (WrapGroupWithZero R) M) = instMulActionLeft := by
  with_reducible_and_instances rfl
example [MonoidWithZero R] [Zero M] [MulActionWithZero R M] :
    (MulActionWithZero.toSMulWithZero R (WrapGroupWithZero M)) = instSMulWithZero := by
  with_reducible_and_instances rfl
example [MonoidWithZero R] [Zero M] [MulActionWithZero R M] :
    (MulActionWithZero.toSMulWithZero (WrapGroupWithZero R) M) = instSMulWithZeroLeft := by
  with_reducible_and_instances rfl

end WrapGroupWithZero

/-!
Tests for the `@[transport]` congruences of the semiring, ring and field classes and of the casts:
each instance is transported without the warning that transport emits when it cannot unfold a
congruence, its operations reduce to the `newtype`'s constructor and projector, and diamonds
between transported instances close with `with_reducible_and_instances rfl`.
-/

newtype WrapRing (M : Type*) where
  unwrap : M

namespace WrapRing

variable {M : Type*}

instance instAdd [Add M] : Add (WrapRing M) := inferInstanceAs (Add M)
instance instMul [Mul M] : Mul (WrapRing M) := inferInstanceAs (Mul M)

#guard_msgs in
instance instNatCast [NatCast M] : NatCast (WrapRing M) := inferInstanceAs (NatCast M)
#guard_msgs in
instance instIntCast [IntCast M] : IntCast (WrapRing M) := inferInstanceAs (IntCast M)
#guard_msgs in
instance instNNRatCast [NNRatCast M] : NNRatCast (WrapRing M) := inferInstanceAs (NNRatCast M)
#guard_msgs in
instance instRatCast [RatCast M] : RatCast (WrapRing M) := inferInstanceAs (RatCast M)
#guard_msgs in
instance instDistrib [Distrib M] : Distrib (WrapRing M) := inferInstanceAs (Distrib M)
#guard_msgs in
instance [Mul M] [Add M] [LeftDistribClass M] : LeftDistribClass (WrapRing M) :=
  inferInstanceAs (LeftDistribClass M)
#guard_msgs in
instance [Mul M] [Add M] [RightDistribClass M] : RightDistribClass (WrapRing M) :=
  inferInstanceAs (RightDistribClass M)
#guard_msgs in
instance instHasDistribNeg [Mul M] [HasDistribNeg M] : HasDistribNeg (WrapRing M) :=
  inferInstanceAs (HasDistribNeg M)
#guard_msgs in
instance instAddMonoidWithOne [AddMonoidWithOne M] : AddMonoidWithOne (WrapRing M) :=
  inferInstanceAs (AddMonoidWithOne M)
#guard_msgs in
instance instAddCommMonoidWithOne [AddCommMonoidWithOne M] : AddCommMonoidWithOne (WrapRing M) :=
  inferInstanceAs (AddCommMonoidWithOne M)
#guard_msgs in
instance instAddGroupWithOne [AddGroupWithOne M] : AddGroupWithOne (WrapRing M) :=
  inferInstanceAs (AddGroupWithOne M)
#guard_msgs in
instance instAddCommGroupWithOne [AddCommGroupWithOne M] : AddCommGroupWithOne (WrapRing M) :=
  inferInstanceAs (AddCommGroupWithOne M)
#guard_msgs in
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring M] :
    NonUnitalNonAssocSemiring (WrapRing M) :=
  inferInstanceAs (NonUnitalNonAssocSemiring M)
#guard_msgs in
instance instNonUnitalSemiring [NonUnitalSemiring M] : NonUnitalSemiring (WrapRing M) :=
  inferInstanceAs (NonUnitalSemiring M)
#guard_msgs in
instance instNonAssocSemiring [NonAssocSemiring M] : NonAssocSemiring (WrapRing M) :=
  inferInstanceAs (NonAssocSemiring M)
#guard_msgs in
instance instSemiring [Semiring M] : Semiring (WrapRing M) := inferInstanceAs (Semiring M)
#guard_msgs in
instance instNonUnitalCommSemiring [NonUnitalCommSemiring M] : NonUnitalCommSemiring (WrapRing M) :=
  inferInstanceAs (NonUnitalCommSemiring M)
#guard_msgs in
instance instCommSemiring [CommSemiring M] : CommSemiring (WrapRing M) :=
  inferInstanceAs (CommSemiring M)
#guard_msgs in
instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing M] : NonUnitalNonAssocRing (WrapRing M) :=
  inferInstanceAs (NonUnitalNonAssocRing M)
#guard_msgs in
instance instNonUnitalRing [NonUnitalRing M] : NonUnitalRing (WrapRing M) :=
  inferInstanceAs (NonUnitalRing M)
#guard_msgs in
instance instNonAssocRing [NonAssocRing M] : NonAssocRing (WrapRing M) :=
  inferInstanceAs (NonAssocRing M)
#guard_msgs in
instance instRing [Ring M] : Ring (WrapRing M) := inferInstanceAs (Ring M)
#guard_msgs in
instance instNonUnitalCommRing [NonUnitalCommRing M] : NonUnitalCommRing (WrapRing M) :=
  inferInstanceAs (NonUnitalCommRing M)
#guard_msgs in
instance instCommRing [CommRing M] : CommRing (WrapRing M) := inferInstanceAs (CommRing M)
#guard_msgs in
instance [Ring M] [IsDomain M] : IsDomain (WrapRing M) := inferInstanceAs (IsDomain M)
#guard_msgs in
instance [CommRing M] [IsDomain M] : IsDomain (WrapRing M) := inferInstanceAs (IsDomain M)
#guard_msgs in
instance instDivisionSemiring [DivisionSemiring M] : DivisionSemiring (WrapRing M) :=
  inferInstanceAs (DivisionSemiring M)
#guard_msgs in
instance instDivisionRing [DivisionRing M] : DivisionRing (WrapRing M) :=
  inferInstanceAs (DivisionRing M)
#guard_msgs in
instance instSemifield [Semifield M] : Semifield (WrapRing M) := inferInstanceAs (Semifield M)
#guard_msgs in
instance instField [Field M] : Field (WrapRing M) := inferInstanceAs (Field M)

/-! Operations reduce to the constructor and projector. -/

example [NatCast M] (n : ℕ) : (n : WrapRing M) = .mk (n : M) := by
  with_reducible_and_instances rfl
example [IntCast M] (n : ℤ) : (n : WrapRing M) = .mk (n : M) := by
  with_reducible_and_instances rfl
example [RatCast M] (q : ℚ) : (q : WrapRing M) = .mk (q : M) := by
  with_reducible_and_instances rfl
example [NNRatCast M] (q : ℚ≥0) : (q : WrapRing M) = .mk (q : M) := by
  with_reducible_and_instances rfl
example [Mul M] [HasDistribNeg M] (x : WrapRing M) : -x = .mk (-x.unwrap) := by
  with_reducible_and_instances rfl
example [Ring M] (x y : WrapRing M) : x * y = .mk (x.unwrap * y.unwrap) := by
  with_reducible_and_instances rfl
example [Ring M] (x y : WrapRing M) : x - y = .mk (x.unwrap - y.unwrap) := by
  with_reducible_and_instances rfl
example [Ring M] (n : ℕ) (x : WrapRing M) : x ^ n = .mk (x.unwrap ^ n) := by
  with_reducible_and_instances rfl
example [Ring M] (n : ℤ) (x : WrapRing M) : n • x = .mk (n • x.unwrap) := by
  with_reducible_and_instances rfl
example [Ring M] (n : ℕ) : (n : WrapRing M) = .mk (n : M) := by
  with_reducible_and_instances rfl
example [Ring M] (n : ℤ) : (n : WrapRing M) = .mk (n : M) := by
  with_reducible_and_instances rfl
example [Ring M] : (1 : WrapRing M) = .mk 1 := by with_reducible_and_instances rfl
example [Field M] (x y : WrapRing M) : x / y = .mk (x.unwrap / y.unwrap) := by
  with_reducible_and_instances rfl
example [Field M] (x : WrapRing M) : x⁻¹ = .mk x.unwrap⁻¹ := by with_reducible_and_instances rfl
example [Field M] (n : ℤ) (x : WrapRing M) : x ^ n = .mk (x.unwrap ^ n) := by
  with_reducible_and_instances rfl
example [Field M] (q : ℚ) (x : WrapRing M) : q • x = .mk (q • x.unwrap) := by
  with_reducible_and_instances rfl
example [Field M] (q : ℚ≥0) (x : WrapRing M) : q • x = .mk (q • x.unwrap) := by
  with_reducible_and_instances rfl
example [Field M] (q : ℚ) : (q : WrapRing M) = .mk (q : M) := by
  with_reducible_and_instances rfl

/-! Diamonds between transported parents and children. -/

example [CommRing M] : (CommRing.toRing : Ring (WrapRing M)) = instRing := by
  with_reducible_and_instances rfl
example [CommRing M] :
    (CommRing.toNonUnitalCommRing : NonUnitalCommRing (WrapRing M)) = instNonUnitalCommRing := by
  with_reducible_and_instances rfl
example [CommRing M] :
    (CommRing.toCommSemiring : CommSemiring (WrapRing M)) = instCommSemiring := by
  with_reducible_and_instances rfl
example [Ring M] : (Ring.toSemiring : Semiring (WrapRing M)) = instSemiring := by
  with_reducible_and_instances rfl
example [Ring M] : (Ring.toNonAssocRing : NonAssocRing (WrapRing M)) = instNonAssocRing := by
  with_reducible_and_instances rfl
example [Ring M] : (Ring.toNonUnitalRing : NonUnitalRing (WrapRing M)) = instNonUnitalRing := by
  with_reducible_and_instances rfl
example [Ring M] :
    (Ring.toAddGroupWithOne : AddGroupWithOne (WrapRing M)) = instAddGroupWithOne := by
  with_reducible_and_instances rfl
example [Ring M] : (Ring.toIntCast : IntCast (WrapRing M)) = instIntCast := by
  with_reducible_and_instances rfl
example [Ring M] :
    (Ring.toNeg : Neg (WrapRing M)) = (instHasDistribNeg (M := M)).toInvolutiveNeg.toNeg := by
  with_reducible_and_instances rfl
example [NonUnitalNonAssocRing M] :
    (NonUnitalNonAssocRing.toHasDistribNeg : HasDistribNeg (WrapRing M)) = instHasDistribNeg := by
  with_reducible_and_instances rfl
example [Ring M] : (instRing (M := M)).toMul = instMul := by
  with_reducible_and_instances rfl
example [Ring M] : (instRing (M := M)).toAdd = instAdd := by
  with_reducible_and_instances rfl
example [NonAssocRing M] :
    (NonAssocRing.toAddCommGroupWithOne : AddCommGroupWithOne (WrapRing M)) =
      instAddCommGroupWithOne := by
  with_reducible_and_instances rfl
example [NonAssocRing M] :
    (NonAssocRing.toNonUnitalNonAssocRing : NonUnitalNonAssocRing (WrapRing M)) =
      instNonUnitalNonAssocRing := by
  with_reducible_and_instances rfl
example [NonUnitalRing M] :
    (NonUnitalRing.toNonUnitalSemiring : NonUnitalSemiring (WrapRing M)) =
      instNonUnitalSemiring := by
  with_reducible_and_instances rfl
example [NonUnitalNonAssocRing M] :
    (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (WrapRing M)) =
      instNonUnitalNonAssocSemiring := by
  with_reducible_and_instances rfl
example [CommSemiring M] : (CommSemiring.toSemiring : Semiring (WrapRing M)) = instSemiring := by
  with_reducible_and_instances rfl
example [NonUnitalCommSemiring M] :
    (NonUnitalCommSemiring.toNonUnitalSemiring : NonUnitalSemiring (WrapRing M)) =
      instNonUnitalSemiring := by
  with_reducible_and_instances rfl
example [Semiring M] : (Semiring.toNonAssocSemiring : NonAssocSemiring (WrapRing M)) =
    instNonAssocSemiring := by
  with_reducible_and_instances rfl
example [Semiring M] : (Semiring.toNonUnitalSemiring : NonUnitalSemiring (WrapRing M)) =
    instNonUnitalSemiring := by
  with_reducible_and_instances rfl
example [NonAssocSemiring M] :
    (NonAssocSemiring.toAddCommMonoidWithOne : AddCommMonoidWithOne (WrapRing M)) =
      instAddCommMonoidWithOne := by
  with_reducible_and_instances rfl
example [NonAssocSemiring M] :
    (NonAssocSemiring.toNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (WrapRing M)) =
      instNonUnitalNonAssocSemiring := by
  with_reducible_and_instances rfl
example [NonUnitalNonAssocSemiring M] :
    (NonUnitalNonAssocSemiring.toDistrib : Distrib (WrapRing M)) = instDistrib := by
  with_reducible_and_instances rfl
example [AddCommGroupWithOne M] :
    (AddCommGroupWithOne.toAddGroupWithOne : AddGroupWithOne (WrapRing M)) =
      instAddGroupWithOne := by
  with_reducible_and_instances rfl
example [AddCommGroupWithOne M] :
    (AddCommGroupWithOne.toAddCommMonoidWithOne : AddCommMonoidWithOne (WrapRing M)) =
      instAddCommMonoidWithOne := by
  with_reducible_and_instances rfl
example [AddGroupWithOne M] :
    (AddGroupWithOne.toAddMonoidWithOne : AddMonoidWithOne (WrapRing M)) =
      instAddMonoidWithOne := by
  with_reducible_and_instances rfl
example [AddCommMonoidWithOne M] :
    (AddCommMonoidWithOne.toAddMonoidWithOne : AddMonoidWithOne (WrapRing M)) =
      instAddMonoidWithOne := by
  with_reducible_and_instances rfl
example [AddMonoidWithOne M] :
    (AddMonoidWithOne.toNatCast : NatCast (WrapRing M)) = instNatCast := by
  with_reducible_and_instances rfl
example [Field M] : (Field.toSemifield : Semifield (WrapRing M)) = instSemifield := by
  with_reducible_and_instances rfl
example [Field M] : (Field.toDivisionRing : DivisionRing (WrapRing M)) = instDivisionRing := by
  with_reducible_and_instances rfl
example [Field M] : (Field.toCommRing : CommRing (WrapRing M)) = instCommRing := by
  with_reducible_and_instances rfl
example [Field M] : (Field.toRatCast : RatCast (WrapRing M)) = instRatCast := by
  with_reducible_and_instances rfl
example [DivisionRing M] :
    (DivisionRing.toDivisionSemiring : DivisionSemiring (WrapRing M)) = instDivisionSemiring := by
  with_reducible_and_instances rfl
example [DivisionRing M] : (DivisionRing.toRing : Ring (WrapRing M)) = instRing := by
  with_reducible_and_instances rfl
example [Semifield M] :
    (Semifield.toDivisionSemiring : DivisionSemiring (WrapRing M)) = instDivisionSemiring := by
  with_reducible_and_instances rfl
example [Semifield M] :
    (Semifield.toCommSemiring : CommSemiring (WrapRing M)) = instCommSemiring := by
  with_reducible_and_instances rfl
example [DivisionSemiring M] :
    (DivisionSemiring.toSemiring : Semiring (WrapRing M)) = instSemiring := by
  with_reducible_and_instances rfl
example [DivisionSemiring M] :
    (DivisionSemiring.toNNRatCast : NNRatCast (WrapRing M)) = instNNRatCast := by
  with_reducible_and_instances rfl

/-! Diamonds with the transported group structures. -/

#guard_msgs in
instance instAddCommGroup [AddCommGroup M] : AddCommGroup (WrapRing M) :=
  inferInstanceAs (AddCommGroup M)
#guard_msgs in
instance instCommMonoid [CommMonoid M] : CommMonoid (WrapRing M) := inferInstanceAs (CommMonoid M)
#guard_msgs in
instance instDivInvMonoid [DivInvMonoid M] : DivInvMonoid (WrapRing M) :=
  inferInstanceAs (DivInvMonoid M)

example [Ring M] : (Ring.toAddCommGroup : AddCommGroup (WrapRing M)) = instAddCommGroup := by
  with_reducible_and_instances rfl
example [CommRing M] : (CommRing.toCommMonoid : CommMonoid (WrapRing M)) = instCommMonoid := by
  with_reducible_and_instances rfl
example [CommSemiring M] :
    (CommSemiring.toCommMonoid : CommMonoid (WrapRing M)) = instCommMonoid := by
  with_reducible_and_instances rfl
example [Field M] :
    (DivisionRing.toDivInvMonoid : DivInvMonoid (WrapRing M)) = instDivInvMonoid := by
  with_reducible_and_instances rfl

#guard_msgs in
instance instMonoidWithZero [MonoidWithZero M] : MonoidWithZero (WrapRing M) :=
  inferInstanceAs (MonoidWithZero M)

example [Semiring M] : (Semiring.toMonoidWithZero : MonoidWithZero (WrapRing M)) =
    instMonoidWithZero := by
  with_reducible_and_instances rfl

end WrapRing

/-! The order dual's instances are transported. -/

example {R : Type*} [CommRing R] :
    (CommRing.toRing : Ring Rᵒᵈ) = OrderDual.instRing := by
  with_reducible_and_instances rfl
example {K : Type*} [Field K] :
    (Field.toDivisionRing : DivisionRing Kᵒᵈ) = OrderDual.instDivisionRing := by
  with_reducible_and_instances rfl
example {K : Type*} [Field K] (x y : Kᵒᵈ) : x / y = OrderDual.toDual' (x.ofDual' / y.ofDual') := by
  with_reducible_and_instances rfl

/-!
Tests for the `@[transport]` congruences of bornologies, uniform spaces, (extended) metric spaces
and normed groups: each instance is transported without the warning that transport emits when it
cannot unfold a congruence, its data reduces to the `newtype`'s constructor and projector, and
diamonds between transported instances close with `with_reducible_and_instances rfl`.
-/

newtype WrapMetric (M : Type*) where
  unwrap : M

namespace WrapMetric

variable {M : Type*}

#guard_msgs in
instance instBornology [Bornology M] : Bornology (WrapMetric M) := inferInstanceAs (Bornology M)
#guard_msgs in
instance [Bornology M] [BoundedSpace M] : BoundedSpace (WrapMetric M) :=
  inferInstanceAs (BoundedSpace M)
#guard_msgs in
instance instTopologicalSpace [TopologicalSpace M] : TopologicalSpace (WrapMetric M) :=
  inferInstanceAs (TopologicalSpace M)
#guard_msgs in
instance instUniformSpace [UniformSpace M] : UniformSpace (WrapMetric M) :=
  inferInstanceAs (UniformSpace M)
#guard_msgs in
instance instEDist [EDist M] : EDist (WrapMetric M) := inferInstanceAs (EDist M)
#guard_msgs in
instance instWeakPseudoEMetricSpace [TopologicalSpace M] [WeakPseudoEMetricSpace M] :
    WeakPseudoEMetricSpace (WrapMetric M) :=
  inferInstanceAs (WeakPseudoEMetricSpace M)
#guard_msgs in
instance instWeakEMetricSpace [TopologicalSpace M] [WeakEMetricSpace M] :
    WeakEMetricSpace (WrapMetric M) :=
  inferInstanceAs (WeakEMetricSpace M)
#guard_msgs in
instance instPseudoEMetricSpace [PseudoEMetricSpace M] : PseudoEMetricSpace (WrapMetric M) :=
  inferInstanceAs (PseudoEMetricSpace M)
#guard_msgs in
instance instEMetricSpace [EMetricSpace M] : EMetricSpace (WrapMetric M) :=
  inferInstanceAs (EMetricSpace M)
#guard_msgs in
instance instDist [Dist M] : Dist (WrapMetric M) := inferInstanceAs (Dist M)
#guard_msgs in
instance instPseudoMetricSpace [PseudoMetricSpace M] : PseudoMetricSpace (WrapMetric M) :=
  inferInstanceAs (PseudoMetricSpace M)
#guard_msgs in
instance instMetricSpace [MetricSpace M] : MetricSpace (WrapMetric M) :=
  inferInstanceAs (MetricSpace M)
#guard_msgs in
instance [PseudoMetricSpace M] [ProperSpace M] : ProperSpace (WrapMetric M) :=
  inferInstanceAs (ProperSpace M)
#guard_msgs in
instance instMonoid [Monoid M] : Monoid (WrapMetric M) := inferInstanceAs (Monoid M)
#guard_msgs in
instance instAddMonoid [AddMonoid M] : AddMonoid (WrapMetric M) := inferInstanceAs (AddMonoid M)
#guard_msgs in
instance [PseudoMetricSpace M] [Monoid M] [LipschitzMul M] : LipschitzMul (WrapMetric M) :=
  inferInstanceAs (LipschitzMul M)
#guard_msgs in
instance [PseudoMetricSpace M] [AddMonoid M] [LipschitzAdd M] : LipschitzAdd (WrapMetric M) :=
  inferInstanceAs (LipschitzAdd M)
#guard_msgs in
instance instNorm [Norm M] : Norm (WrapMetric M) := inferInstanceAs (Norm M)
#guard_msgs in
instance instNNNorm [NNNorm M] : NNNorm (WrapMetric M) := inferInstanceAs (NNNorm M)
#guard_msgs in
instance instGroup [Group M] : Group (WrapMetric M) := inferInstanceAs (Group M)
#guard_msgs in
instance instAddGroup [AddGroup M] : AddGroup (WrapMetric M) := inferInstanceAs (AddGroup M)
#guard_msgs in
instance instSeminormedGroup [SeminormedGroup M] : SeminormedGroup (WrapMetric M) :=
  inferInstanceAs (SeminormedGroup M)
#guard_msgs in
instance instSeminormedAddGroup [SeminormedAddGroup M] : SeminormedAddGroup (WrapMetric M) :=
  inferInstanceAs (SeminormedAddGroup M)
#guard_msgs in
instance instSeminormedCommGroup [SeminormedCommGroup M] : SeminormedCommGroup (WrapMetric M) :=
  inferInstanceAs (SeminormedCommGroup M)
#guard_msgs in
instance instSeminormedAddCommGroup [SeminormedAddCommGroup M] :
    SeminormedAddCommGroup (WrapMetric M) :=
  inferInstanceAs (SeminormedAddCommGroup M)
#guard_msgs in
instance instNormedGroup [NormedGroup M] : NormedGroup (WrapMetric M) :=
  inferInstanceAs (NormedGroup M)
#guard_msgs in
instance instNormedAddGroup [NormedAddGroup M] : NormedAddGroup (WrapMetric M) :=
  inferInstanceAs (NormedAddGroup M)
#guard_msgs in
instance instNormedCommGroup [NormedCommGroup M] : NormedCommGroup (WrapMetric M) :=
  inferInstanceAs (NormedCommGroup M)
#guard_msgs in
instance instNormedAddCommGroup [NormedAddCommGroup M] : NormedAddCommGroup (WrapMetric M) :=
  inferInstanceAs (NormedAddCommGroup M)

/-! The data reduces to the underlying data. -/

example [Bornology M] : Bornology.cobounded (WrapMetric M) = (Bornology.cobounded M).map .mk := by
  with_reducible_and_instances rfl
example [UniformSpace M] :
    UniformSpace.uniformity (α := WrapMetric M) =
      (UniformSpace.uniformity (α := M)).map (Prod.map .mk .mk) := by
  with_reducible_and_instances rfl
example [EDist M] (x y : WrapMetric M) : edist x y = edist x.unwrap y.unwrap := by
  with_reducible_and_instances rfl
example [PseudoEMetricSpace M] (x y : WrapMetric M) : edist x y = edist x.unwrap y.unwrap := by
  with_reducible_and_instances rfl
example [Dist M] (x y : WrapMetric M) : dist x y = dist x.unwrap y.unwrap := by
  with_reducible_and_instances rfl
example [PseudoMetricSpace M] (x y : WrapMetric M) : dist x y = dist x.unwrap y.unwrap := by
  with_reducible_and_instances rfl
example [PseudoMetricSpace M] (x y : WrapMetric M) : edist x y = edist x.unwrap y.unwrap := by
  with_reducible_and_instances rfl
example [Norm M] (x : WrapMetric M) : ‖x‖ = ‖x.unwrap‖ := by with_reducible_and_instances rfl
example [NNNorm M] (x : WrapMetric M) : ‖x‖₊ = ‖x.unwrap‖₊ := by with_reducible_and_instances rfl
example [SeminormedAddCommGroup M] (x : WrapMetric M) : ‖x‖ = ‖x.unwrap‖ := by
  with_reducible_and_instances rfl

/-! Diamonds between separately transported instances. -/

example [UniformSpace M] :
    (UniformSpace.toTopologicalSpace : TopologicalSpace (WrapMetric M)) = instTopologicalSpace := by
  with_reducible_and_instances rfl
example [PseudoEMetricSpace M] :
    (PseudoEMetricSpace.toUniformSpace : UniformSpace (WrapMetric M)) = instUniformSpace := by
  with_reducible_and_instances rfl
example [PseudoEMetricSpace M] :
    (PseudoEMetricSpace.toEDist : EDist (WrapMetric M)) = instEDist := by
  with_reducible_and_instances rfl
example [PseudoEMetricSpace M] :
    PseudoEMetricSpace.toWeakPseudoEMetricSpace (WrapMetric M) = instWeakPseudoEMetricSpace := by
  with_reducible_and_instances rfl
example [EMetricSpace M] :
    (EMetricSpace.toPseudoEMetricSpace : PseudoEMetricSpace (WrapMetric M)) =
      instPseudoEMetricSpace := by
  with_reducible_and_instances rfl
example [EMetricSpace M] :
    EMetricSpace.toWeakEMetricSpace (WrapMetric M) = instWeakEMetricSpace := by
  with_reducible_and_instances rfl
example [TopologicalSpace M] [WeakEMetricSpace M] :
    (WeakEMetricSpace.toWeakPseudoEMetricSpace : WeakPseudoEMetricSpace (WrapMetric M)) =
      instWeakPseudoEMetricSpace := by
  with_reducible_and_instances rfl
example [PseudoMetricSpace M] :
    (PseudoMetricSpace.toUniformSpace : UniformSpace (WrapMetric M)) = instUniformSpace := by
  with_reducible_and_instances rfl
example [PseudoMetricSpace M] :
    (PseudoMetricSpace.toBornology : Bornology (WrapMetric M)) = instBornology := by
  with_reducible_and_instances rfl
example [PseudoMetricSpace M] : (PseudoMetricSpace.toDist : Dist (WrapMetric M)) = instDist := by
  with_reducible_and_instances rfl
example [PseudoMetricSpace M] :
    (PseudoMetricSpace.toPseudoEMetricSpace : PseudoEMetricSpace (WrapMetric M)) =
      instPseudoEMetricSpace := by
  with_reducible_and_instances rfl
example [MetricSpace M] :
    (MetricSpace.toPseudoMetricSpace : PseudoMetricSpace (WrapMetric M)) =
      instPseudoMetricSpace := by
  with_reducible_and_instances rfl
example [MetricSpace M] :
    (MetricSpace.toEMetricSpace : EMetricSpace (WrapMetric M)) = instEMetricSpace := by
  with_reducible_and_instances rfl
example [SeminormedGroup M] : (SeminormedGroup.toNorm : Norm (WrapMetric M)) = instNorm := by
  with_reducible_and_instances rfl
example [SeminormedAddGroup M] :
    (SeminormedAddGroup.toNNNorm : NNNorm (WrapMetric M)) = instNNNorm := by
  with_reducible_and_instances rfl
example [SeminormedGroup M] : (SeminormedGroup.toGroup : Group (WrapMetric M)) = instGroup := by
  with_reducible_and_instances rfl
example [SeminormedGroup M] :
    (SeminormedGroup.toPseudoMetricSpace : PseudoMetricSpace (WrapMetric M)) =
      instPseudoMetricSpace := by
  with_reducible_and_instances rfl
example [SeminormedAddGroup M] :
    (SeminormedAddGroup.toAddGroup : AddGroup (WrapMetric M)) = instAddGroup := by
  with_reducible_and_instances rfl
example [SeminormedCommGroup M] :
    (SeminormedCommGroup.toSeminormedGroup : SeminormedGroup (WrapMetric M)) =
      instSeminormedGroup := by
  with_reducible_and_instances rfl
example [NormedGroup M] :
    (NormedGroup.toSeminormedGroup : SeminormedGroup (WrapMetric M)) = instSeminormedGroup := by
  with_reducible_and_instances rfl
example [NormedGroup M] :
    (NormedGroup.toMetricSpace : MetricSpace (WrapMetric M)) = instMetricSpace := by
  with_reducible_and_instances rfl
example [NormedCommGroup M] :
    (NormedCommGroup.toNormedGroup : NormedGroup (WrapMetric M)) = instNormedGroup := by
  with_reducible_and_instances rfl
example [NormedCommGroup M] :
    (NormedCommGroup.toSeminormedCommGroup : SeminormedCommGroup (WrapMetric M)) =
      instSeminormedCommGroup := by
  with_reducible_and_instances rfl
example [NormedAddCommGroup M] :
    (NormedAddCommGroup.toSeminormedAddCommGroup : SeminormedAddCommGroup (WrapMetric M)) =
      instSeminormedAddCommGroup := by
  with_reducible_and_instances rfl
example [SeminormedAddCommGroup M] :
    (SeminormedAddCommGroup.toSeminormedAddGroup : SeminormedAddGroup (WrapMetric M)) =
      instSeminormedAddGroup := by
  with_reducible_and_instances rfl
example [NormedAddGroup M] :
    (NormedAddGroup.toSeminormedAddGroup : SeminormedAddGroup (WrapMetric M)) =
      instSeminormedAddGroup := by
  with_reducible_and_instances rfl

end WrapMetric

/-! The `OrderDual` instances agree with each other. -/

section OrderDual

variable {α : Type*}

example [UniformSpace α] :
    (UniformSpace.toTopologicalSpace : TopologicalSpace αᵒᵈ) = OrderDual.instTopologicalSpace := by
  with_reducible_and_instances rfl
example [PseudoMetricSpace α] :
    (PseudoMetricSpace.toUniformSpace : UniformSpace αᵒᵈ) = OrderDual.instUniformSpace := by
  with_reducible_and_instances rfl
example [PseudoMetricSpace α] :
    (PseudoMetricSpace.toBornology : Bornology αᵒᵈ) = OrderDual.instBornology := by
  with_reducible_and_instances rfl
example [SeminormedAddCommGroup α] :
    (SeminormedAddCommGroup.toNorm : Norm αᵒᵈ) = OrderDual.toNorm := by
  with_reducible_and_instances rfl
example [SeminormedAddGroup α] :
    (SeminormedAddGroup.toNNNorm : NNNorm αᵒᵈ) = OrderDual.toNNNorm := by
  with_reducible_and_instances rfl
example [PseudoMetricSpace α] :
    (PseudoMetricSpace.toPseudoEMetricSpace : PseudoEMetricSpace αᵒᵈ) =
      instPseudoEMetricSpaceOrderDual := by
  with_reducible_and_instances rfl
example [MetricSpace α] :
    (MetricSpace.toPseudoMetricSpace : PseudoMetricSpace αᵒᵈ) = instPseudoMetricSpaceOrderDual := by
  with_reducible_and_instances rfl
example [SeminormedGroup α] :
    (SeminormedGroup.toPseudoMetricSpace : PseudoMetricSpace αᵒᵈ) =
      instPseudoMetricSpaceOrderDual := by
  with_reducible_and_instances rfl
example [NormedAddCommGroup α] :
    (NormedAddCommGroup.toSeminormedAddCommGroup : SeminormedAddCommGroup αᵒᵈ) =
      OrderDual.seminormedAddCommGroup := by
  with_reducible_and_instances rfl
example [Norm α] (x : α) : ‖OrderDual.toDual x‖ = ‖x‖ := rfl
example [NNNorm α] (x : α) : ‖OrderDual.toDual x‖₊ = ‖x‖₊ := rfl

end OrderDual

/-!
Tests for the `@[transport]` congruences of the topological mixins, `MeasurableSpace`, `Fintype`,
`Finite` and `Small`: each instance is transported without the unfolding warning, data reduces to
the `newtype`'s constructor and projector, and the mixins apply to transported parents.
-/

newtype WrapMisc (M : Type*) where
  unwrap : M

namespace WrapMisc

variable {R M : Type*}

#guard_msgs in
instance instTopologicalSpace [TopologicalSpace M] : TopologicalSpace (WrapMisc M) :=
  inferInstanceAs (TopologicalSpace M)
#guard_msgs in
instance instMul [Mul M] : Mul (WrapMisc M) := inferInstanceAs (Mul M)
#guard_msgs in
instance instAdd [Add M] : Add (WrapMisc M) := inferInstanceAs (Add M)
#guard_msgs in
instance instInv [Inv M] : Inv (WrapMisc M) := inferInstanceAs (Inv M)
#guard_msgs in
instance instNeg [Neg M] : Neg (WrapMisc M) := inferInstanceAs (Neg M)
#guard_msgs in
instance instSMul [SMul R M] : SMul R (WrapMisc M) := inferInstanceAs (SMul R M)

#guard_msgs in
instance [TopologicalSpace M] [DiscreteTopology M] : DiscreteTopology (WrapMisc M) :=
  inferInstanceAs (DiscreteTopology M)
#guard_msgs in
instance [TopologicalSpace M] [FirstCountableTopology M] : FirstCountableTopology (WrapMisc M) :=
  inferInstanceAs (FirstCountableTopology M)
#guard_msgs in
instance [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology (WrapMisc M) :=
  inferInstanceAs (SecondCountableTopology M)
#guard_msgs in
instance [TopologicalSpace M] [TopologicalSpace.SeparableSpace M] :
    TopologicalSpace.SeparableSpace (WrapMisc M) :=
  inferInstanceAs (TopologicalSpace.SeparableSpace M)
#guard_msgs in
instance [TopologicalSpace M] [Mul M] [ContinuousMul M] : ContinuousMul (WrapMisc M) :=
  inferInstanceAs (ContinuousMul M)
#guard_msgs in
instance [TopologicalSpace M] [Add M] [ContinuousAdd M] : ContinuousAdd (WrapMisc M) :=
  inferInstanceAs (ContinuousAdd M)
#guard_msgs in
instance [TopologicalSpace M] [Mul M] [SeparatelyContinuousMul M] :
    SeparatelyContinuousMul (WrapMisc M) :=
  inferInstanceAs (SeparatelyContinuousMul M)
#guard_msgs in
instance [TopologicalSpace M] [Add M] [SeparatelyContinuousAdd M] :
    SeparatelyContinuousAdd (WrapMisc M) :=
  inferInstanceAs (SeparatelyContinuousAdd M)
#guard_msgs in
instance [TopologicalSpace M] [Inv M] [ContinuousInv M] : ContinuousInv (WrapMisc M) :=
  inferInstanceAs (ContinuousInv M)
#guard_msgs in
instance [TopologicalSpace M] [Neg M] [ContinuousNeg M] : ContinuousNeg (WrapMisc M) :=
  inferInstanceAs (ContinuousNeg M)
#guard_msgs in
instance [TopologicalSpace M] [SMul R M] [ContinuousConstSMul R M] :
    ContinuousConstSMul R (WrapMisc M) :=
  inferInstanceAs (ContinuousConstSMul R M)

#guard_msgs in
instance instMeasurableSpace [MeasurableSpace M] : MeasurableSpace (WrapMisc M) :=
  inferInstanceAs (MeasurableSpace M)
#guard_msgs in
instance instFintype [Fintype M] : Fintype (WrapMisc M) := inferInstanceAs (Fintype M)
#guard_msgs in
instance [Finite M] : Finite (WrapMisc M) := inferInstanceAs (Finite M)
#guard_msgs in
instance [Small.{0} M] : Small.{0} (WrapMisc M) := inferInstanceAs (Small.{0} M)

example [MeasurableSpace M] (s : Set (WrapMisc M)) :
    MeasurableSet s ↔ MeasurableSet (WrapMisc.mk ⁻¹' s) := by
  unfold MeasurableSet
  with_reducible_and_instances rfl
example [Fintype M] :
    (Fintype.elems : Finset (WrapMisc M)).val = (Fintype.elems : Finset M).val.map WrapMisc.mk := by
  with_reducible_and_instances rfl
example [TopologicalSpace M] (s : Set (WrapMisc M)) :
    TopologicalSpace.IsOpen s ↔ TopologicalSpace.IsOpen (WrapMisc.mk ⁻¹' s) := by
  with_reducible_and_instances rfl

end WrapMisc

/-! Transport along the scalars of an action. -/

newtype WrapScalar (R : Type*) where
  unwrap : R

namespace WrapScalar

variable {R α : Type*}

#guard_msgs in
instance instSMul [SMul R α] : SMul (WrapScalar R) α := inferInstanceAs (SMul R α)
#guard_msgs in
instance instVAdd [VAdd R α] : VAdd (WrapScalar R) α := inferInstanceAs (VAdd R α)
#guard_msgs in
instance [TopologicalSpace α] [SMul R α] [ContinuousConstSMul R α] :
    ContinuousConstSMul (WrapScalar R) α :=
  inferInstanceAs (ContinuousConstSMul R α)
#guard_msgs in
instance [TopologicalSpace α] [VAdd R α] [ContinuousConstVAdd R α] :
    ContinuousConstVAdd (WrapScalar R) α :=
  inferInstanceAs (ContinuousConstVAdd R α)

example [SMul R α] (r : WrapScalar R) (x : α) : r • x = r.unwrap • x := by
  with_reducible_and_instances rfl

end WrapScalar

/-! The `OrderDual` instances. -/

example {α : Type*} [TopologicalSpace α] (s : Set αᵒᵈ) :
    TopologicalSpace.IsOpen s ↔ TopologicalSpace.IsOpen (OrderDual.toDual' ⁻¹' s) := by
  with_reducible_and_instances rfl
example {α : Type*} [MeasurableSpace α] (s : Set αᵒᵈ) :
    MeasurableSet s ↔ MeasurableSet (OrderDual.toDual' ⁻¹' s) := by
  unfold MeasurableSet
  with_reducible_and_instances rfl
example {α : Type*} [Fintype α] :
    (Fintype.elems : Finset αᵒᵈ).val = (Fintype.elems : Finset α).val.map OrderDual.toDual' := by
  with_reducible_and_instances rfl

/-!
Congruences take an equivalence for every type argument, so they transport in several positions at
once, including through the opposite of the scalars for `IsCentralScalar`.
-/

newtype WrapBoth (M : Type*) where
  unwrap : M

namespace WrapBoth

variable {R S M : Type*}

#guard_msgs in
instance instSMul [SMul R M] : SMul (WrapBoth R) (WrapBoth M) := inferInstanceAs (SMul R M)
#guard_msgs in
instance instVAdd [VAdd R M] : VAdd (WrapBoth R) (WrapBoth M) := inferInstanceAs (VAdd R M)
#guard_msgs in
instance instSMulOp [SMul Rᵐᵒᵖ M] : SMul (WrapBoth R)ᵐᵒᵖ (WrapBoth M) :=
  inferInstanceAs (SMul Rᵐᵒᵖ M)
#guard_msgs in
instance [Pow M R] : Pow (WrapBoth M) (WrapBoth R) := inferInstanceAs (Pow M R)
#guard_msgs in
instance instMonoid [Monoid R] : Monoid (WrapBoth R) := inferInstanceAs (Monoid R)
#guard_msgs in
instance instMonoidWithZero [MonoidWithZero R] : MonoidWithZero (WrapBoth R) :=
  inferInstanceAs (MonoidWithZero R)
#guard_msgs in
instance instSemiring [Semiring R] : Semiring (WrapBoth R) := inferInstanceAs (Semiring R)
#guard_msgs in
instance instZero [Zero M] : Zero (WrapBoth M) := inferInstanceAs (Zero M)
#guard_msgs in
instance instAddMonoid [AddMonoid M] : AddMonoid (WrapBoth M) := inferInstanceAs (AddMonoid M)
#guard_msgs in
instance instAddCommMonoid [AddCommMonoid M] : AddCommMonoid (WrapBoth M) :=
  inferInstanceAs (AddCommMonoid M)
#guard_msgs in
instance instTopologicalSpace [TopologicalSpace M] : TopologicalSpace (WrapBoth M) :=
  inferInstanceAs (TopologicalSpace M)

#guard_msgs in
instance instMulAction [Monoid R] [MulAction R M] : MulAction (WrapBoth R) (WrapBoth M) :=
  inferInstanceAs (MulAction R M)
#guard_msgs in
instance [SMul R M] [SMul S M] [SMulCommClass R S M] :
    SMulCommClass (WrapBoth R) (WrapBoth S) (WrapBoth M) :=
  inferInstanceAs (SMulCommClass R S M)
#guard_msgs in
instance [SMul R S] [SMul S M] [SMul R M] [IsScalarTower R S M] :
    IsScalarTower (WrapBoth R) (WrapBoth S) (WrapBoth M) :=
  inferInstanceAs (IsScalarTower R S M)
#guard_msgs in
instance [SMul R M] [SMul Rᵐᵒᵖ M] [IsCentralScalar R M] :
    IsCentralScalar (WrapBoth R) (WrapBoth M) :=
  inferInstanceAs (IsCentralScalar R M)
#guard_msgs in
instance [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero (WrapBoth R) (WrapBoth M) :=
  inferInstanceAs (SMulWithZero R M)
#guard_msgs in
instance [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    DistribMulAction (WrapBoth R) (WrapBoth M) :=
  inferInstanceAs (DistribMulAction R M)
#guard_msgs in
instance [MonoidWithZero R] [Zero M] [MulActionWithZero R M] :
    MulActionWithZero (WrapBoth R) (WrapBoth M) :=
  inferInstanceAs (MulActionWithZero R M)
#guard_msgs in
instance instModule [Semiring R] [AddCommMonoid M] [Module R M] :
    Module (WrapBoth R) (WrapBoth M) :=
  inferInstanceAs (Module R M)
#guard_msgs in
instance [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M] :
    Module.Free (WrapBoth R) (WrapBoth M) :=
  inferInstanceAs (Module.Free R M)
#guard_msgs in
instance [Semiring R] [AddCommMonoid M] [Module R M] [Module.Finite R M] :
    Module.Finite (WrapBoth R) (WrapBoth M) :=
  inferInstanceAs (Module.Finite R M)
#guard_msgs in
instance [TopologicalSpace R] [TopologicalSpace M] [SMul R M] [ContinuousSMul R M] :
    ContinuousSMul (WrapBoth R) (WrapBoth M) :=
  inferInstanceAs (ContinuousSMul R M)
#guard_msgs in
instance [TopologicalSpace M] [SMul R M] [ContinuousConstSMul R M] :
    ContinuousConstSMul (WrapBoth R) (WrapBoth M) :=
  inferInstanceAs (ContinuousConstSMul R M)

example [SMul R M] (r : WrapBoth R) (x : WrapBoth M) : r • x = .mk (r.unwrap • x.unwrap) := by
  with_reducible_and_instances rfl
example [Pow M R] (x : WrapBoth M) (r : WrapBoth R) : x ^ r = .mk (x.unwrap ^ r.unwrap) := by
  with_reducible_and_instances rfl
example [Semiring R] [AddCommMonoid M] [Module R M] :
    (Module.toDistribMulAction.toMulAction.toSMul : SMul (WrapBoth R) (WrapBoth M)) = instSMul := by
  with_reducible_and_instances rfl
example [Semiring R] [AddCommMonoid M] [Module R M] :
    (Module.toDistribMulAction.toMulAction : MulAction (WrapBoth R) (WrapBoth M)) = instMulAction :=
  by with_reducible_and_instances rfl

end WrapBoth

/-! Order duals in both positions. -/

example {α β : Type*} [Semiring α] [AddCommMonoid β] [Module α β] : Module αᵒᵈ βᵒᵈ :=
  inferInstanceAs (Module α β)
example {α β : Type*} [Monoid α] [MulAction α β] : MulAction αᵒᵈ βᵒᵈ :=
  inferInstanceAs (MulAction α β)
example {α β : Type*} [SMul α β] (a : αᵒᵈ) (b : βᵒᵈ) :
    letI : SMul αᵒᵈ βᵒᵈ := inferInstanceAs (SMul α β)
    a • b = OrderDual.toDual' (a.ofDual' • b.ofDual') := by
  with_reducible_and_instances rfl
