import Mathlib.Topology.Algebra.UniformConvergence

/-!
Tests for the `newtype`-sealed `UniformFun`: `α →ᵤ β` is a type of its own, distinct from `α → β`
and from `α →ᵤ[𝔖] β`; its transported instances reduce to the constructor and projector; and the
algebraic diamonds close with `with_reducible_and_instances rfl`.
-/

open UniformConvergence UniformFun

variable {α β R : Type*} {𝔖 : Set (Set α)}

/-! Crossing the seal needs the equivalences. -/

example (f : α → β) : α →ᵤ β := by
  fail_if_success exact f
  exact ofFun f
example (f : α →ᵤ β) : α → β := by
  fail_if_success exact f
  exact toFun f
example (f : α →ᵤ[𝔖] β) : α →ᵤ β := by
  fail_if_success exact f
  exact ofFun (UniformOnFun.toFun 𝔖 f)

example (f : α → β) : toFun (ofFun f) = f := rfl
example (f : α →ᵤ β) : ofFun (toFun f) = f := rfl

section Group

variable [Group β]

example (f g : α →ᵤ β) : f * g = ofFun' (f.toFun' * g.toFun') := by
  with_reducible_and_instances rfl
example : (1 : α →ᵤ β) = ofFun' 1 := by with_reducible_and_instances rfl
example (f : α →ᵤ β) : f⁻¹ = ofFun' f.toFun'⁻¹ := by with_reducible_and_instances rfl
example (f g : α →ᵤ β) : f / g = ofFun' (f.toFun' / g.toFun') := by
  with_reducible_and_instances rfl
example (n : ℕ) (f : α →ᵤ β) : f ^ n = ofFun' (f.toFun' ^ n) := by
  with_reducible_and_instances rfl

example : (Group.toDivInvMonoid.toMonoid : Monoid (α →ᵤ β)) = instMonoidUniformFun := by
  with_reducible_and_instances rfl
example : (Monoid.toMulOneClass.toMul : Mul (α →ᵤ β)) = instMulUniformFun := by
  with_reducible_and_instances rfl

end Group

example [CommGroup β] : (CommGroup.toGroup : Group (α →ᵤ β)) = instGroupUniformFun := by
  with_reducible_and_instances rfl

section Module

variable [Semiring R] [AddCommMonoid β] [Module R β]

example (r : R) (f : α →ᵤ β) : r • f = ofFun' (r • f.toFun') := by
  with_reducible_and_instances rfl
example : (Module.toDistribMulAction : DistribMulAction R (α →ᵤ β)) =
    instDistribMulActionUniformFun := by
  with_reducible_and_instances rfl

end Module

example [AddCommGroup β] :
    (AddCommGroup.toIntModule _ : Module ℤ (α →ᵤ β)) = instModuleUniformFun := by
  with_reducible_and_instances rfl
