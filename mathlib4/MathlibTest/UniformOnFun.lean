import Mathlib.Topology.Algebra.UniformConvergence

/-!
Tests for the `newtype`-sealed `UniformOnFun`: `α →ᵤ[𝔖] β` is a type of its own, distinct from
`α → β` and from `α →ᵤ[𝔗] β`; its transported instances reduce to the constructor and projector;
and the algebraic diamonds close with `with_reducible_and_instances rfl`.
-/

open UniformConvergence UniformOnFun

variable {α β R : Type*} {𝔖 𝔗 : Set (Set α)}

/-! Crossing the seal needs the equivalences. -/

example (f : α → β) : α →ᵤ[𝔖] β := by
  fail_if_success exact f
  exact ofFun 𝔖 f
example (f : α →ᵤ[𝔗] β) : α →ᵤ[𝔖] β := by
  fail_if_success exact f
  exact ofFun 𝔖 (toFun 𝔗 f)

example (f : α → β) : toFun 𝔖 (ofFun 𝔖 f) = f := rfl
example (f : α →ᵤ[𝔖] β) : ofFun 𝔖 (toFun 𝔖 f) = f := rfl

section Group

variable [Group β]

example (f g : α →ᵤ[𝔖] β) : f * g = ofFun' (f.toFun' * g.toFun') := by
  with_reducible_and_instances rfl
example : (1 : α →ᵤ[𝔖] β) = ofFun' 1 := by with_reducible_and_instances rfl
example (f : α →ᵤ[𝔖] β) : f⁻¹ = ofFun' f.toFun'⁻¹ := by with_reducible_and_instances rfl
example (f g : α →ᵤ[𝔖] β) : f / g = ofFun' (f.toFun' / g.toFun') := by
  with_reducible_and_instances rfl
example (n : ℕ) (f : α →ᵤ[𝔖] β) : f ^ n = ofFun' (f.toFun' ^ n) := by
  with_reducible_and_instances rfl

example : (Group.toDivInvMonoid.toMonoid : Monoid (α →ᵤ[𝔖] β)) = instMonoidUniformOnFun := by
  with_reducible_and_instances rfl
example : (Monoid.toMulOneClass.toMul : Mul (α →ᵤ[𝔖] β)) = instMulUniformOnFun := by
  with_reducible_and_instances rfl

end Group

example [CommGroup β] : (CommGroup.toGroup : Group (α →ᵤ[𝔖] β)) = instGroupUniformOnFun := by
  with_reducible_and_instances rfl

section Module

variable [Semiring R] [AddCommMonoid β] [Module R β]

example (r : R) (f : α →ᵤ[𝔖] β) : r • f = ofFun' (r • f.toFun') := by
  with_reducible_and_instances rfl
example : (Module.toDistribMulAction : DistribMulAction R (α →ᵤ[𝔖] β)) =
    instDistribMulActionUniformOnFun := by
  with_reducible_and_instances rfl

end Module

example [AddCommGroup β] :
    (AddCommGroup.toIntModule _ : Module ℤ (α →ᵤ[𝔖] β)) = instModuleUniformOnFun := by
  with_reducible_and_instances rfl
