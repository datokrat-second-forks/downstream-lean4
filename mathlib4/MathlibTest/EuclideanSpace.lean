import Mathlib.Analysis.InnerProductSpace.PiL2

#guard_expr !₂[] = PiLp.toLp 2 (α := fun _ : Fin 0 => _) ![]
#guard_expr !₂[1, 2, 3] = PiLp.toLp 2 (α := fun _ : Fin 3 => ℕ) ![1, 2, 3]
#guard_expr !₁[1, 2, (3 : ℝ)] = PiLp.toLp 1 (α := fun _ : Fin 3 => ℝ) ![1, 2, 3]

section delaborator

/-- info: !₂[1, 2, 3] : PiLp 2 fun (x : Fin 3) => ℕ -/
#guard_msgs in
#check !₂[1, 2, 3]

/-- info: !₀[] : PiLp 0 fun (x : Fin 0) => ?_ -/
#guard_msgs in
#check !₀[]

section var
variable {p : ENNReal}
/-- info: PiLp.toLp p ![1, 2, 3] : PiLp p fun (x : Fin 3) => ℕ -/
#guard_msgs in#check !ₚ[1, 2, 3]
end var

section tombstoned_var
/- Here the `p` in the subscript is shadowed by a later p; so even if we do
make the delaborator less conservative, it should not fire here since `✝` cannot
be subscripted. -/
variable {p : ENNReal} {x} (hx : x = !ₚ[1, 2, 3]) (p : True)
/-- info: hx : x = PiLp.toLp p✝ ![1, 2, 3] -/
#guard_msgs in #check hx
end tombstoned_var

end delaborator

section PiLp

variable {p : ENNReal} {ι : Type*} {α : ι → Type*}

-- The dependent family can be inferred through the constructor and projection.
example (f : ∀ i, α i) : ∃ x : PiLp p α, x.ofLp = f := ⟨_, rfl⟩

example (x : PiLp p α) : PiLp.toLp p x.ofLp = x := rfl

example (f : ∀ i, α i) (i : ι) : PiLp.toLp p f i = f i := rfl

-- A generic `WithLp` wrapper is no longer a `PiLp` vector.
example (f : ∀ i, α i) : PiLp p α := by
  fail_if_success exact WithLp.toLp p f
  exact PiLp.toLp p f

-- Transport finite generation without requiring a finite index type.
example [∀ i, AddCommGroup (α i)] [Module.Finite ℤ (∀ i, α i)] :
    Module.Finite ℤ (PiLp p α) := inferInstance

-- Coordinate notation and the Euclidean norm still work together.
example : ‖(!₂[3, 4] : EuclideanSpace ℝ (Fin 2))‖ = 5 := by
  norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_succ]
  rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5)]

end PiLp
