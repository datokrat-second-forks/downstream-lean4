/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Topology.Homeomorph.Defs

/-!
# Transfer topological structure across `Equiv`s

We show how to transport a topological space structure across an `Equiv` and prove that this
make the equivalence a homeomorphism between the original space and the transported topology.

-/

@[expose] public section

variable {α β : Type*}

namespace Equiv

-- See note [instance transfer via equivalence]
/-- Transfer a `TopologicalSpace` across an `Equiv` -/
protected abbrev topologicalSpace [TopologicalSpace β] (e : α ≃ β) :
    TopologicalSpace α :=
  .induced e.toFun ‹_›

/-- An equivalence `e : α ≃ β` gives a homeomorphism `α ≃ₜ β` where the topological space structure
on `α` is the one obtained by transporting the topological space structure on `β` back along `e`. -/
def homeomorph [TopologicalSpace β] (e : α ≃ β) :
    letI := e.topologicalSpace
    α ≃ₜ β :=
  letI := e.topologicalSpace
  { e with
    continuous_toFun := continuous_induced_dom
    continuous_invFun := by
      simp only [Equiv.invFun_as_coe]
      convert! continuous_coinduced_rng
      rw [e.coinduced_symm]
      rfl }

end Equiv

/-- A canonical equivalence is a homeomorphism for the topology transported along it. -/
def Lean.CanonicalEquivalence.homeomorph (e : Lean.CanonicalEquivalence α β) [TopologicalSpace β] :
    letI := (TopologicalSpace.canonicalCongr e).invFun ‹TopologicalSpace β›
    α ≃ₜ β :=
  letI := (TopologicalSpace.canonicalCongr e).invFun ‹TopologicalSpace β›
  { toFun := e.toFun
    invFun := e.invFun
    left_inv := e.left_inv
    right_inv := e.right_inv
    continuous_toFun := ⟨fun s hs ↦ by
      have : e.invFun ⁻¹' (e.toFun ⁻¹' s) = s := Set.ext fun y ↦ by
        change e.toFun (e.invFun y) ∈ s ↔ y ∈ s; rw [e.right_inv y]
      change IsOpen (e.invFun ⁻¹' (e.toFun ⁻¹' s))
      rwa [this]⟩
    continuous_invFun := ⟨fun _ hs ↦ hs⟩ }
