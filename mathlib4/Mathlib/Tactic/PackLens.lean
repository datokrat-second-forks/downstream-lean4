/-
Copyright (c) 2026 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public meta import Lean.Elab.Command
public import Mathlib.Init

/-!
# Class packs and lenses for parent projections

`ClassPack c` groups a type with an instance of the one-parameter class `c`. Pack congruences
(`@[dsimp_congr]` theorems) state their hypotheses as equations between such packs.

The command `derive_pack_edges` adds, for each one-parameter class `C` defined in the current file
and each one-parameter parent `D` of `C`, the lens
`ClassPack.mk α i = ClassPack.mk α' i' → ClassPack.mk α i.toD = ClassPack.mk α' i'.toD`.
-/

@[expose] public section

universe u v

set_option checkBinderAnnotations false in
/-- A type with an instance of the one-parameter class `c`. -/
structure ClassPack (c : Type u → Type v) where
  /-- The carrier. -/
  α : Type u
  /-- The instance. -/
  [inst : c α]

end

namespace Mathlib.Tactic.PackLens

open Lean Elab Command

/-- Whether `n` is a class of type `Type u → Type u` with the single universe parameter `u`. -/
meta def isOneParamClass (env : Environment) (n : Name) : Bool := Id.run do
  let some ci := env.find? n | return false
  unless isClass env n && isStructure env n do return false
  match ci.type with
  | .forallE _ (.sort (.succ (.param a))) (.sort (.succ (.param b))) .default =>
    return a == b && ci.levelParams == [a]
  | _ => return false

/-- `derive_pack_edges` adds, for each one-parameter class `C` defined in the current file and each
parent projection `C.toD` to a one-parameter class `D`, the `@[dsimp_congr]` lens
`C.toD.packLens : ClassPack.mk α i = ClassPack.mk α' i' →
  ClassPack.mk α i.toD = ClassPack.mk α' i'.toD`.
Lenses whose name already exists are skipped. -/
elab "derive_pack_edges" : command => do
  let env ← getEnv
  let classes := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
    if (env.getModuleIdxFor? n).isNone && isOneParamClass env n then acc.push n else acc
  for C in classes.qsort Name.lt do
    for p in getStructureParentInfo env C do
      let D := p.structName
      unless isOneParamClass (← getEnv) D do continue
      let thm := p.projFn ++ `packLens
      if (← getEnv).contains thm then continue
      let r (n : Name) : String := s!"_root_.{n}"
      let src := s!"@[dsimp_congr] public theorem {r thm}.\{u_pack} \{α α' : Type u_pack}
    \{i : {r C} α} \{i' : {r C} α'}
    (h : @_root_.ClassPack.mk {r C} α i = @_root_.ClassPack.mk {r C} α' i') :
    @_root_.ClassPack.mk {r D} α (@{r p.projFn} α i) =
      @_root_.ClassPack.mk {r D} α' (@{r p.projFn} α' i') := by
  cases h; rfl"
      match Parser.runParserCategory (← getEnv) `command src with
      | .error e => logWarning m!"derive_pack_edges: cannot parse the lens {thm}: {e}"
      | .ok stx =>
        try elabCommand stx
        catch e => logWarning m!"derive_pack_edges: skipped the lens {thm}: {e.toMessageData}"

end Mathlib.Tactic.PackLens
