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

A class pack groups a type with an instance of a one-parameter class. The pack of the class `C` is
the structure `CPack` with the fields `α` and `inst : C α`. Pack congruences (`@[dsimp_congr]`
theorems) state their hypotheses as equations between such packs.

The command `class_pack C` declares the structure `CPack` for a class `C : Type u → Type u`.

The command `derive_pack_edges` declares, for each one-parameter class `C` defined in the current
file, the structure `CPack`. It also adds, for each one-parameter parent `D` of `C`, the lens
`CPack.mk α i = CPack.mk α' i' → DPack.mk α i.toD = DPack.mk α' i'.toD`.
-/

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

/-- The name of the pack structure of the class `C`. -/
meta def packName (C : Name) : Name := C.appendAfter "Pack"

/-- Declares the pack structure of the one-parameter class `C`, unless it exists. -/
meta def addClassPack (C : Name) : CommandElabM Unit := do
  if (← getEnv).contains (packName C) then return
  let src := s!"/-- A type with an instance of the class `{C}`. -/
public structure _root_.{packName C}.\{u_pack} where
  /-- The carrier. -/
  α : Type u_pack
  /-- The instance. -/
  [inst : _root_.{C} α]"
  match Parser.runParserCategory (← getEnv) `command src with
  | .error e => throwError "class_pack: cannot parse the pack of {C}: {e}"
  | .ok stx => elabCommand stx

/-- `class_pack C` declares the structure `CPack` with the fields `α : Type u` and `inst : C α`
for the class `C : Type u → Type u`. -/
elab "class_pack " C:ident : command => do
  let C ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo C
  unless isOneParamClass (← getEnv) C do
    throwError "class_pack: {C} is not a class of type `Type u → Type u`"
  addClassPack C

/-- `derive_pack_edges` declares, for each one-parameter class `C` defined in the current file, the
pack structure `CPack`. It adds, for each parent projection `C.toD` to a one-parameter class `D`,
the `@[dsimp_congr]` lens
`C.toD.packLens : CPack.mk α i = CPack.mk α' i' → DPack.mk α i.toD = DPack.mk α' i'.toD`.
Packs and lenses whose name already exists are skipped. -/
elab "derive_pack_edges" : command => do
  let env ← getEnv
  let classes := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
    if (env.getModuleIdxFor? n).isNone && isOneParamClass env n then acc.push n else acc
  let classes := classes.qsort Name.lt
  for C in classes do addClassPack C
  for C in classes do
    for p in getStructureParentInfo env C do
      let D := p.structName
      unless isOneParamClass (← getEnv) D do continue
      let thm := p.projFn ++ `packLens
      if (← getEnv).contains thm then continue
      unless (← getEnv).contains (packName D) do
        logWarning m!"derive_pack_edges: the pack of {D} does not exist; skipped the lens {thm}"
        continue
      let r (n : Name) : String := s!"_root_.{n}"
      let src := s!"@[dsimp_congr] public theorem {r thm}.\{u_pack} \{α α' : Type u_pack}
    \{i : {r C} α} \{i' : {r C} α'}
    (h : @{r (packName C)}.mk α i = @{r (packName C)}.mk α' i') :
    @{r (packName D)}.mk α (@{r p.projFn} α i) =
      @{r (packName D)}.mk α' (@{r p.projFn} α' i') := by
  cases h; rfl"
      match Parser.runParserCategory (← getEnv) `command src with
      | .error e => logWarning m!"derive_pack_edges: cannot parse the lens {thm}: {e}"
      | .ok stx =>
        try elabCommand stx
        catch e => logWarning m!"derive_pack_edges: skipped the lens {thm}: {e.toMessageData}"

end Mathlib.Tactic.PackLens

@[expose] public section

/-! Packs of the one-parameter classes of Lean core that pack congruences in Mathlib use. -/

class_pack Add
class_pack Mul
class_pack Neg
class_pack Zero
class_pack One
class_pack Inv
class_pack Div
class_pack Sub
class_pack Mod
class_pack LE
class_pack LT
class_pack Min
class_pack Max
class_pack Ord
class_pack BEq
class_pack NatCast
class_pack IntCast
class_pack Dvd
class_pack SDiff

/-- A type with an `SMul α` instance. -/
structure SMulPack.{ua, ub} (α : Type ua) where
  /-- The carrier. -/
  β : Type ub
  /-- The instance. -/
  [inst : SMul α β]

end
