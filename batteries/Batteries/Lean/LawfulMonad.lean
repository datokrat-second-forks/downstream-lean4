/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Lean.Elab.Command
import all Init.System.ST

@[expose] public section

/-!
# Construct `LawfulMonad` instances for the Lean monad stack.
-/

open Lean Elab Term Tactic Command

instance : LawfulMonad (ST σ) := .mk' _
  (id_map := fun x => rfl)
  (pure_bind := fun x f => rfl)
  (bind_assoc := fun f g x => rfl)

instance  : LawfulMonad (EST ε σ) := .mk' _
  (id_map := fun x => congrArg EST.mk <| funext fun v => by cases x.run v <;> rfl)
  (pure_bind := fun x f => rfl)
  (bind_assoc := fun f g x => congrArg EST.mk <| funext fun v => by
    simp only [bind, EST.bind]
    cases f.run v <;> rfl)

instance : LawfulMonad (EIO ε) := .mk' _
  (id_map := fun x => congrArg EIO.mk (id_map x.toEST))
  (pure_bind := fun x f => congrArg EIO.mk (pure_bind x (fun a => (f a).toEST)))
  (bind_assoc := fun x f g =>
    congrArg EIO.mk (bind_assoc x.toEST (fun a => (f a).toEST) (fun b => (g b).toEST)))
instance : LawfulMonad BaseIO := .mk' _
  (id_map := fun x => congrArg BaseIO.mk (id_map x.toST))
  (pure_bind := fun x f => congrArg BaseIO.mk (pure_bind x (fun a => (f a).toST)))
  (bind_assoc := fun x f g =>
    congrArg BaseIO.mk (bind_assoc x.toST (fun a => (f a).toST) (fun b => (g b).toST)))
instance : LawfulMonad IO := inferInstanceAs <| LawfulMonad (EIO _)

instance : LawfulMonad CoreM :=
  inferInstanceAs <| LawfulMonad (ReaderT _ <| StateRefT' _ _ (EIO Exception))
instance : LawfulMonad MetaM :=
  inferInstanceAs <| LawfulMonad (ReaderT _ <| StateRefT' _ _ CoreM)
instance : LawfulMonad TermElabM :=
  inferInstanceAs <| LawfulMonad (ReaderT _ <| StateRefT' _ _ MetaM)
instance : LawfulMonad TacticM :=
  inferInstanceAs <| LawfulMonad (ReaderT _ $ StateRefT' _ _ $ TermElabM)
instance : LawfulMonad CommandElabM :=
  inferInstanceAs <| LawfulMonad (ReaderT _ $ StateRefT' _ _ $ EIO _)
