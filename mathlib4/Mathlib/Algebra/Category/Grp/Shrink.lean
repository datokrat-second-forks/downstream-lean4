/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# Shrinking a functor to `GrpCat`

For a functor `C ⥤ GrpCat.{w'}` with `w`-small image, we shrink to a functor `C ⥤ GrpCat.{w}`.
-/

@[expose] public section

universe w w' v u

open CategoryTheory

variable {C : Type u} [Category.{v} C]

instance (F : C ⥤ GrpCat.{w'}) [∀ X, Small.{w} (F.obj X)] :
    FunctorToTypes.Small.{w} (F ⋙ forget _) :=
  fun X ↦ inferInstanceAs <| Small.{w} (F.obj X)

/-- A functor `F : C ⥤ GrpCat.{w'}` factors through `GrpCat.{w}` if all the
monoids are `w`-small. -/
@[simps, pp_with_univ]
noncomputable def GrpCat.shrinkFunctor (F : C ⥤ GrpCat.{w'}) [∀ X, Small.{w} (F.obj X)] :
    C ⥤ GrpCat.{w} where
  obj X := ↧(Shrink.{w} (F.obj X))
  map {X Y} f := GrpCat.ofHom <|
    (Shrink.mulEquiv.symm.toMonoidHom.comp (F.map f).hom).comp Shrink.mulEquiv.toMonoidHom

/-- Pack root lemma: the group pack of `(GrpCat.shrinkFunctor F).obj X`. -/
@[simp] theorem GrpCat.shrinkFunctor_obj_classPack.{ws, wf, vc, uc} {C : Type uc}
    [Category.{vc} C] (F : C ⥤ GrpCat.{wf}) [∀ X, Small.{ws} (F.obj X)] (X : C) :
    @ClassPack.mk Group ((GrpCat.shrinkFunctor.{ws} F).obj X)
        ((GrpCat.shrinkFunctor.{ws} F).obj X).str =
      @ClassPack.mk Group (Shrink.{ws} (F.obj X)) Shrink.instGroup :=
  rfl

/-- The natural transformation `GrpCat.shrinkFunctor.{w} F ⟶ GrpCat.shrinkFunctor.{w} G`
induces by a natural transformation `τ : F ⟶ G` between `w`-small functors to monoids. -/
@[simps]
noncomputable def GrpCat.shrinkFunctorMap {F G : C ⥤ GrpCat.{w'}} (τ : F ⟶ G)
    [∀ X, Small.{w} (F.obj X)] [∀ X, Small.{w} (G.obj X)] :
    GrpCat.shrinkFunctor.{w} F ⟶ GrpCat.shrinkFunctor.{w} G where
  app X := GrpCat.ofHom <|
    (Shrink.mulEquiv.symm.toMonoidHom.comp (τ.app X).hom).comp Shrink.mulEquiv.toMonoidHom
  naturality X Y f := by
    ext x
    exact
      congr($((FunctorToTypes.shrinkMap.{w} (Functor.whiskerRight τ (forget _))).naturality f) x)
