/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Derivatives of maps in the tangent bundle

This file contains properties of derivatives which need the manifold structure of the tangent
bundle. Notably, it includes formulas for the tangent maps to charts, and unique differentiability
statements for subsets of the tangent bundle.
-/

@[expose] public section

open Bundle Set
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' 1 M']


/-- The derivative of the chart at a base point is the chart of the tangent bundle, composed with
the identification `tangentBundleModelSpaceEquiv` between the tangent bundle of the model space and
the product space. -/
theorem tangentMap_chart {p q : TangentBundle I M} (h : q.1 ∈ (chartAt H p.1).source) :
    tangentMap% (chartAt H p.1) q =
      (tangentBundleModelSpaceEquiv I).symm
        ((chartAt (ModelProd H E) p : TangentBundle I M → ModelProd H E) q) := by
  dsimp [tangentMap]
  rw [MDifferentiableAt.mfderiv]
  · rfl
  · exact mdifferentiableAt_atlas (chart_mem_atlas _ _) h

/-- The derivative of the inverse of the chart at a base point is the inverse of the chart of the
tangent bundle, composed with the identification `tangentBundleModelSpaceEquiv` between the tangent
bundle of the model space and the product space. -/
theorem tangentMap_chart_symm {p : TangentBundle I M} {q : TangentBundle I H}
    (h : q.1 ∈ (chartAt H p.1).target) :
    tangentMap% (chartAt H p.1).symm q =
      (chartAt (ModelProd H E) p).symm (tangentBundleModelSpaceEquiv I q) := by
  dsimp only [tangentMap]
  rw [MDifferentiableAt.mfderiv (mdifferentiableAt_atlas_symm (chart_mem_atlas _ _) h)]
  simp only [TangentBundle.chartAt, tangentBundleCore,
    mfld_simps]
  -- `simp` fails to apply `PartialEquiv.prod_symm` with `ModelProd`
  refine TotalSpace.ext rfl (heq_of_eq ?_)
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
    id_eq]
  -- the base point of the `fderivWithin` on the left is `I q.proj`, while on the right it is
  -- `I ((chartAt H p.proj) ((chartAt H p.proj).symm q.proj))`; these agree by `right_inv`
  rw [show (I q.proj : E) = I (chartAt H p.proj ((chartAt H p.proj).symm q.proj)) from
    congrArg I ((chartAt H p.proj).right_inv h).symm]
  rfl

lemma mfderiv_chartAt_eq_tangentCoordChange {x y : M} (hsrc : x ∈ (chartAt H y).source) :
    mfderiv% (chartAt H y) x =
      (TangentSpace.equivModel I (chartAt H y x)).symm.toContinuousLinearMap ∘L
        tangentCoordChange I x y x ∘L (TangentSpace.equivModel I x).toContinuousLinearMap := by
  have := mdifferentiableAt_atlas (I := I) (ChartedSpace.chart_mem_atlas _) hsrc
  simp [mfderiv, ite_eq_left this, Function.comp_assoc]
  rfl

/-- The preimage under the projection from the tangent bundle of a set with unique differential in
the basis also has unique differential. -/
theorem UniqueMDiffOn.tangentBundle_proj_preimage {s : Set M} (hs : UniqueMDiffOn I s) :
    UniqueMDiffOn I.tangent (π E (TangentSpace I) ⁻¹' s) :=
  hs.bundle_preimage _

/- TODO: define `vmfderiv` for the derivative from a vector space to a manifold, and use it
to rewrite the last term in the expression below. -/
/-- To write a linear map between tangent spaces in coordinates amounts to precomposing and
postcomposing it with derivatives of extended charts.
Concrete version of `inTangentCoordinates_eq`. -/
lemma inTangentCoordinates_eq_mfderiv_comp
    {N : Type*} {f : N → M} {g : N → M'}
    {ϕ : Π x : N, TangentSpace% (f x) →L[𝕜] TangentSpace% (g x)} {x₀ : N} {x : N}
    (hx : f x ∈ (chartAt H (f x₀)).source) (hy : g x ∈ (chartAt H' (g x₀)).source) :
    inTangentCoordinates I I' f g ϕ x₀ x =
      mvfderiv I' (extChartAt I' (g x₀)) (g x) ∘L (ϕ x) ∘L
        (TangentSpace.cast I ((extChartAt I (f x₀)).left_inv (by rwa [extChartAt_source]))
          ).toContinuousLinearMap ∘L
        mfderiv[range I] (extChartAt I (f x₀)).symm (extChartAt I (f x₀) (f x)) ∘L
        (NormedSpace.fromTangentSpace (extChartAt I (f x₀) (f x))).symm.toContinuousLinearMap := by
  rw [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_trivializationAt hy,
    TangentBundle.symmL_trivializationAt hx]
  rfl

theorem TangentSpace.homEquivModel_eq_inTangentCoordinates {N : Type*} (f : N → M) (g : N → M')
    (ϕ : Π x : N, TangentSpace I (f x) →L[𝕜] TangentSpace I' (g x)) (x : N) :
    TangentSpace.homEquivModel I I' (f x) (g x) (ϕ x) = inTangentCoordinates I I' f g ϕ x x := by
  rw [inTangentCoordinates_eq f g ϕ (mem_chart_source H (f x)) (mem_chart_source H' (g x))]
  ext v
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    (tangentBundleCore I M).coordChange_self _ _ (mem_achart_source H (f x)),
    (tangentBundleCore I' M').coordChange_self _ _ (mem_achart_source H' (g x))]
  rfl

open Bundle
variable (I) in
/-- The canonical identification between the tangent bundle to the model space and the product,
as a diffeomorphism. -/
noncomputable def tangentBundleModelSpaceDiffeomorph (n : ℕ∞) :
    TangentBundle I H ≃ₘ^n⟮I.tangent, I.prod 𝓘(𝕜, E)⟯ ModelProd H E where
  __ := tangentBundleModelSpaceEquiv I
  contMDiff_toFun := contMDiff_tangentBundleModelSpaceHomeomorph
  contMDiff_invFun := contMDiff_tangentBundleModelSpaceHomeomorph_symm
