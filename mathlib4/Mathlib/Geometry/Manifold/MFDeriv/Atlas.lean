/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.Notation

/-!
# Differentiability of models with corners and (extended) charts

In this file, we analyse the differentiability of charts, models with corners and extended charts.
We show that
* models with corners are differentiable
* charts are differentiable on their source
* `mdifferentiableOn_extChartAt`: `extChartAt` is differentiable on its source

Suppose an open partial homeomorphism `e` is differentiable. This file shows
* `OpenPartialHomeomorph.MDifferentiable.mfderiv`: its derivative is a continuous linear equivalence
* `OpenPartialHomeomorph.MDifferentiable.mfderiv_bijective`: its derivative is bijective;
  there are also spellings with trivial kernel and full range

In particular, (extended) charts have bijective differential.

## Tags
charts, differentiable, bijective
-/

@[expose] public section

noncomputable section

open Bundle Set

open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']

section ModelWithCorners
namespace ModelWithCorners

/- In general, the model with corner `I` is implicit in most theorems in differential geometry, but
this section is about `I` as a map, not as a parameter. Therefore, we make it explicit. -/
variable (I)

/-! #### Model with corners -/

/-- The derivative of `I : H → E` at `x` is `TangentSpace.equivModel I x`, read in the tangent space
to `E` at `I x`. -/
protected theorem hasMFDerivAt {x} :
    HasMFDerivAt I 𝓘(𝕜, E) I x ((NormedSpace.fromTangentSpace (I x)).symm.toContinuousLinearMap ∘L
      (TangentSpace.equivModel I x).toContinuousLinearMap) :=
  ⟨I.continuousAt, (hasFDerivWithinAt_id _ _).congr' I.rightInvOn (mem_range_self _)⟩

protected theorem hasMFDerivWithinAt {s x} :
    HasMFDerivWithinAt I 𝓘(𝕜, E) I s x
      ((NormedSpace.fromTangentSpace (I x)).symm.toContinuousLinearMap ∘L
        (TangentSpace.equivModel I x).toContinuousLinearMap) :=
  I.hasMFDerivAt.hasMFDerivWithinAt

protected theorem mdifferentiableWithinAt {s x} : MDiffAt[s] I x :=
  I.hasMFDerivWithinAt.mdifferentiableWithinAt

protected theorem mdifferentiableAt {x} : MDiffAt I x :=
  I.hasMFDerivAt.mdifferentiableAt

protected theorem mdifferentiableOn {s} : MDiff[s] I := fun _ _ =>
  I.mdifferentiableWithinAt

protected theorem mdifferentiable : MDiff I := fun _ => I.mdifferentiableAt

theorem hasMFDerivWithinAt_symm {x} (hx : x ∈ range I) :
    HasMFDerivWithinAt 𝓘(𝕜, E) I I.symm (range I) x
      ((TangentSpace.equivModel I (I.symm x)).symm.toContinuousLinearMap ∘L
        (NormedSpace.fromTangentSpace x).toContinuousLinearMap) :=
  ⟨I.continuousWithinAt_symm,
    (hasFDerivWithinAt_id _ _).congr' (fun _y hy => I.rightInvOn hy.1) ⟨hx, mem_range_self _⟩⟩

theorem mdifferentiableOn_symm : MDiff[range I] I.symm := fun _x hx =>
  (I.hasMFDerivWithinAt_symm hx).mdifferentiableWithinAt

theorem mdifferentiableWithinAt_symm {z : E} (hz : z ∈ range I) :
    MDiffAt[range I] I.symm z :=
  I.mdifferentiableOn_symm z hz

end ModelWithCorners

end ModelWithCorners

section Charts

variable {e : OpenPartialHomeomorph M H}

theorem mdifferentiableAt_of_mem_maximalAtlas
    (h : e ∈ IsManifold.maximalAtlas I 1 M) {x : M} (hx : x ∈ e.source) : MDiffAt e x :=
  (contMDiffAt_of_mem_maximalAtlas h hx).mdifferentiableAt one_ne_zero

lemma mdifferentiableAt_symm_of_mem_maximalAtlas
    (h : e ∈ IsManifold.maximalAtlas I 1 M) {x : H} (hx : x ∈ e.target) :
    MDiffAt e.symm x :=
  contMDiffAt_symm_of_mem_maximalAtlas h hx |>.mdifferentiableAt one_ne_zero

variable [IsManifold I 1 M] [IsManifold I' 1 M'] [IsManifold I'' 1 M'']

theorem mdifferentiableAt_atlas (h : e ∈ atlas H M) {x : M} (hx : x ∈ e.source) : MDiffAt e x :=
  contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas h) hx
    |>.mdifferentiableAt one_ne_zero

theorem mdifferentiableOn_atlas (h : e ∈ atlas H M) : MDiff[e.source] e :=
  fun _x hx => (mdifferentiableAt_atlas h hx).mdifferentiableWithinAt

theorem mdifferentiableAt_atlas_symm (h : e ∈ atlas H M) {x : H} (hx : x ∈ e.target) :
    MDiffAt e.symm x :=
  mdifferentiableAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas h) hx

theorem mdifferentiableOn_atlas_symm (h : e ∈ atlas H M) : MDiff[e.target] e.symm :=
  fun _x hx => (mdifferentiableAt_atlas_symm h hx).mdifferentiableWithinAt

theorem mdifferentiable_of_mem_atlas (h : e ∈ atlas H M) : e.MDifferentiable I I :=
  ⟨mdifferentiableOn_atlas h, mdifferentiableOn_atlas_symm h⟩

theorem mdifferentiable_chart (x : M) : (chartAt H x).MDifferentiable I I :=
  mdifferentiable_of_mem_atlas (chart_mem_atlas _ _)

end Charts

/-! ### Differentiable open partial homeomorphisms -/

namespace OpenPartialHomeomorph.MDifferentiable
variable {e : OpenPartialHomeomorph M M'} (he : e.MDifferentiable I I')
  {e' : OpenPartialHomeomorph M' M''}
include he

nonrec theorem symm : e.symm.MDifferentiable I' I := he.symm

protected theorem mdifferentiableAt {x : M} (hx : x ∈ e.source) : MDiffAt e x :=
  (he.1 x hx).mdifferentiableAt (e.open_source.mem_nhds hx)

theorem mdifferentiableAt_symm {x : M'} (hx : x ∈ e.target) : MDiffAt e.symm x :=
  (he.2 x hx).mdifferentiableAt (e.open_target.mem_nhds hx)

/-- The derivative of `e.symm` after that of `e` is the identity, up to the identification of the
tangent spaces at `x` and at `e.symm (e x)`. -/
theorem symm_comp_deriv {x : M} (hx : x ∈ e.source) :
    (mfderiv% e.symm (e x)).comp (mfderiv% e x) =
      (TangentSpace.cast I (e.left_inv hx).symm).toContinuousLinearMap := by
  have hcomp : mfderiv% (e.symm ∘ e) x = (mfderiv% e.symm (e x)).comp (mfderiv% e x) :=
    mfderiv_comp x (he.mdifferentiableAt_symm (e.map_source hx)) (he.mdifferentiableAt hx)
  have hEq : (e.symm ∘ e : M → M) =ᶠ[𝓝 x] _root_.id :=
    Filter.mem_of_superset (e.open_source.mem_nhds hx) (by mfld_set_tac)
  rw [← hcomp, hEq.mfderiv_eq, mfderiv_id, ContinuousLinearMap.comp_id]

theorem comp_symm_deriv {x : M'} (hx : x ∈ e.target) :
    (mfderiv% e (e.symm x)).comp (mfderiv% e.symm x) =
      (TangentSpace.cast I' (e.right_inv hx).symm).toContinuousLinearMap :=
  he.symm.symm_comp_deriv hx

/-- The derivative of a differentiable open partial homeomorphism, as a continuous linear
equivalence between the tangent spaces at `x` and `e x`. -/
protected def mfderiv (he : e.MDifferentiable I I') {x : M} (hx : x ∈ e.source) :
    TangentSpace I x ≃L[𝕜] TangentSpace I' (e x) :=
  { mfderiv% e x with
    invFun v := TangentSpace.cast I (e.left_inv hx) (mfderiv% e.symm (e x) v)
    continuous_toFun := (mfderiv% e x).cont
    continuous_invFun :=
      (TangentSpace.cast I (e.left_inv hx)).continuous.comp (mfderiv% e.symm (e x)).cont
    left_inv := fun y => by
      have := congr($(he.symm_comp_deriv hx) y)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at this
      change TangentSpace.cast I _ (mfderiv% e.symm (e x) (mfderiv% e x y)) = y
      simp [this]
    right_inv := fun y => by
      have key {a b : M} (h : a = b) (v : TangentSpace I a) :
          mfderiv% e b (TangentSpace.cast I h v) =
            TangentSpace.cast I' (congrArg e h) (mfderiv% e a v) := by
        subst h; rfl
      have := congr($(he.comp_symm_deriv (e.map_source hx)) y)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at this
      change mfderiv% e x (TangentSpace.cast I _ (mfderiv% e.symm (e x) y)) = y
      simp [key, this] }

theorem mfderiv_bijective {x : M} (hx : x ∈ e.source) : Function.Bijective (mfderiv% e x) :=
  (he.mfderiv hx).bijective

theorem mfderiv_injective {x : M} (hx : x ∈ e.source) : Function.Injective (mfderiv% e x) :=
  (he.mfderiv hx).injective

theorem mfderiv_surjective {x : M} (hx : x ∈ e.source) : Function.Surjective (mfderiv% e x) :=
  (he.mfderiv hx).surjective

theorem ker_mfderiv_eq_bot {x : M} (hx : x ∈ e.source) : (mfderiv% e x).ker = ⊥ :=
  (he.mfderiv hx).toLinearEquiv.ker

theorem range_mfderiv_eq_top {x : M} (hx : x ∈ e.source) : (mfderiv% e x).range = ⊤ :=
  (he.mfderiv hx).toLinearEquiv.range

theorem range_mfderiv_eq_univ {x : M} (hx : x ∈ e.source) : range (mfderiv% e x) = univ :=
  (he.mfderiv_surjective hx).range_eq

theorem trans (he' : e'.MDifferentiable I' I'') : (e.trans e').MDifferentiable I I'' := by
  constructor
  · intro x hx
    simp only [mfld_simps] at hx
    exact
      ((he'.mdifferentiableAt hx.2).comp _ (he.mdifferentiableAt hx.1)).mdifferentiableWithinAt
  · intro x hx
    simp only [mfld_simps] at hx
    exact
      ((he.symm.mdifferentiableAt hx.2).comp _
          (he'.symm.mdifferentiableAt hx.1)).mdifferentiableWithinAt

end OpenPartialHomeomorph.MDifferentiable

/-! ### Differentiability of `extChartAt` -/

section

open IsManifold

variable {e : OpenPartialHomeomorph M H}

theorem OpenPartialHomeomorph.mdifferentiableAt_extend
    {x : M} (he : e ∈ maximalAtlas I 1 M) (hx : x ∈ e.source) :
    MDiffAt (e.extend I) x :=
  e.contMDiffAt_extend he hx |>.mdifferentiableAt (by simp)

theorem OpenPartialHomeomorph.mdifferentiableOn_extend (he : e ∈ maximalAtlas I 1 M) :
    MDiff[e.source] (e.extend I) :=
  e.contMDiffOn_extend he |>.mdifferentiableOn (by simp)

variable {z : E}

theorem mdifferentiableWithinAt_extend_symm
    (he : e ∈ maximalAtlas I 1 M) (h : z ∈ (e.extend I).target) :
    MDiffAt[range I] (e.extend I).symm z := by
  have Z : MDiffAt[range ↑I] I.symm z :=
    I.mdifferentiableWithinAt_symm (e.extend_target_subset_range h)
  apply MDifferentiableAt.comp_mdifferentiableWithinAt _ _ Z
  exact mdifferentiableAt_symm_of_mem_maximalAtlas he (by simp_all)

theorem mdifferentiableOn_extend_symm (he : e ∈ maximalAtlas I 1 M) :
    MDiff[(e.extend I).target] (e.extend I).symm := by
  intro y hy
  exact mdifferentiableWithinAt_extend_symm he hy |>.mono (e.extend_target_subset_range)

/-- The composition of the derivative of an extended chart `e.extend I` with the derivative of its
inverse `(e.extend I).symm` gives the identity, up to the identification of the tangent spaces at
`y` and at `e.extend I ((e.extend I).symm y)`.
Version where the basepoint belongs to `(e.extend I).target`. -/
lemma mfderiv_extend_comp_mfderivWithin_extend_symm
    {y : E} (he : e ∈ maximalAtlas I 1 M) (hy : y ∈ (e.extend I).target) :
    (mfderiv% (e.extend I) ((e.extend I).symm y)) ∘L (mfderiv[range I] (e.extend I).symm y) =
      (TangentSpace.cast 𝓘(𝕜, E) ((e.extend I).right_inv hy).symm).toContinuousLinearMap := by
  have U : UniqueMDiffAt[range I] y := by
    apply I.uniqueMDiffOn
    apply e.extend_target_subset_range hy
  have h'y : (e.extend I).symm y ∈ e.source := PartialEquiv.map_target _ (by simp_all)
  have hEq : ((e.extend I) ∘ (e.extend I).symm) =ᶠ[𝓝[range I] y] _root_.id := by
    filter_upwards [(e.extend I).right_inv hy ▸ e.extend_target_mem_nhdsWithin h'y (I := I)]
      with z hz
    simp_all
  rw [← mfderiv_comp_mfderivWithin _ (e.mdifferentiableAt_extend he h'y)
      (mdifferentiableWithinAt_extend_symm he hy) U,
    hEq.mfderivWithin_eq ((e.extend I).right_inv hy), mfderivWithin_id U,
    ContinuousLinearMap.comp_id]

/-- The composition of the derivative of the inverse of an extended chart `e.extend I` with the
derivative of `e.extend I` gives the identity, up to the identification of the tangent spaces at
`y` and at `(e.extend I).symm (e.extend I y)`.
Version where the basepoint belongs to `e.source`. -/
lemma mfderivWithin_extend_symm_comp_mfderiv_extend'
    {y : M} (he : e ∈ maximalAtlas I 1 M) (hy : y ∈ e.source) :
    (mfderiv[range I] (e.extend I).symm (e.extend I y)) ∘L (mfderiv% (e.extend I) y) =
      (TangentSpace.cast I
        ((e.extend I).left_inv (by simpa using hy)).symm).toContinuousLinearMap := by
  have hy' : y ∈ (e.extend I).source := by simpa using hy
  have U : UniqueMDiffAt[(e.extend I).source] y := by
    rw [e.extend_source]
    exact e.open_source.uniqueMDiffWithinAt hy
  have hEq : ((e.extend I).symm ∘ (e.extend I)) =ᶠ[𝓝[(e.extend I).source] y] _root_.id := by
    filter_upwards [e.extend_source_mem_nhdsWithin (I := I) hy] with z hz
    simp only [Function.comp_def, PartialEquiv.left_inv (e.extend I) hz, id_eq]
  rw [← mfderivWithin_eq_mfderiv U (e.mdifferentiableAt_extend he hy),
    ← mfderivWithin_comp y (mdifferentiableWithinAt_extend_symm he ((e.extend I).map_source hy'))
      (e.mdifferentiableAt_extend he hy).mdifferentiableWithinAt
      (fun z hz ↦ e.extend_target_subset_range ((e.extend I).map_source hz)) U,
    hEq.mfderivWithin_eq ((e.extend I).left_inv hy'), mfderivWithin_id U,
    ContinuousLinearMap.comp_id]

/-- The composition of the derivative of an extended chart `e.extend I` with the derivative of its
inverse `(e.extend I).symm` gives the identity.
Version where the basepoint belongs to `(e.extend I).source`. -/
lemma mfderiv_extend_comp_mfderivWithin_extend_symm'
    {y : M} (he : e ∈ maximalAtlas I 1 M) (hy : y ∈ (e.extend I).source) :
    (mfderiv% (e.extend I) y) ∘L
        (TangentSpace.cast I ((e.extend I).left_inv hy)).toContinuousLinearMap ∘L
        (mfderiv[range I] (e.extend I).symm (e.extend I y)) =
      ContinuousLinearMap.id 𝕜 _ := by
  have h := mfderiv_extend_comp_mfderivWithin_extend_symm he ((e.extend I).map_source hy)
  rw [mfderiv_congr_point (f := e.extend I) ((e.extend I).left_inv hy).symm]
  ext v
  have := congr($h v)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at this
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.id_apply, TangentSpace.cast_cast, TangentSpace.cast_rfl, this]

/-- The composition of the derivative of the inverse of an extended chart `e.extend I` with the
derivative of `e.extend I` gives the identity.
Version where the basepoint belongs to `(e.extend I).target`. -/
lemma mfderivWithin_extend_symm_comp_mfderiv_extend
    {y : E} (he : e ∈ maximalAtlas I 1 M) (hy : y ∈ (e.extend I).target) :
    (mfderiv[range I] (e.extend I).symm y) ∘L
        (TangentSpace.cast 𝓘(𝕜, E) ((e.extend I).right_inv hy)).toContinuousLinearMap ∘L
        (mfderiv% (e.extend I) ((e.extend I).symm y)) =
      ContinuousLinearMap.id 𝕜 _ := by
  have h'y : (e.extend I).symm y ∈ e.source := by simp_all
  have h := mfderivWithin_extend_symm_comp_mfderiv_extend' he h'y
  rw [mfderivWithin_congr_point (f := (e.extend I).symm) ((e.extend I).right_inv hy).symm]
  ext v
  have := congr($h v)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at this
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.id_apply, TangentSpace.cast_cast, TangentSpace.cast_rfl, this]

lemma isInvertible_mfderivWithin_extend_symm
    {y : E} (he : e ∈ maximalAtlas I 1 M) (hy : y ∈ (e.extend I).target) :
    (mfderiv[range I] (e.extend I).symm y).IsInvertible := by
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (mfderivWithin_extend_symm_comp_mfderiv_extend he hy) ?_
  ext v
  have := congr($(mfderiv_extend_comp_mfderivWithin_extend_symm he hy) v)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at this
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.id_apply, TangentSpace.cast_cast, TangentSpace.cast_rfl, this]

lemma isInvertible_mfderiv_extend {y : M} (he : e ∈ maximalAtlas I 1 M) (hy : y ∈ e.source) :
    (mfderiv% (e.extend I) y).IsInvertible := by
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (mfderiv_extend_comp_mfderivWithin_extend_symm' he (by simpa using hy)) ?_
  ext v
  have := congr($(mfderivWithin_extend_symm_comp_mfderiv_extend' he hy) v)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at this
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.id_apply, TangentSpace.cast_cast, TangentSpace.cast_rfl, this]

end

section extChartAt

variable [IsManifold I 1 M] {s : Set M} {x y : M} {z : E}

theorem hasMFDerivAt_extChartAt (h : y ∈ (chartAt H x).source) :
    HasMFDerivAt% (extChartAt I x) y
      (((NormedSpace.fromTangentSpace (extChartAt I x y)).symm.toContinuousLinearMap ∘L
        (TangentSpace.equivModel I (chartAt H x y)).toContinuousLinearMap) ∘L
          mfderiv% (chartAt H x) y) :=
  I.hasMFDerivAt.comp y ((mdifferentiable_chart x).mdifferentiableAt h).hasMFDerivAt

theorem hasMFDerivWithinAt_extChartAt (h : y ∈ (chartAt H x).source) :
    HasMFDerivAt[s] (extChartAt I x) y
      (((NormedSpace.fromTangentSpace (extChartAt I x y)).symm.toContinuousLinearMap ∘L
        (TangentSpace.equivModel I (chartAt H x y)).toContinuousLinearMap) ∘L
          mfderiv% (chartAt H x) y) :=
  (hasMFDerivAt_extChartAt h).hasMFDerivWithinAt

theorem mdifferentiableAt_extChartAt (h : y ∈ (chartAt H x).source) :
    MDiffAt (extChartAt I x) y :=
  (hasMFDerivAt_extChartAt h).mdifferentiableAt

theorem mdifferentiableOn_extChartAt : MDiff[(chartAt H x).source] (extChartAt I x) :=
  fun _y hy ↦ (hasMFDerivWithinAt_extChartAt hy).mdifferentiableWithinAt

theorem mdifferentiableWithinAt_extChartAt_symm (h : z ∈ (extChartAt I x).target) :
    MDiffAt[range I] (extChartAt I x).symm z :=
  mdifferentiableWithinAt_extend_symm (IsManifold.chart_mem_maximalAtlas x) h

theorem mdifferentiableOn_extChartAt_symm :
    MDiff[(extChartAt I x).target] (extChartAt I x).symm :=
  mdifferentiableOn_extend_symm (IsManifold.chart_mem_maximalAtlas x)

/-- The composition of the derivative of `extChartAt` with the derivative of the inverse of
`extChartAt` gives the identity, up to the identification of the tangent spaces at `y` and at
`extChartAt I x ((extChartAt I x).symm y)`.
Version where the basepoint belongs to `(extChartAt I x).target`. -/
lemma mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm {x : M}
    {y : E} (hy : y ∈ (extChartAt I x).target) :
    (mfderiv% (extChartAt I x) ((extChartAt I x).symm y)) ∘L
      (mfderiv[range I] (extChartAt I x).symm y) =
      (TangentSpace.cast 𝓘(𝕜, E) ((extChartAt I x).right_inv hy).symm).toContinuousLinearMap :=
  mfderiv_extend_comp_mfderivWithin_extend_symm (IsManifold.chart_mem_maximalAtlas x) hy

/-- The composition of the derivative of `extChartAt` with the derivative of the inverse of
`extChartAt` gives the identity.
Version where the basepoint belongs to `(extChartAt I x).source`. -/
lemma mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' {x : M}
    {y : M} (hy : y ∈ (extChartAt I x).source) :
    (mfderiv% (extChartAt I x) y) ∘L
        (TangentSpace.cast I ((extChartAt I x).left_inv hy)).toContinuousLinearMap ∘L
        (mfderiv[range I] (extChartAt I x).symm (extChartAt I x y)) =
      ContinuousLinearMap.id 𝕜 _ :=
  mfderiv_extend_comp_mfderivWithin_extend_symm' (IsManifold.chart_mem_maximalAtlas x) hy

/-- The composition of the derivative of the inverse of `extChartAt` with the derivative of
`extChartAt` gives the identity.
Version where the basepoint belongs to `(extChartAt I x).target`. -/
lemma mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
    {y : E} (hy : y ∈ (extChartAt I x).target) :
    (mfderiv[range I] (extChartAt I x).symm y) ∘L
        (TangentSpace.cast 𝓘(𝕜, E) ((extChartAt I x).right_inv hy)).toContinuousLinearMap ∘L
        (mfderiv% (extChartAt I x) ((extChartAt I x).symm y)) =
      ContinuousLinearMap.id 𝕜 _ :=
  mfderivWithin_extend_symm_comp_mfderiv_extend (IsManifold.chart_mem_maximalAtlas x) hy

/-- The composition of the derivative of the inverse of `extChartAt` with the derivative of
`extChartAt` gives the identity, up to the identification of the tangent spaces at `y` and at
`(extChartAt I x).symm (extChartAt I x y)`.
Version where the basepoint belongs to `(extChartAt I x).source`. -/
lemma mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    {y : M} (hy : y ∈ (extChartAt I x).source) :
    (mfderiv[range I] (extChartAt I x).symm (extChartAt I x y)) ∘L (mfderiv% (extChartAt I x) y) =
      (TangentSpace.cast I ((extChartAt I x).left_inv hy).symm).toContinuousLinearMap :=
  mfderivWithin_extend_symm_comp_mfderiv_extend' (IsManifold.chart_mem_maximalAtlas x)
    (by simpa using hy)

lemma isInvertible_mfderivWithin_extChartAt_symm {y : E} (hy : y ∈ (extChartAt I x).target) :
    (mfderiv[range I] (extChartAt I x).symm y).IsInvertible :=
  isInvertible_mfderivWithin_extend_symm (IsManifold.chart_mem_maximalAtlas x) hy

lemma isInvertible_mfderiv_extChartAt {y : M} (hy : y ∈ (extChartAt I x).source) :
    (mfderiv% (extChartAt I x) y).IsInvertible :=
  isInvertible_mfderiv_extend (IsManifold.chart_mem_maximalAtlas x) (by simpa using hy)

set_option backward.isDefEq.respectTransparency false in
/-- The trivialization of the tangent bundle at a point is the manifold derivative of the
extended chart, read in `E` through `NormedSpace.fromTangentSpace`. -/
theorem TangentBundle.continuousLinearMapAt_trivializationAt
    {x₀ x : M} (hx : x ∈ (chartAt H x₀).source) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x =
      (NormedSpace.fromTangentSpace (extChartAt I x₀ x)).toContinuousLinearMap ∘L
        mfderiv% (extChartAt I x₀) x := by
  have : MDiffAt (extChartAt I x₀) x := mdifferentiableAt_extChartAt hx
  simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe] at this
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx]
  simp only [mfderiv, this, mfld_simps]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse trivialization of the tangent bundle at a point is the manifold derivative of the
inverse of the extended chart, read from `E` through `NormedSpace.fromTangentSpace`. -/
theorem TangentBundle.symmL_trivializationAt
    {x₀ x : M} (hx : x ∈ (chartAt H x₀).source) :
    (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x =
      (TangentSpace.cast I ((extChartAt I x₀).left_inv (by rwa [extChartAt_source]))
        ).toContinuousLinearMap ∘L
        mfderiv[range I] (extChartAt I x₀).symm (extChartAt I x₀ x) ∘L
        (NormedSpace.fromTangentSpace (extChartAt I x₀ x)).symm.toContinuousLinearMap := by
  have : MDiffAt[range I] ((chartAt H x₀).symm ∘ I.symm) (I (chartAt H x₀ x)) := by
    simpa using mdifferentiableWithinAt_extChartAt_symm (by simp [hx])
  rw [TangentBundle.symmL_trivializationAt_eq_core hx]
  simp only [hx, mfderivWithin, this, mfld_simps]
  rfl

omit [IsManifold I 1 M] in
/-- The `fderivWithin` of the round-trip composition `(extChartAt I x) ∘ (extChartAt I x).symm`
at the chart point in `range I` equals the identity. -/
lemma fderivWithin_extChartAt_comp_extChartAt_symm_range :
    fderivWithin 𝕜 ((extChartAt I x) ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) =
      ContinuousLinearMap.id 𝕜 _ := by
  set φ := extChartAt I x
  have eq_nhd : ((extChartAt I x) ∘ (extChartAt I x).symm) =ᶠ[𝓝[range I] (extChartAt I x x)] id :=
    Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin x)
      (fun _ ↦ (extChartAt I x).right_inv)
  rw [eq_nhd.fderivWithin_eq (by simp)]
  exact fderivWithin_id <| I.uniqueDiffOn.uniqueDiffWithinAt (mem_range_self _)

/-- The manifold derivative of `extChartAt` at the basepoint is `TangentSpace.equivModel`. -/
lemma mfderiv_extChartAt_self :
    mfderiv% (extChartAt I x) x =
      (NormedSpace.fromTangentSpace (extChartAt I x x)).symm.toContinuousLinearMap ∘L
        (TangentSpace.equivModel I x).toContinuousLinearMap := by
  rw [TangentSpace.equivModel_eq_continuousLinearMapAt,
    TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source H x),
    ← ContinuousLinearMap.comp_assoc, ContinuousLinearEquiv.coe_symm_comp_coe,
    ContinuousLinearMap.id_comp]

-- TODO: should there be a version for `extChartAt`?
/-- The manifold derivative within `range I` of `(extChartAt I x).symm` at the chart point is the
inverse of `TangentSpace.equivModel`. -/
lemma mfderivWithin_range_extChartAt_symm :
    mfderiv[range I] (extChartAt I x).symm (extChartAt I x x) =
      (TangentSpace.cast I (extChartAt_to_inv x).symm).toContinuousLinearMap ∘L
        (TangentSpace.equivModel I x).symm.toContinuousLinearMap ∘L
        (NormedSpace.fromTangentSpace (extChartAt I x x)).toContinuousLinearMap := by
  rw [TangentSpace.equivModel_symm_eq_symmL,
    TangentBundle.symmL_trivializationAt (mem_chart_source H x)]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, TangentSpace.cast_cast, TangentSpace.cast_rfl]

/-- The inverse of the derivative of `(extChartAt I x).symm` at the chart point,
applied to a tangent vector, gives back the tangent vector. -/
lemma mfderivWithin_extChartAt_symm_inverse_apply (v : TangentSpace I x) :
    (mfderiv[range I] (extChartAt I x).symm (extChartAt I x x)).inverse
        (TangentSpace.cast I (extChartAt_to_inv x).symm v) =
      (NormedSpace.fromTangentSpace (extChartAt I x x)).symm (TangentSpace.equivModel I x v) := by
  have : mfderiv[range I] (extChartAt I x).symm (extChartAt I x x) =
      ((NormedSpace.fromTangentSpace (extChartAt I x x)).trans
        ((TangentSpace.equivModel I x).symm.trans
          (TangentSpace.cast I (extChartAt_to_inv x).symm))).toContinuousLinearMap := by
    rw [mfderivWithin_range_extChartAt_symm]
    rfl
  rw [this, ContinuousLinearMap.inverse_equiv]
  rfl

end extChartAt
