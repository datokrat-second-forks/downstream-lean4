# OrderDual as a `newtype`

This document records issues from the OrderDual migration on Lean branch `irredalias`.
The starting point is the structure spike at Mathlib commit `3df90ba905`.
The downstream base is `c1a733679b5`.

Validation: `LEAN_NUM_THREADS=2 lake build Mathlib MathlibTest Archive Counterexamples` succeeds
with 9,443 jobs and no warnings or errors. The log is `/tmp/orderdual-newtype-build-12.log`.
`MathlibTest/OrderDual.lean` checks the abstraction boundary, projection inference and reduction,
and unsealing in named theorems and separate proof branches.

## 1. `public section` does not supply the expected visibility

Status: accepted for now. An explicit `public newtype` works.

```lean
module
public meta import Lean.Elab.NewType

@[expose] public section

newtype N (α : Type) := α with val
```

The command reports that `_private.<module>.0.N` is not a definition.
The generated `def` uses the public name, but the command looks for a private name.
The migration currently uses `public newtype OrderDual ...` inside the public section.

## 2. Projection inference differs from a structure

Status: fixed in the active toolchain after the initial report.
Both minimal examples now compile.

The following structure example compiles:

```lean
import Lean

structure S (α : Type) where
  val : α

namespace S
instance [OfNat α 1] : OfNat (S α) 1 := ⟨mk 1⟩
theorem val_inj {a b : S α} : a.val = b.val ↔ a = b :=
  ⟨fun h => congrArg mk h, fun h => congrArg val h⟩
example [OfNat α 1] {a : S α} : a.val = 1 ↔ a = 1 := val_inj (b := 1)
end S
```

Before the fix, replacing the structure declaration with `newtype S (α : Type) := α with val` made the last example fail.
The inferred type retained metavariables for the underlying type and the first argument of `val_inj`.
Both round-trip equalities compiled with `rfl`.

The corresponding Mathlib failures include `OrderDual.ofDual_eq_one` and `OrderDual.ofDual_eq_top`.
Additional failures occur in the regularity proofs in `Algebra/Order/Group/Synonym.lean`.
Those failures involve projection arguments that Lean must infer from equalities of underlying values.

A smaller reproducer isolates the projection inference:

```lean
import Lean

structure S (α : Type) where
  val : α
newtype N (α : Type) := α with val

example (x : α) : ∃ y : S α, y.val = x := ⟨_, rfl⟩ -- succeeds
example (x : α) : ∃ y : N α, y.val = x := ⟨_, rfl⟩ -- failed before the fix
```

Lean could infer the structure value from its field, but could not infer the corresponding `newtype` value.
The explicit witness `⟨N.mk x, rfl⟩` worked.
The injectivity example also compiled with `val_inj (α := α) (a := a) (b := 1)`.

## 3. Local reducibility initially failed in asynchronous theorem proofs

Status: fixed in the active toolchain.

The original `with_reducible_type` tactic modified the declaration extension directly.
Named theorem proofs produced an `asyncDecl` environment-extension panic.
Anonymous examples did not expose this issue.

The replacement tactic, `unsealing_newtype`, uses a local scope for reducibility changes.
This example now compiles with asynchronous elaboration enabled:

```lean
import Lean
newtype N := Nat with val

theorem newtype_eq : N = Nat := by
  unsealing_newtype N => rfl
```

The tactic treats the type, constructor, and projection as semireducible within its block.
The migration uses this spelling and behavior.

## 4. The structure spike is not a complete build baseline

The spike deliberately left `Data/Ordmap/Invariants`, `Order/CompleteLattice/PiLex`, and `Order/Category/BddOrd` broken.
Some statements in these modules rely on equality between a type and its dual.
A `newtype` retains that equality in the kernel.
Local reducibility can preserve many proofs.
Statements that cross the type boundary still need explicit conversions.
For example, `Ordnode.dual_insert` now maps tree values through `OrderDual.toDual`.
All three modules now compile in the migration checkout.

## 5. Much of the old transport code is unnecessary

The spike adds private equivalences for relation series in `Order/KrullDimension.lean`.
Their purpose is to transport series across the structure wrapper.
The migration instead retains the original proofs and uses local reducibility where necessary.
The definition of `Order.coheight` explicitly applies `OrderDual.toDual`.
The complete `Order/KrullDimension.lean` module now compiles with this approach.
The cleanup also removes 81 unused private transport helpers elsewhere in the spike.
Explicit transport remains where typeclass matching needs it.

A further review restores pre-spike proofs in more than 400 additional declarations.
Most need only an `unsealing_newtype OrderDual` block around the original proof.
Some need explicit arguments to select the intended instances.
The review keeps direct proofs that are noticeably simpler.
Of the 81 removed helpers, 35 become unused during this further review.
Examples include inverse bounds, annihilator identities, measure extensionality, and monotone limits.

## 6. Parameter support was a prerequisite

Status: fixed in the active toolchain before this migration.

The first version of `newtype` accepted no explicit parameters.
Section variables also made its generated constructor fail.
The updated command supports parameters, and its virtual reductions account for their arguments.
The parameterized iota and eta examples now compile.

## 7. `rcases` expects an inductive value

Status: difference from the structure spike. The explicit recursor provides a local solution.

The spike destructures a dual sum with `rintro ⟨a | a⟩`.
With `newtype`, `rcases` reports that the dual sum is not an inductive datatype.
The migration first uses `cases x using OrderDual.rec`, then destructures the underlying sum.
The same pattern applies to lexicographic sums.

A later in-memory comparison confirmed this limitation while simplifying `OrderIso.sumDualDistrib`.
The same `rcases` pattern succeeds for an ordinary one-field structure on the current toolchain:

```lean
import Mathlib.Data.Sum.Order

structure Wrapped (α : Type) where
  val : α

example (x : Wrapped (Nat ⊕ Nat)) : True := by
  rcases x with ⟨a | b⟩ <;> trivial

example (x : (Nat ⊕ Nat)ᵒᵈ) : True := by
  rcases x with ⟨a | b⟩ <;> trivial
```

Only the second example fails: `Tactic rcases failed: x : (ℕ ⊕ ℕ)ᵒᵈ is not an inductive datatype`.
In `src/Lean/Elab/Tactic/RCases.lean`, `rcasesCore` reduces the type with `whnfD`, then inspects its constant declaration.
This branch accepts `ConstantInfo.inductInfo` and `ConstantInfo.quotInfo`; it rejects the sealed newtype's definition.
It does not use the newtype's registered cases eliminator.

The existing `sumDualDistrib` proof uses `cases a using OrderDual.rec` before splitting the underlying sum.
That proof avoids this limitation, but the shorter nested pattern needs newtype support in `rcases`.
The comparison changed neither production Lean files nor the compiler.

## 8. Semireducibility does not make typeclass search unfold the type

Status: expected consequence of the chosen transparency level.

The Colex proofs apply Lex theorems with the index type `ιᵒᵈ`.
Inside `unsealing_newtype`, ordinary elaboration can identify the index types.
Typeclass search still cannot reuse an instance of type `∀ i : ι, PartialOrder (β i)` directly.
An explicit local instance supplies the family indexed by `ιᵒᵈ`.
Passing existing instance families explicitly with `‹_›` also works, as in `Pi.Colex.isOrderedCancelMonoid`.
The type stays semireducible, as intended.

In `AddMonoidAlgebra.le_inf_support_coeff_mul`, instance search can find `AddLeftMono Tᵒᵈ` inside unsealing.
However, passing `degtm` directly lets unification infer the original `Add T` for the theorem's addition instance.
The dual monotonicity instance expects `OrderDual.instAdd`, which instance search cannot identify with that original addition.
Before the spike, dual addition was the original addition.
With the wrapper sealed, the distinct types prevent this inference.
Scratch tests confirm that delaying the hypothesis check avoids this inference.
These scratch tests use the default semireducible unsealing.

Rewriting can also need help after unsealing.
In `Ordnode.dual_insert`, simplifying the tree maps leaves an equality with mixed type annotations.
A `change` step presents the unsealed goal in the form used by the original proof.

Topology proofs can also infer incompatible instance arguments.
In `IsCompact.lt_sInf_iff_of_continuous`, passing the original continuity hypothesis selects the original topology `t`.
The registered dual instance uses `TopologicalSpace.coinduced OrderDual.toDual t`.
After unsealing, `rfl` proves that these topologies are equal.
Typeclass matching does not unfold the semireducible maps to identify them.
The proof now unseals and reuses the original dual theorem, with explicit continuity transport.
The argument `continuous_toDual.comp_continuousOn hf` keeps the topology arguments aligned.
The spike's proof also compiles with `newtype`. The failed version was an attempted simplification.

Unsealing does not undo changes to data-valued instances from the spike.
Finite intervals use `Finset.map`, and uniformities use `UniformSpace.comap`.
These constructions need not reduce definitionally to the original data.
The affected interval and Dini proofs therefore retain explicit transport or direct arguments.
This limitation also follows from the structure spike's instance definitions.

## 9. An applied function-valued projection does not reduce

Status: fixed in the active toolchain. The comparison examples now compile.

```lean
import Lean
structure S (α β : Type) where
  fn : α → β
newtype N (α β : Type) := α → β with fn

example {α β : Type} (f : α → β) (x : α) : S.fn (S.mk f) x = f x := rfl
example {α β : Type} (f : α → β) (x : α) : N.fn (N.mk f) x = f x := rfl
```

Before the fix, only the structure example compiled.
The virtual projection rule required exactly the parameters and the wrapped value.
It did not handle the extra argument `x`.
The bug also affected sets, which are functions to `Prop`.
The first Mathlib example was the membership proof in `gciIciSInf`.

The same failure occurred with `OrderDual`; this example also compiles after the fix:

```lean
example {α β : Type} (f : α → β) (x : α) :
    OrderDual.ofDual (OrderDual.toDual f) x = f x := rfl
```

The broader build exposed this issue in `Topology/Order.lean` and `Order/UpperLower/Closure.lean`.
For example, the lifted order on topologies wraps the function `IsOpen` in `OrderDual`.
Applying its unwrapped function to a set did not reduce as it did with a structure.
This broke basic order proofs such as `TopologicalSpace.le_def`.
These failures differed from the intentional restrictions of semireducible unsealing.

## 10. The editor temporarily failed to find the tactic

Status: resolved in the user's editor; the cause is unconfirmed.

The editor reported that `unsealing_newtype` was unavailable in `Data/Ordmap/Invariants.lean`.
An extra `public meta import Mathlib.Order.OrderDual` changed the diagnostics.
The missing-tactic error later disappeared.

A fresh language server recognized the tactic without the extra import.
Command-line checks with `Elab.inServer` both enabled and disabled also recognized it.
Adding the extra import did not change those results.
Stale imported artifacts or cached editor state remain possible causes.

## 11. An unchanged Galois proof reaches the typeclass heartbeat limit

Status: reproduced with both representations; a local heartbeat limit of 40,000 resolves the failure.

`IsGaloisGroup.of_isScalarTower` has the same proof text as the structure spike.
The default limit of 20,000 heartbeats is reached while elaborating `AlgHom.equivFieldRange`.
The failing instance is:

```lean
Algebra K (IsScalarTower.toAlgHom K F L).fieldRange
```

Diagnostics show repeated unfolding of fraction rings and field ranges during algebra instance search.
They do not report `OrderDual` among the used instances or unfolded declarations.
A temporary copy compiles with an 80,000-heartbeat limit.
A second temporary copy compiles at the default limit with this local instance:

```lean
let : Algebra K (IsScalarTower.toAlgHom K F L).fieldRange :=
  IntermediateField.algebra' _
```

The declaration now sets `synthInstance.maxHeartbeats` to 40,000, with a brief comment.
The proof body is unchanged, and the module compiles at this limit.

### Structure comparison on the same toolchain

The isolated comparison is in `/root/downstream/orderdual-structure-check/mathlib4`.
It uses the saved structure port, with the remaining merge errors repaired in its dependencies.
`OrderDual` is a plain one-field structure throughout this build.
All dependencies of the Galois file compile.
The Galois source was byte-for-byte identical to the migration checkout during the comparison.
Both builds use `/root/lean4/irredalias/build/release/stage1/bin/lean`, rebuilt on September 8, 2026.

The structure version reaches the same 20,000-heartbeat limit at the same instance search.
With the temporary limit of 80,000, both versions compile.
Each uses 42,807 heartbeats for the whole theorem command, measured with asynchronous elaboration disabled.
This count includes the whole theorem, whereas the failing limit applies to one instance search.

The failure therefore does not require an actual `newtype` declaration for `OrderDual`.
General overhead from the new elaborator code remains a possible cause.
This comparison does not isolate that code from other toolchain or dependency changes.

The structure build log is `/tmp/orderdual-structure-galois-build-6.log`.
The shared measurement source is `/tmp/OrderDualGaloisHeartbeatComparison.lean`.
Its results are in `/tmp/orderdual-galois-heartbeats-structure.log` and
`/tmp/orderdual-galois-heartbeats-newtype.log`.

## 12. Instance reducibility exposes a stuck exception in offset recognition

Status: diagnosed in scratch files. A smaller reproduction does not require `newtype` or Mathlib.

The new `.instanceReducible` configuration permits instance search to unfold the type, constructor, and projection.
For `le_inf_support_coeff_mul`, instance search now selects the original `Add T` even with the delayed hypothesis.
Thus, both `degtm` and `(by exact degtm)` require matching that addition with the transported addition.
The search finds the dual monotonicity instance, but its matching step throws a stuck exception.

The trace reaches `a =?= OrderDual.instAdd ?a`, where `a` is the original addition instance.
Unfolding and structure eta reduce this comparison to expressions involving `Add.add` and the candidate metavariable `?a`.
The offset recognizer in `Lean.Meta.isDefEqOffset` checks whether this addition is natural-number addition.
Its `matchesInstance` helper compares `?a` with `instAddNat` under `withNewMCtxDepth`, which prevents assignment of `?a`.
Instance search enables `isDefEqStuckEx`, so this speculative check throws a stuck exception instead of declining the offset optimization.
The exception interrupts matching before Lean can assign `?a` to the original addition instance.

With `Meta.Config.offsetCnstrs := false` around the scratch proof, both hypothesis variants compile under `.instanceReducible`.
An explicit application of the dual monotonicity instance also compiles.
These results confirm that the remaining error is not insufficient transparency of the newtype maps.
The delayed hypothesis succeeds under semireducible unsealing because instance search selects the transported addition directly.
That choice avoids the failing comparison.

`/tmp/OrderDualOffsetPlain.lean` reproduces the stuck exception with an ordinary definition that reconstructs an `Add` instance.
This file imports only `Lean` and contains no `OrderDual` or `newtype`.
Disabling offset constraints also makes this smaller example compile.
The full proof comparison is `/tmp/OrderDualDegreeNoOffsets.lean`.
The detailed trace is `/tmp/orderdual-conservative/instance-minimal.log`.
These experiments change neither the production Lean proofs nor the compiler.

## 13. Instance reducibility can select the original order

Status: diagnosed in scratch files. This result follows from the selected transparency level.

The attempted unsealing proof of `DFinsupp.Colex.total_le` applies `DFinsupp.Lex.total_le` with index type `ιᵒᵈ`.
At `.implicitReducible`, direct matching of `LinearOrder ιᵒᵈ` against the local `LinearOrder ι` cannot unfold `OrderDual`.
It selects `OrderDual.instLinearOrder`, which reverses the index order, and the proof succeeds.

At `.instanceReducible`, instance search can reuse the local `LinearOrder ι` for `LinearOrder ιᵒᵈ`.
This local instance takes precedence over the global dual instance.
The resulting Lex theorem uses the original index order, but the Colex goal requires the reversed index order.
Without an explicit family argument, elaboration reports a stuck search for `(i : ιᵒᵈ) → LinearOrder (?α i)`.
With the family `α` explicit, the error shows the incompatible relations directly.

Explicitly supplying `OrderDual.instLinearOrder ι` makes the scratch proof compile at `.instanceReducible`.
The local family of zero instances does not resolve the order mismatch.
This failure is separate from the offset-recognition exception in section 12.
The comparison is in `/tmp/ColexTotalPinnedOrder.lean` and `/tmp/ColexTotalPinnedOrder.log`.
The production proof remains under the user's control.

### Dependent instance families need the assignment transparency bump

The related `letI : (i : ιᵒᵈ) → Zero (α i) := inferInstance` succeeds at `.implicitReducible` but fails at `.semireducible`.
The local instance has type `(i : ι) → Zero (α i)`.
To apply it under the goal's binder `i : ιᵒᵈ`, search creates a metavariable `?m : ιᵒᵈ → ι`.
Matching the result types requires `?m i = i`, so Lean tries assigning `?m := fun i => i`.
Checking this assignment requires comparing `ιᵒᵈ → ι` with `ιᵒᵈ → ιᵒᵈ`.

`Lean.Meta.checkTypesAndAssign` uses `withImplicitConfig` for this check.
The trace records `raising transparency instances → implicit`.
This permits unfolding `OrderDual` at `.implicitReducible`, but not at `.semireducible`.
Thus, instance search can identify the index types during this assignment check even when direct instance matching cannot.
Supplying the local family explicitly succeeds with semireducible unsealing, since ordinary term checking can unfold it.

The comparison and trace are in `/tmp/ColexLetITransparencyTraced.lean` and `/tmp/ColexLetITransparencyTraced.log`.
These experiments make no changes to production proofs or the compiler.

### The pre-spike proof enabled the stronger transparency check

At pre-spike revision `c1a733679b5`, `DFinsupp.Colex.total_le` had `set_option backward.isDefEq.respectTransparency false in` before its declaration.
That option also disables `backward.isDefEq.respectTransparency.types`.
The metavariable assignment's type check then uses `.default` transparency, which can unfold the original semireducible `OrderDual` definition.
Direct matching of the index order still uses instance transparency, so search selects the reversed order.

Restoring the same option in scratch makes semireducible unsealing succeed on the current toolchain.
Both the isolated `inferInstance` family and the original `Lex.total_le (ι := ιᵒᵈ)` proof compile.
The original proof does not need the extra `letI` under this option.
Thus, this comparison changed the transparency option as well as the type declaration; it does not establish a newtype regression.
The successful comparison is `/tmp/ColexPreSpikeTransparency.lean`, with trace in `/tmp/ColexPreSpikeTransparency.log`.

## 14. Unsealing is restricted to proofs

Status: explicit data constructions restored.

Applying `Pi.Lex.linearOrder (ι := ιᵒᵈ)` under unsealing compiles as a definition of `Pi.Colex.linearOrder`.
However, rebuilding its dependents exposed a failure in `Pi.Colex.completeLattice`: Lean reported missing `le_top` and `bot_le` fields.
The reused linear order retained the Lex partial order over dual indices.
Once `OrderDual` was sealed again, instance search could not match that order with the existing Colex bounds instances.
This failure arose from the proposed simplification; it was not observed with the preceding direct construction.

Preserving the Colex `toPartialOrder` field in a structure update resolved that failure.
The scratch comparison is `/tmp/orderdual-apply-verified/ColexOrderParent.lean`.
However, `LinearOrder` contains data, so this approach conflicts with the requirement to restrict unsealing to proofs.
The direct `linearOrderOfSTO` construction is restored.

An audit of all `unsealing_newtype` uses also found two data constructions in `DFinsupp.Colex.decidableLE` and `DFinsupp.Colex.decidableLT`.
Both now use their explicit computable constructions, with the shared `colex_lt_trichotomy_rec` helper restored.
The remaining uses prove propositions, including proof fields within structures and instances whose types are propositions.

The affected PiLex, DFinsupp, Finsupp, and complete-lattice modules build successfully, together with `MathlibTest.OrderDual`.
The 1,005-job build completed without warnings; its log is `/tmp/orderdual-proof-only/build.log`.

A later cleanup removes the duplicate colex recursion without unsealing data.
Both colex decidability instances reuse their lex counterparts under a locally reversed index order.
`LinearOrder.lift' OrderDual.toDual OrderDual.toDual.injective` constructs this order on the original index type.
Thus, the dependent value family needs no transport.

## 15. `inferInstanceAs` loses a local order's defining value

Status: reproduced without using `OrderDual` to reverse the order; direct instance applications compile.

An attempted simplification of `DFinsupp.Colex.decidableLE` used:

```lean
letI := LinearOrder.lift' (OrderDual.toDual : ι → ιᵒᵈ) OrderDual.toDual.injective
inferInstanceAs (DecidableLE (Lex (Π₀ i, α i)))
```

The local order makes the lex and colex relations definitionally equal.
However, `inferInstanceAs` generates an auxiliary definition whose body abstracts this order as an arbitrary `LinearOrder ι` parameter.
Its expected type still uses the original colex relation.
The parameter no longer retains the value that establishes the equality, so the kernel rejects the auxiliary definition.
The less-than instance fails in the same way.

`Lean.Meta.wrapInstance` calls `mkAuxDefinition` without its `zetaDelta` flag, which defaults to `false`.
The definitions are in `src/Lean/Meta/WrapInstance.lean` and `src/Lean/Meta/Closure.lean` in `/root/lean4/irredalias`.
The reported auxiliary types show the local order becoming a parameter.

Replacing the local order construction with `linearOrderOfSTO (fun x y : ι => y < x)` gives the same kernel error.
Thus, this failure does not require using the newtype to construct the reversed order.
The comparison is `/tmp/orderdual-last-four/df_nodual.lean`, with errors in `/tmp/orderdual-last-four/df_nodual.log`.
It does not establish a regression against the one-field structure representation.

The final instances use `Lex.decidableLE` and `Lex.decidableLT` directly under the local order.
Both compile without an auxiliary wrapper or unsealing.
No compiler changes were made.

# UniformOnFun as a `newtype`

This section records the migration of `UniformOnFun` (the type alias `α →ᵤ[𝔖] β`) to a `newtype`,
on top of the `OrderDual` migration above. `UniformFun` (`α →ᵤ β`) stays a plain definition.
The raw projection is `UniformOnFun.toFun'`; the existing equivalences `UniformOnFun.ofFun 𝔖` and
`UniformOnFun.toFun 𝔖` keep their names and remain the public interface.
`MathlibTest/UniformOnFun.lean` checks the abstraction boundary, projection inference and reduction,
that different families `𝔖`, `𝔗` give different types, and unsealing in named theorems and
separate proof branches.

## 16. Statements that were only well-typed by definitional unfolding

Status: fixed by restating. These are the clearest gains of sealing the type.

Each of the following compiled before only because `α →ᵤ[𝔖] β`, `α →ᵤ[𝔗] β`, and `α → β` were
the same type after unfolding. The `newtype` rejects them as type errors.

- `UniformOnFun.uniformContinuous_ofFun_toFun` and its two corollaries stated the map as
  `ofFun 𝔗 ∘ toFun 𝔖` but ascribed it the type `(α →ᵤ[𝔗] β) → α →ᵤ[𝔖] β`. The composite goes the
  other way. The docstring and all callers meant `ofFun 𝔖 ∘ toFun 𝔗`; the statement now says so.
- `UniformOnFun.mono` compared `𝒱(α, γ, 𝔖₁, u₁) ≤ 𝒱(α, γ, 𝔖₂, u₂)`, an inequality between uniform
  structures on two different types. It is now monotonicity in `u` alone, mirroring
  `UniformFun.mono`. Monotonicity in `𝔖` is the uniform continuity of the identity map, which
  `uniformContinuous_ofFun_toFun_of_subset` already stated.
- `UniformOnFun.comap_eq` used `(f ∘ ·)` as a map `(α →ᵤ[𝔖] γ) → (α →ᵤ[𝔖] β)`; it now transports
  through `ofFun 𝔖 ∘ (f ∘ ·) ∘ toFun 𝔖`, the form the neighbouring lemmas already used. Two
  trailing `rfl` steps in callers became unnecessary.
- `UniformOnFun.hasBasis_nhds_one` and `UniformOnFun.toFun_prod` applied an element of
  `α →ᵤ[𝔖] G` to a point, or `toFun 𝔖` to a plain function.
- `UniformOnFun.congrRight`, `congrLeft`, and `uniformEquivPiComm` reused equivalences between
  plain function types as equivalences between the aliases. They now conjugate by `toFun`/`ofFun`,
  as `uniformEquivProdArrow` already did.
- `range_toUniformOnFunIsCompact` asked for `Continuous f` with `f` in the alias.

## 17. Algebraic instances were `rfl`-lemmas by instance identity

Status: fixed following `Algebra/Order/Group/Synonym.lean`.

The `inferInstanceAs` instances on `α →ᵤ[𝔖] β` become explicit constructors through
`ofFun`/`toFun`, and the structure instances use `Function.Injective.monoid` and friends. All
`toFun_mul`-style lemmas stay `rfl` because projection-of-constructor reduces.
`ofFun_prod`/`toFun_prod` were `rfl` only because both sides used the identical `Finset.prod`; they
are now `map_prod` of the obvious `MulEquiv`.

## 18. Downstream statements that quantified over the alias as functions

Status: fixed by inserting `toFun`/`ofFun`; a few proofs needed one extra step.

- `eVariationOn.lowerSemicontinuous` and `lowerSemicontinuous_uniformOn` applied `eVariationOn` to
  an element of `α →ᵤ[𝔖] M`, and passed `id` as the family `ι → α → M` with `ι` the alias.
- `UniformOnFun.continuousSMul_submodule_of_image_bounded` took images `u '' s` with `u` in the
  alias, and coerced `LinearMap.id.domRestrict H` to `H →ₗ[𝕜] α → E`.
- `MultipliableUniformlyOn.exists` and `HasProdUniformlyOn.multipliableUniformlyOn` exchanged an
  existential over `β → α` with one over `β →ᵤ[{s}] α`.
- `UniformConvergenceCLM.instTopologicalSpace` induced along `DFunLike.coe` typed as a map into
  `E →ᵤ[𝔖] F`; `topologicalSpace_eq` already stated the honest `ofFun 𝔖 ∘ DFunLike.coe`, so the
  instance now agrees with its own characterisation lemma.
- `EquicontinuousOn.comap_uniformOnFun_eq` comapped the `𝔖`-uniformity along `F : ι → X → α`.
- Injectivity side goals (`isUniformEmbedding_toUniformOnFunIsCompact`, `isUniformEmbedding_coeFn`,
  `postcomp_isUniformEmbedding`, `t2Space_of_covering`) needed `(ofFun 𝔖).injective` or
  `(toFun 𝔖).injective` composed in, where before `DFunLike.coe_injective` or `funext` sufficed.
- `range (ofFun 𝔖 ∘ F)` is `ofFun 𝔖 '' range F` and no longer `range F`; proofs that fed such a
  membership into a closedness argument (`isClosed_range_pi_of_uniformOnFun'`,
  `UniformConvergenceCLM.completeSpace`) rewrite with `range_comp` and
  `(ofFun 𝔖).injective.mem_set_image`, as `isClosed_range_uniformOnFun_iff_pi` already did.

## 19. Rewriting the family `𝔖` no longer works, because it is a type parameter

Status: fixed by a small new definition.

Two proofs of `isUniformEmbedding_restrictScalars` (for `E →SL[σ] F` and for multilinear maps)
used `convert! isUniformEmbedding_toUniformOnFun using 4` and then closed the goal
`{s | IsVonNBounded 𝕜 s} = {s | IsVonNBounded 𝕜' s}` by `Set.ext`. The uniform structure on the
alias was the same term, so `convert` only had to match the parameter `𝔖`. Once `α →ᵤ[𝔖] β` and
`α →ᵤ[𝔗] β` are distinct types, an equality `𝔖 = 𝔗` cannot be rewritten in the *type* of a
uniform embedding, and `convert` produces heterogeneous goals about instances that it cannot close.

The honest replacement is `UniformOnFun.uniformEquivOfEq (h : 𝔖 = 𝔗) : (α →ᵤ[𝔖] β) ≃ᵤ (α →ᵤ[𝔗] β)`,
whose two directions are `uniformContinuous_ofFun_toFun_of_subset` with `h.ge` and `h.le`. Both
proofs are now `(uniformEquivOfEq h𝔖).isUniformEmbedding.comp isUniformEmbedding_toUniformOnFun`.
This is the same pattern as `OrderDual`: a property that was transported by `rw`/`convert` becomes
an explicit equivalence.

## 20. An ill-typed instance took the elaborator down with it

Status: toolchain robustness issue, not specific to `newtype`; recorded because the migration is
how one runs into it. Not reduced to a minimal example.

While `UniformConvergenceCLM.instTopologicalSpace` still had the pre-migration body (inducing along
`DFunLike.coe` typed as a map into `E →ᵤ[𝔖] F`), it failed with the expected type mismatch, and
Lean recovered with an error term. The two instances built on top of it then failed in a way that
does not point at the actual mistake:

```
error: UniformConvergenceCLM.lean:135:9: (kernel) declaration has metavariables
  'UniformConvergenceCLM.instUniformSpace'
error: UniformConvergenceCLM.lean:146:6: Unknown constant `_inhabitedExprDummy`
info: UniformConvergenceCLM.lean:142:0: PANIC at Lean.MetavarContext.getDecl
  Lean.MetavarContext:507:17: unknown metavariable _uniq.29375
```

A recovered instance body should not leak a metavariable to the kernel, and the later declaration
should not panic. Fixing the first error (`ofFun 𝔖 ∘ DFunLike.coe`, the form the file's own
`topologicalSpace_eq` lemma already used) made all three messages disappear.

## 21. Small API and environment friction

Status: worked around.

- After `rw [range_comp]` on `range (ofFun 𝔖 ∘ f)`, the lemma that turns `ofFun 𝔖 '' s` into a
  preimage under `toFun 𝔖` is `Equiv.image_eq_preimage_symm`; the name `Equiv.image_eq_preimage`
  one reaches for first does not exist. With it, `UniformConvergenceCLM.completeSpace` reduces to
  `ContinuousLinearMap.range_coeFn_eq` as before.
- `UniformOnFun.toFun_prod` had to change its binder from `{f : ι → α → β}` to
  `{f : ι → α →ᵤ[𝔖] β}`; the old statement was only about plain functions on both sides.
- The wide downstream rebuild could not be completed on this machine (16 GiB, shared with several
  other sessions holding about 5 GiB). The `lowprio` watchdog killed every attempt (exit 137) at
  startup, at 250k to 935k refaults/s: once the page cache has been evicted by an earlier kill,
  a Lean process importing most of Mathlib re-reads about 2.1 GiB of `.olean`s at disk speed,
  which the refault heuristic cannot distinguish from thrash. Raising the group ceiling from 50%
  to 70%, reducing `LEAN_NUM_THREADS`, reclaiming the group's stale cache, and pre-warming the
  oleans below the watchdog rate all failed to get past startup. `lake build` here has no `-j`
  flag. The change is therefore verified on the eleven touched files, the new test, and the
  direct dependents listed above, not on all of Mathlib.

## 22. Six `respectTransparency` overrides became unnecessary

Status: removed. This is the measurable side of the improvement.

The adaptation branch had switched off `backward.isDefEq.respectTransparency` in front of
declarations whose proofs only worked by unfolding the alias. With the `newtype`, the following no
longer need it, because the statements now say what the proofs use:

- `UniformOnFun.hasBasis_uniformity_of_basis_aux₁`, `UniformOnFun.uniformEquivProdArrow`,
  `UniformOnFun.uniformEquivPiComm` in `UniformConvergenceTopology.lean`;
- `eVariationOn.lowerSemicontinuous_uniformOn` in `BoundedVariation.lean`;
- both `isUniformEmbedding_restrictScalars` (via `uniformEquivOfEq`, item 19).

For the three in `UniformConvergenceTopology.lean`, removing them from the pre-migration file was
checked to fail; the other three guarded proofs that passed `id` or `convert!` through the alias,
which the new proofs no longer do. The overrides that remain
in these files are about `UniformFun` (still a plain definition), about `UniformSpace.comap`
through `DFunLike.coe`, or about `UniformOnFun.comap_eq`, whose proof rewrites under
`UniformSpace.comap` with `UniformFun.comap_eq` and still needs the alias unfolded there.

# PiLp as a one-field structure

This section records the migration of `PiLp p α` from `abbrev PiLp p α := WithLp p (∀ i, α i)`
to its own one-field structure `structure PiLp (p) (α : ι → Type*) where toLp (p) :: ofLp : ∀ i, α i`,
shaped exactly like `WithLp`. The transport API (`PiLp.equiv`, `PiLp.addEquiv`,
`PiLp.linearEquiv`, the `toLp_*`/`ofLp_*` lemmas and the algebraic instances) is a copy of the
`WithLp` one specialised to Pi types. The `WithLp` type and instances are unchanged;
its documentation now directs users of dependent products to `PiLp`.

## 23. Statements that spelled out the abbreviation

Status: fixed by restating.

- `PiLp.sumPiLpEquivProdLpPiLp` was stated between `WithLp p (Π i, α i)` and
  `WithLp p (WithLp p (Π i, α (.inl i)) × WithLp p (Π i, α (.inr i)))`; it is now between
  `PiLp p α` and `WithLp p (PiLp p (fun i => α (.inl i)) × PiLp p (fun i => α (.inr i)))`.
- `Matrix.toLpLin` and its lemmas (`Analysis/Normed/Lp/Matrix.lean`) used `WithLp p (n → R)`
  throughout for what the docstring calls "`PiLp R _`".
- The `!₂[x, y, …]` macro and its delaborator in `PiL2.lean` produced and matched
  `WithLp.toLp 2 ![…]`, so the notation silently stopped applying to `EuclideanSpace` elements.
- The measurable-space structure of `PiLp` came for free from `WithLp.measurableSpace`;
  `PiLp.measurableSpace`, `PiLp.measurable_ofLp/toLp` and `MeasurableEquiv.toPiLp` are new, and
  `PiLp.borelSpace` now unfolds its own instance.

## 24. `toLp`/`ofLp` are overloaded between `WithLp` and `PiLp`

Status: worked around per file.

Files that only deal with `PiLp`/`EuclideanSpace` had `open WithLp` for `toLp`, `ofLp` and
their lemmas; they now need `open PiLp` instead (`LpEquiv.lean`, `PiL2.lean`, …). A file using
both (`sumPiLpEquivProdLpPiLp`, `EuclideanSpace.sumEquivProd`) must qualify one side. With both
namespaces open, an unqualified `toLp p x` elaborates by overload resolution on the expected
type, but `rw [toLp_add]`/`simp [ofLp_add]` are ambiguous.

## 25. A `by exact` that stopped seeing through `LinearIsometryEquiv.symm`

Status: worked around with `change`.

`DirectSum.IsInternal.isometryL2OfOrthogonalFamily_symm_apply` closed with
`exact this (e₁.symm w)`, relying on `(hV.isometryL2OfOrthogonalFamily hV').symm w` unfolding to
`e₂ (e₁.symm (ofLp w))` (with `respectTransparency false`). After replacing
`WithLp.linearEquiv 2 𝕜 (Π i, V i)` by the identically-shaped `PiLp.linearEquiv 2 𝕜 fun i => V i`
in the definition, `exact` reports a type mismatch, while `change e₂ (e₁.symm (ofLp w)) = _`
followed by the same `exact` succeeds. Not reduced to a minimal example.

## 26. Mixed product and Pi APIs need different conversions

Status: conversions made explicit at the affected sites.

Characteristic functions and Gaussian laws have both product and dependent-product versions.
The product versions still use `WithLp.toLp` and `MeasurableEquiv.toLp`.
The dependent-product versions now use `PiLp.toLp` and `MeasurableEquiv.toPiLp`.
Changing the open namespace for a whole mixed-use file would select the wrong conversion.
The proofs still use the same integral and measure transport lemmas.

The Euclidean mixed space of a number field has the same distinction:
its outer product uses `WithLp`, and its real and complex coordinate spaces use `PiLp`.
Its ring instances and linear equivalence now name these respective transports.

## 27. The vector delaborator depends on the constructor's arity

Status: fixed and covered by `MathlibTest/EuclideanSpace.lean`.

`WithLp.toLp` has three arguments: `p`, the underlying type, and the value.
`PiLp.toLp` has four: `p`, the index type, the dependent family, and the function.
Changing only the delaborator registration leaves `!₂[...]` printing broken.
The delaborator now uses `withOverApp 4` and reads the function with `withNaryArg 3`.
The tests check empty vectors, numeric and variable subscripts, and a shadowed subscript variable.
They also check dependent projection inference and the norm of `!₂[3, 4]`.

The default printer also hides the index type in constant families:
`PiLp 2 fun x => ℕ` does not tell the reader the dimension.
`PiLp.delabPiLp` enables `pp.funBinderTypes` at the family argument, using the same
per-position option mechanism as `delabLinearIndependent`.
The displayed type of `!₂[1, 2, 3]` therefore includes `Fin 3`.

## 28. Existing transparency overrides still matter

Status: retained after checking their removal.

Removing the overrides from `iSup_edist_ne_top_aux`, `norm_eq_of_L1`, and `edist_eq_of_L1`
still makes their existing proofs fail on this toolchain.
The first fails at `mod_cast`; the other two report that `simp` made no progress.
Removing the override from `isometryL2OfOrthogonalFamily_symm_apply` leaves a goal about
the direct-sum linear map after simplification.
Thus, this migration does not by itself eliminate these four overrides.

## 29. Transport finite generation without strengthening assumptions

Status: the new instance preserves the generality of `WithLp.instModuleFinite`.

The initial `PiLp.instModuleFinite` required a finite index type and finite generation of each factor.
The existing transport only needs finite generation of the underlying function space.
The instance now takes `[Module.Finite K (∀ i, α i)]` directly.
Finite products still obtain this through the usual Pi instance.
A regression test checks transport with no `[Finite ι]` assumption.

## PiLp validation

`lowprio schedule pilp-complete env LEAN_NUM_THREADS=2 lake build Mathlib MathlibTest Archive Counterexamples`
followed by `lowprio waitfor pilp-complete` completed successfully: 9,444 jobs, no warnings or errors.
The log is `/var/log/lowprio/pilp-complete.log`.
This includes `MathlibTest.ImportAll` and the updated Euclidean-space tests.
An earlier pass lost `ImportAll` to a watchdog kill (exit 137); the final pass needed no change
to the memory cap or watchdog settings.
