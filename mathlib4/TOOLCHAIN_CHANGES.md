# Toolchain changes for the downstream port

## Scope and revisions

The toolchain repository is `/root/lean4/onefieldstructures`.
The reviewed base is `origin/downstream-green`, at `53d83477fb548cde0bc848538b03ce6bc6cc7aaf`.
The current toolchain commit is `a9cc981af4958ffbc5a0033ee7dc954fa8fb67a2`.
Generated changes under `stage0/` are outside this review.

The downstream repository root is `/root/downstream/ofs`.
Its initial commit is `37c5c33a37b`, and its current branch name is `ofs`.
The existing `lean-toolchain` selects `/root/lean4/onefieldstructures/build/release/stage1`.
Mathlib's `.lake/package-overrides.json` already selects the sibling dependency checkouts.
There is no need to replace the dependency manifests with local paths.

## Two different abstraction changes

The downstream port must preserve existing downstream type definitions.
The user explicitly excluded conversions of downstream definitions to `newtype` declarations.
Only the fallout from toolchain changes is in scope.

Many former type aliases now use real structures with one field.
Examples include `NameMap`, `NameSet`, `ModuleIdx`, and environment extension wrappers.
Their constructors and projections replace implicit conversion to the underlying representation.

Other former aliases now use the new `newtype` command.
Examples include `Id`, `StateT`, `ReaderT`, `ExceptT`, `OptionT`, `EStateM`, `ST`, `EST`, `BaseIO`, and `EIO`.
The commit history also includes `Parsec`, `MonadCacheT`, asynchronous monads, Lake monads, and `Std.Time` units.
These latter families need further API inspection if downstream errors involve them.

## How `newtype` works

The implementation is in `src/Lean/Elab/NewType.lean`.
A declaration such as `newtype N := A with val` generates `N.mk`, `N.val`, and `N.equiv`.
The type, constructor, and projector are ordinary definitions marked irreducible.
The constructor and projector are identity functions with `always_inline` attributes.
Their bodies inherit the exposure of the type declaration.

`VirtualStructureInfo` registers the type, constructor, projector, and parameter count.
See `src/Lean/Meta/VirtualStructure.lean`.
The elaborator recognizes constructor/projector cancellation and eta equality without unfolding the sealed definitions.
For example, `N.val (N.mk a)` reduces to `a`, and `N.mk (N.val x)` compares equal to `x`.
See `src/Lean/Meta/ExprDefEq.lean` for the virtual eta and projector unification rules.

These are not inductive structures.
Ordinary structure literal notation and direct function application do not automatically cross their abstraction boundaries.
The public `.mk` and projector operations express those boundaries.
The source design intends to preserve the underlying runtime representation.
This review does not establish downstream performance equivalence.

## Monads and pure computations

`Id α` no longer elaborates as `α`.
An `Id.run do` block needs `return value` where the original code ended with a bare pure value.
This also applies to pure early-exit branches.
A pure callback supplied to an `Id` traversal needs `pure` or `return`.
The traversal result needs `Id.run` when the caller expects a pure value.

`StateT.mk` wraps a state function, and `StateT.run` applies an action to its initial state.
`StateT.run` on `StateM` returns `Id (α × σ)`.
Thus `(action.run state).run` returns the pair, and `(action.run' state).run` returns the value.
A projection such as `(action.run state).1` no longer works.

`ReaderT` similarly requires `.mk` around environment functions and `.run` for execution.
`ExceptT` and `OptionT` require `.mk` and `.run` around their underlying monadic results.
`EStateM` requires `.mk` and `.run` around state functions.
Core implementations retain the same operations and add these explicit boundaries.
See `src/Init/Control/{Id,State,Reader,Except,Option,EState}.lean` and `src/Init/Prelude.lean`.

The `do` elaborator explicitly constructs and runs its internal transformers.
See `src/Lean/Elab/Do/{Basic,Control}.lean`.
The branch also adapts partial-definition handling for sealed monads.
Consequently, an ordinary monadic implementation can often retain its existing `do` structure.

## Instance transport

`N.equiv` is reducible, macro-inlined, and registered with `@[transport]`.
`inferInstanceAs` can transport an instance when definitional equality fails.
`deriving` for a sealed definition also uses transport.
See `src/Lean/Elab/BuiltinTerm.lean`, `src/Lean/Elab/Deriving/Basic.lean`, and `src/Lean/Meta/Transport.lean`.

`src/Init/Transport.lean` registers congruences for core classes.
These include orders, decidable equality, inhabited values, arithmetic operations, printing, and several monadic classes.
A lawful congruence applies to the transported parent instance specifically.
Transport does not imply that every downstream class already has a suitable congruence.
The initial dependency build reports failures in Batteries' lawful monad and lawful lift instances.
These require inspection of the actual parent instances before a repair decision.

## Cases and induction

The branch extends `cases` and `induction` to handle indices through definitional bijections.
These bijections include real one-field structures and registered virtual structures.
`induction` can reparametrize a goal through constructor/projector chains to obtain variable indices.
It also transports dependent local declarations and elimination information.
See `src/Lean/Elab/Tactic/Induction.lean` and the one-field structure metaprogramming support.
The implementation rejects multiple induction targets that depend on the same underlying variable.
Some simplification during reparametrization uses syntactic matching.

The signatures of `evalInductionCore` and `evalCasesCore` now require `mkInitInfo : TacticM Info`.
Downstream callers of these internal APIs need to preserve the initial tactic information.

`unsealing_newtype` temporarily changes reducibility for a type and its generated constructor and projector.
See `src/Lean/Elab/Tactic/NewType.lean`.
This is an available escape hatch, not the default repair for ordinary abstraction-boundary errors.

## Collections and environment APIs

`src/Lean/Data/NameMap/Basic.lean` defines these real structures:

| Type | Underlying field |
| --- | --- |
| `NameMap α` | `toTreeMap` |
| `NameSet` | `toTreeSet` |
| `NameSSet` | `toSSet` |
| `NameHashSet` | `toHashSet` |

`NameMap` exposes insertion, erasure, lookup, traversal, conversion, filtering, and merging operations.
It does not expose `insertMany` at this revision.
`NameSet` exposes insertion, erasure, membership, traversal, conversions, merging, and unions.
It does not expose `min!` at this revision.
The initial downstream errors identify callers of both missing operations.
A repair must distinguish a missing wrapper API from a caller that intentionally accesses the underlying collection.

`ModuleIdx` is a structure with `toNat`, not a synonym for `Nat`.
It derives `BEq`, `Hashable`, and `Inhabited`.
An array index from `idxOf?` needs construction as a `ModuleIdx`.
A `DecidableEq Nat` instance cannot directly serve as `DecidableEq ModuleIdx`.
See `src/Lean/Environment.lean`.

`SimplePersistentEnvExtension` extends `PersistentEnvExtension`.
`TagDeclarationExtension` extends `SimplePersistentEnvExtension`.
An API that needs the parent extension requires the corresponding parent projection.
See `src/Lean/EnvExtension.lean`.

`Lean.Environment.evalConstCheck` now returns `Except String α`, rather than `ExceptT String Id α`.
This deliberately describes its pure exception result directly.

## Initial build evidence and next work

The command below ran from the Mathlib directory:

```sh
lake build batteries Qq aesop proofwidgets importGraph LeanSearchClient plausible Cli
```

The initial log is `/tmp/ofs-dependencies.log`.
The pre-existing `mathlib4/mylog` remains unchanged.
The dependency build failed with direct errors across Batteries, Qq, Aesop, ProofWidgets, ImportGraph, Plausible, and Cli.
Many errors involve missing `return`, explicit transformer execution, or wrapper construction.
Additional errors involve lawful instances, missing collection APIs, and the now-duplicate `EStateM.ext` declaration.
Qq reports `Id.const` because missing `return` changes expected-type inference for `.const`.

No downstream repairs were complete when this initial record was written.
The full Mathlib build remains outside the completion claim for this first repair batch.
Nontrivial repair choices belong in `/root/static/ofs-ddr/`.
This file records toolchain facts and will accumulate further findings during the port.

## Further findings from dependency repairs

`MonadCacheT` is sealed with projector `toStateRefT`.
Its `run` starts with an empty cache and returns only the result.
A downstream runner that accepts an initial cache or returns the final cache must run `x.toStateRefT` explicitly.
See `src/Lean/Util/MonadCache.lean` and ImportGraph's existing `StanceM` runners.

`StateRefT'.run` accepts an initial state value and creates its reference.
`ReaderT.run` applies the existing reference directly.
This distinction matters in Aesop's simplifier callback, which already has the reference.
Replacing direct function application with field notation `.run` can select the wrong runner.

Core supplies `EStateM.ext` in `src/Init/Control/Lawful/Instances.lean`.
Batteries can remove its duplicate declaration.
The toolchain also wraps `OptionDecls` and `Lsp.TextEditBatch`.
Callers must use the named collection type or construct the batch explicitly.

`DecidableEq.congr` already carries `@[transport]` in `src/Init/Transport.lean`.
The definition-deriving handler uses transport for sealed definitions with registered equivalences.
Real structures such as `ModuleIdx` also support ordinary structural `deriving DecidableEq`.
No `ModuleIdx` representation equivalence is registered at this revision.

After the initial repair batch, all eight dependency package targets passed (476 jobs).
The successful log is `/tmp/ofs-dependencies-8.log`.
Dependency test libraries and selected Mathlib targets are the next verification steps.

## Verified stopping point for the initial batch

All eight dependency package targets now pass.
The Batteries, Qq, Aesop, Cli, Plausible, ImportGraph, LeanSearchClient, and ProofWidgets test libraries also pass.
ImportGraph's tests require the ImportGraph working directory because they read relative fixture paths.

The selected Mathlib targets pass:

```sh
lake build Mathlib.Init Mathlib.Control.Basic Mathlib.Lean.Expr.Basic Mathlib.Tactic.Basic
lake build MathlibTest.Linter.Whitespace MathlibTest.DirectoryDependencyLinter.Test
```

The repairs cover seven Mathlib files, chiefly early metaprogramming utilities and linters.
The complete Mathlib port remains open.
Durable logs, commands, and repair counts are in `/root/static/ofs-ddr/README.md` and its `evidence/` directory.
No downstream type definition changed to a `newtype` declaration.

## Findings from the next ten Mathlib modules

Core's `Equiv` is defined in `src/Init/Prelude.lean`.
Its operations and theorems are in `src/Init/Data/Function.lean`.
Mathlib now reuses this structure and removes its duplicate notation and basic operations.
The upstreamed API has three further differences:

- `Equiv.ext` takes two function equalities, rather than pointwise equality of the forward maps.
- `Equiv.symm_trans` is a cancellation theorem, rather than inversion of a composition.
- `refl`, `symm`, and `trans` are abbreviations, which changes simplifier and grind matching.

The core structure also omits Mathlib's default inverse proofs.
Affected constructors now provide those proofs explicitly.
The downstream pointwise theorem is `Equiv.ext_apply`; inversion of composition is `Equiv.symm_trans_eq`.
The constructor lemmas `coe_fn_mk` and `symm_mk` remain explicit rewrite lemmas but no longer have global simp attributes.
The former otherwise cycles with `invFun_as_coe`; the latter prematurely exposes composition constructors.
DDR 007 records this integration and its compatibility limits.
Minimal examples and evidence are under `/root/static/ofs-ddr/anomalies/`.
The toolchain source remains unchanged.

For metaprogramming, `SimpM.run` is not interchangeable with running the raw reader/state stack.
It performs extra setup and tracks statistics.
The translation helper retains its original raw-runner behavior through explicit `ReaderT.run` calls.
The discrimination-tree initializer likewise keeps its existing mutable references and cache reuse.
`ExceptT.run` and `OptionT.run` expose their result values before downstream code inspects them.

All ten additional repaired modules and three selected tests pass in a scheduled `lowprio` build (137 jobs).
See `/root/static/ofs-ddr/progress/mathlib-batch-02.md` and `evidence/ten-final.log` for the module list, command, and direct failure evidence.
The full Mathlib build and performance comparison remain open.

## Current core Equiv alignment (supersedes the previous integration notes)

The user authorized changes to the toolchain's newly upstreamed Equiv API.
`src/Init/Data/Function.lean` now matches Mathlib's original operation reducibility:
`refl` and `trans` are ordinary definitions; `symm` has `implicit_reducible`.
All three are exposed across module boundaries, as Mathlib's originals were.

Core's unprotected `Equiv.ext` now takes pointwise equality of the forward maps.
Core's `Equiv.symm_trans` now states inversion of composition.
Cancellation uses `Equiv.self_trans_symm` and `Equiv.symm_trans_self`.
`Init.Transport` uses the new cancellation names in its inverse-law proofs.

Mathlib removes the duplicate declarations and attaches its original attributes to the core declarations.
The temporary theorem renames and removed constructor simp registrations are no longer needed.
Registering `toFun_as_coe` with `grind norm` aligns core's projection with Mathlib's coercion before matching.
The original proof automation works without higher search limits.
Explicit inverse proofs remain necessary because the core structure has no default inverse proofs.

The toolchain build and all 14 selected core tests pass.
A clean downstream build passes all eight dependency targets, their available tests, and the selected Mathlib modules and tests.
The main build has 807 Lake jobs; ImportGraph tests pass separately with 50 jobs.
`lake clean` and `--no-cache` prevent reuse of artifacts from before the uncommitted toolchain changes.
Lake otherwise retains the same toolchain identity because the Git commit has not changed.

DDR 008 records the final decision and verification.
The anomaly records retain the original failures and their resolutions.
The exact tested core patch and source checksums are preserved under `/root/static/ofs-ddr/evidence/`.
No stage0 source was manually edited, and no downstream type definition became a newtype.

The verified core changes are now committed as `9d16753d84f66efca4be5105db45086669b60723`.
The toolchain working tree is clean. The downstream repairs remain uncommitted.
The tests ran on the exact source contents before the commit; no source changed during the commit.

## Further Mathlib findings: cache nonemptiness and reader contexts

The partial-definition elaborator cannot infer nonemptiness of `TermCongr.M α` through the sealed `MonadCacheT` boundary.
Deriving `Nonempty` for `CongrResult` resolves the obligation.
Core already lifts `Nonempty α` to `Nonempty (m α)` for any monad.
This replaces the earlier private exception witness and does not change the executable tactic.
See DDR 009 and anomaly 004 for the diagnostic and verified repair.

Function-property discrimination-tree lookup already returns a `MetaM` action.
Calling it directly avoids a redundant manual application of the current reader context.
Its `.run` field would instead select `MetaM.run`, which returns a separate state value.

`MkBindingM` and the internal binding monad use different reader contexts.
The `wlog` adapter now uses `.mk` for the outer reader and `.run` for the inner reader.
This follows core's `MetavarContext.revert` pattern and preserves the quotation context and state.

`NameSet.min?` is not forwarded by the wrapper; use `toTreeSet.min?` to retain the underlying ordering.
Product and sum equivalence constructors need explicit inverse proofs where Mathlib formerly used default fields.
Core's `Equiv.ext` can expose projections earlier, making an intermediate `simp only` step unnecessary before `rfl`.

The ten additional repaired modules and five existing tactic test modules pass (217 Lake jobs).
No toolchain changes or test-assertion changes were needed for this batch.

## Further findings: representation equivalences and identity composition

Generated `ReaderT.equiv` and `StateT.equiv` point from the representation to the sealed type.
Mathlib had helpers with those names for lifting arbitrary equivalences between two representations.
The helpers are now `equivCongr`, implemented by composing the generated representation equivalences.
DDR 010 and anomaly 005 describe the ownership conflict.

Sealing `Id` makes identity-composition instance types different during ordinary elaboration.
The four identity-instance lemmas were initially changed to `HEq`; they are now replaced by explicit unitors.
`Comp.leftUnitor` and `Comp.rightUnitor`, with their inverse maps, preserve `map`, `pure`, and `<*>`.
The two traversal-law consumers use the bundled inverse unitors, naturality, and injectivity.
These APIs keep `Id` sealed and need no casts or heterogeneous equality.
DDR 011 and anomaly 006 record the migration.

`Traversable Id` needs to convert `m β` into `m (Id β)`.
Mapping `Id.mk` could add runtime work, so its implementation uses a proof-based cast instead.
`Id.traverse_eq_map` proves agreement with the mapping formulation for lawful applicatives.
Generated C contains only an application of the supplied function and a return.
See DDR 013 and `evidence/id-traverse-generated.c` for this local code-generation evidence.

`Equiv.ext` exposes `.toFun` in some goals. A `simp only` proof must explicitly include `toFun_as_coe` when subsequent rules use coercions.
A global simp registration cannot affect a `simp only` list.
Core's `Equiv` still has no default inverse proofs; it is declared in `Init.Prelude`, before `autoParam` in `Init.Tactics`.
Downstream constructors currently supply the omitted proofs explicitly.

Three continuation-law proofs now finish at simplification, before their old `ext; rfl` suffixes.
Anomaly 007 records this proof simplification and the unused constructor/projection rewrite rules.

## StateRefT computation inhabitants

Toolchain commit `4013a0b4ba7c5ded41e71560c67adf0fdfd0c993` adds an `Inhabited (StateRefT' ω σ m α)` instance from `Inhabited (m α)`.
Instance lookup did not retrieve ReaderT's instance through the StateRefT alias.
Before ReaderT was sealed, partial elaboration could recover a witness by unfolding the function stack.
The explicit lifting instance restores this capability without requiring an inhabitant of `α`.
The full core build, a regression test with result type `Empty`, and existing ring and field_simp tests pass.
See DDR 014 and anomaly 012 in `/root/static/ofs-ddr/`.

## Equiv.trans and downstream proof inference

Core `Equiv.trans` uses `e₂.toFun ∘ e₁.toFun` for its forward map.
The former Mathlib definition used `e₂ ∘ e₁`, through Mathlib's function coercion.
These bodies are definitionally equal, but they affect proof automation differently.

In pullback naturality, the raw projection changes which occurrence a rewrite selects.
The selected repair inserts `Equiv.toFun_as_coe` after cancellation; see anomaly 014 and DDR 015.

In Ext exactness, the decisive composition occurs inside Yoneda's shift-sequence instance.
A checked local clone with the old coercion-based forward map restores bare `apply` in both affected proofs.
The raw forward map fails, regardless of which inverse-map form the clone uses.
With coercions, structural comparison infers the category from matching `ShiftedHom.opEquiv` arguments.
With raw projections, further unfolding gets stuck on `HasDerivedCategory ?C` before that successful assignment.
Specifying `(C := C)` avoids this path; fixing only universe parameters does not.
The earlier diagnostic about the unexposed Mathlib definition `Shrink` did not identify the cause.

See `/root/static/ofs-ddr/anomalies/013-ext-theorem-argument-inference.md` for the controlled comparison and traces.
The self-checking probe is `/root/static/ofs-ddr/evidence/ext-trans-inference-regression.lean`.
These results isolate definition changes on the current compiler, not changes in the unification algorithm itself.

A Mathlib-free reduction is now in `/root/lean4/onefieldstructures/src/Demo/CoercionCompositionInference.lean`.
It checks successful wrapped-function inference, failed raw-projection inference, and repair by an explicit parameter.
The further reduction removes all coercion machinery; explicit evaluation records retain the relevant class-projection behavior.
Its trace reproduces the stuck typeclass dependency using only operations on natural numbers.


## Rebased canonical equivalences and Mathlib integration

The rebased toolchain is `bf4b35c7e0e349f6bdcf277a6d7ea487daae4d65`.
Core uses `Lean.CanonicalEquivalence` and generated `.equivDef` declarations, without global equivalence notation.
Mathlib again owns its original `Equiv`, notation, constructor defaults, and coercion-based operations.
`Lean.CanonicalEquivalence.toEquiv` explicitly converts generated representation equivalences for the control library.
The mathematical helpers regain their original names `ReaderT.equiv` and `StateT.equiv`.
See DDR 018 for the conversion decision and its tests.

The actual rebased history retains `b525d6acc2`, the former Mathlib-alignment commit under renamed core declarations.
It also contains the StateRefT inhabitance fix as `72f640304d`.
Some transport congruences use `canonicalCongr`; others still use `congr`.
These are observations of the supplied toolchain. This downstream integration does not alter it.
The separation lets Mathlib use its own API independently of those core choices.


## Removal of retained canonical-equivalence alignment

The rebase retained the old alignment as `b525d6acc2`.
Current-toolchain commit `48b5962a10c978ec2f98c64b69d768c88f5aa570` removes its unnecessary API effects.
`Lean.CanonicalEquivalence.refl`, `symm`, and `trans` are abbreviations again.
Extensionality takes equality of both maps. The cancellation names are `trans_symm` and `symm_trans`.
Production transport proofs use those names, and the redundant Mathlib-alignment test is removed.
The mixed transport-congruence names and the StateRefT instance are unchanged.
DDR 017 records this completed cleanup on the rebased branch.


## Current toolchain (phase 6)

The toolchain is `5529b7abe6` on `onefieldstructures-changes`.
Core has no root `Equiv`, so the earlier `toFun_as_coe` normalization repairs (DDR 015, anomaly 014) are gone.
278 Mathlib files are restored from the green base `37c5c33a37b`.
The sections above on core Equiv alignment (DDRs 008, 012, 015; anomalies 001, 002, 013) are superseded by DDRs 017 and 018.
New core API used downstream:
- `NameMap.find?` replaces the deprecated `get?`, and `NameSet.union` replaces `append`/`merge`.
- `NameMap.insertMany`, `toArray` and `ofArray`.
- `FormatWithInfos` keys are `SubExpr.Pos`.
- `ModuleIdx` derives `DecidableEq`.
See `/root/static/ofs-ddr/progress/phase6-current-toolchain.md` for the package results and the open items.
