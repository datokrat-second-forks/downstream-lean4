# One-field structures downstream experiment

This downstream branch tests the changes that Batteries, Mathlib, and their dependencies need for the `/root/lean4/onefieldstructures` toolchain.
The result must provide credible evidence about the effect on downstream projects.
The aim is to avoid substantial deterioration and identify improvements where possible.
Repairs must usually follow the design of the original declarations on the green branch that forms this checkout's base.
Use sustainable repairs that preserve the intended abstractions. Avoid ad hoc workarounds.
Preserve downstream type definitions such as `def X := Nat`. Do not convert downstream definitions to `newtype` declarations.
The scope is the fallout from abstraction changes in the toolchain.

## Work sequence

1. Record this task in `TASK.md`.
2. Read the toolchain changes relative to `origin/downstream-green`. Ignore the generated `stage0` changes.
3. Fix Mathlib's dependencies.
4. Start the Mathlib port with repairs for a few errors.

## Decision records and evidence

Record each nontrivial repair decision in a Markdown file under `/root/static/ofs-ddr/`.
Use one DDR per substantive decision, not one per user task or work batch.
Identify who decided: the user, the assistant, or both, with their respective contributions.
Reuse an existing DDR when a repair applies the same decision.
Keep batch progress, module lists, and verification summaries in `/root/static/ofs-ddr/progress/`, with raw evidence in `evidence/`.
Each future progress report must include the number of directly failing Mathlib modules and transitively blocked Mathlib modules.
Use `/root/documentation/scripts/blocked.py` with `MATHLIB_ROOT=/root/downstream/ofs/mathlib4` and the directly failing module names.
Record the failure list, total module count, source build log, and whether the scan completed or used `--fail-fast`.
For a current full-build statistic, use a scheduled build without `--fail-fast`; retain `--fail-fast` for first-error discovery.
Label incomplete scans as observations, not complete failure counts.
The script's `outside failure set` output means outside the supplied failure set and its transitive dependents; it does not verify successful compilation.
Do not count fail-fast import cancellations as direct failures.
Explain the original intent, the cause of the error, the alternatives, and the selected repair.
Verify the repairs with the requested toolchain and record the results.
Distinguish completed dependency builds and selected Mathlib repairs from a complete Mathlib build.

## Initial batch outcome

The toolchain findings are in `TOOLCHAIN_CHANGES.md`.
Decision records and durable build logs are in `/root/static/ofs-ddr/`.
All eight dependency package targets and their available test libraries passed.
Seven initial Mathlib files received repairs.
The selected Mathlib build and two existing linter test modules passed.
The complete Mathlib build and performance comparisons remain open.

## Next batch and execution requirements

Fix ten additional failing Mathlib modules and verify each repaired module.
Run every Lean invocation through `lowprio`, as required by `/root/.claude/CLAUDE.md`.
For builds, use `lowprio schedule --preemptable TASKNAME lake build ...`, then `lowprio waitfor TASKNAME`.
Always specify the task name when waiting. Use `--fail-fast` when only the first error is needed.
Use `lowprio lake env lean ...` for direct Lean invocations.

When the Equiv conflict arises, remove Mathlib's duplicate definition and reuse the upstream core definition.
For representation-only collection conversions, avoid an elementwise map.
Prefer a proof-based cast when the types are propositionally equal, with an equivalence-to-map theorem if useful.
For actual newtypes, `unsealing_newtype` can establish the required representation equality.
Verify the type declaration first: the current toolchain declares `ModuleIdx` as a real structure.
Record nontrivial decisions with short explanatory examples in `/root/static/ofs-ddr/`.
Record unexpected toolchain differences as anomaly records under `/root/static/ofs-ddr/anomalies/`.
An anomaly record does not replace a DDR when its repair involves a substantive choice.
Keep observed behavior and diagnostic evidence in the anomaly, and link to the decision, alternatives, and rationale in a DDR.
Include a small example, observed behavior, toolchain revision, and links to the relevant DDR and evidence.

## Ten-module batch outcome

Ten additional Mathlib modules now compile, including `Mathlib.Logic.Equiv.Defs`.
The existing cross-reference and location tests pass, together with a new core-Equiv regression test.
The final scheduled build passes 137 Lake jobs.
The batch 02 progress report lists repairs and verification. DDRs 006–007 record runner and Equiv decisions.
Anomaly records describe the changed Equiv API and operation transparency.
The toolchain source remains unchanged, and no downstream type definition became a newtype.

## Authorized core Equiv follow-up

Align the newly upstreamed core Equiv API with Mathlib, as authorized by the user.
Match the original operation reducibility and upstream pointwise `Equiv.ext`.
Align the composition and cancellation theorem names, then simplify the downstream repair.
Record the decision in DDR 008 and update the anomaly resolutions after verification.

The authorized core follow-up is complete and verified; see DDR 008.
The original Mathlib theorem names, constructor simp registrations, and proof automation are restored.
The full toolchain build and all 14 selected core tests pass.
A clean downstream rebuild passes 807 jobs, followed by 50 jobs for ImportGraph tests.
The verified toolchain edits are committed as `9d16753d84f66efca4be5105db45086669b60723` and preserved as a patch in the verification evidence.
The full Mathlib build and performance comparison remain open.

## Further ten-module batch

Ten more directly failing Mathlib modules now compile; see the batch 03 progress report for the list and DDR 009 for the nonemptiness decision.
The final scheduled build passes 217 jobs, including five existing tactic test modules.
This batch changes ten source files, with 34 inserted lines and 9 removed lines.
The toolchain remains unchanged at `9d16753d84f66efca4be5105db45086669b60723`.
The repairs preserve downstream type definitions and the existing algorithms.
The complete Mathlib build and performance comparison remain open.

DDR 009 now selects `deriving Nonempty` on `CongrResult`, following the user’s suggestion.
The private exception witness was removed; the revised module and unchanged tests pass (78 jobs).

## Ongoing work

Continue as a long-running task until the user asks to stop. Ten-module batches are reporting checkpoints, not a stopping condition.

Batch 04 repairs 22 further Mathlib modules and passes a 580-job selected build.
Full scans report 17 direct failures and 7,875 blocked modules before repairs, then 22 direct failures and 7,610 blocked modules afterward.
Both snapshots contain 8,526 modules and use the corrected header parser in the preserved `blocked.py`.
See `/root/static/ofs-ddr/progress/mathlib-batch-04.md` for evidence and limits.

Batch 05 repairs 27 more source modules and passes 713 selected jobs, including traversal and `itauto` tests.
The full scan reports 22 direct failures and 7,195 blocked modules out of 8,526.
See `/root/static/ofs-ddr/progress/mathlib-batch-05.md`.

## Resumed work

The user released the DDR 011 discussion pause and requested continued work.
Apply explicit constructor-based unitors to the two traversal proofs, then resume the Mathlib port.
The four instance-identity lemmas retain their HEq statements pending a separate API decision.
Batch 06 repairs all 22 previous direct failures and applies the verified unitor proofs.
Its completed full scan reports 20 direct failures and 6,831 blocked modules out of 8,526.
See `/root/static/ofs-ddr/progress/mathlib-batch-06.md`.

Batch 07 repairs the next 20 direct failures and passes the existing abel, ring, and field_simp tests.
Its completed full scan reports 14 direct failures and 6,557 blocked modules out of 8,526.
See `/root/static/ofs-ddr/progress/mathlib-batch-07.md`.

Batch 08 repairs all 14 baseline failures and passes 1,119 selected Lake jobs.
The completed full scan reports 24 direct failures and 6,103 blocked modules.
See `/root/static/ofs-ddr/progress/mathlib-batch-08.md`.

Batch 09 repairs all 24 baseline failures. Its completed full scan reports 14 direct failures and 5,477 blocked modules.
See `/root/static/ofs-ddr/progress/mathlib-batch-09.md`.

Batch 10 repairs 38 source modules and passes the existing matrix/determinant and slim_check tests (1,681 jobs).
The completed full scan reports 44 direct failures and 4,177 blocked modules.
See `/root/static/ofs-ddr/progress/mathlib-batch-10.md`.

Batch 11 repairs all 44 baseline failures and passes 2,258 selected jobs with five tactic test modules.
Its completed full scan reports 30 direct failures and 3,405 blocked modules out of 8,526.
Toolchain commit `4013a0b4ba` lifts StateRefT computation inhabitants; the extra DDR 014 result witnesses are removed.
See `/root/static/ofs-ddr/progress/mathlib-batch-11.md`.

Batch 12 repairs all 30 baseline failures with inverse proofs and passes 2,454 selected jobs.
Its completed full scan reports 40 direct failures and 1,926 blocked modules out of 8,526.
See `/root/static/ofs-ddr/progress/mathlib-batch-12.md`.

Batch 13 repairs all 40 baseline failures and passes 3,210 selected jobs.
Its completed full scan reports 20 direct failures and 1,273 blocked modules out of 8,526.
See `/root/static/ofs-ddr/progress/mathlib-batch-13.md`.

Batch 14 repairs all 20 baseline failures and passes 3,434 selected jobs.
Its completed full scan reports 13 direct failures and 438 blocked modules out of 8,526.
See `/root/static/ofs-ddr/progress/mathlib-batch-14.md`.

Batch 15 repairs all 13 baseline failures and passes 3,755 selected jobs.
Its completed full scan reports 9 direct failures and 79 blocked modules out of 8,526.
The pullback naturality proof now uses 2,239 heartbeats on this toolchain; see anomaly 014.
See `/root/static/ofs-ddr/progress/mathlib-batch-15.md`.

Batch 16 repairs all 9 baseline failures and passes 3,556 selected jobs.
Its completed full scan reports 3 direct failures and 9 blocked modules out of 8,526.
See `/root/static/ofs-ddr/progress/mathlib-batch-16.md`.

Batch 17 repairs the remaining 3 baseline failures. The full `lake build Mathlib` now passes all 8,920 jobs.
The completed scan reports zero direct failures and zero blocked modules out of 8,526.
The full `MathlibTest` target, accumulated-change review, and performance comparison remain open.
See `/root/static/ofs-ddr/progress/mathlib-batch-17.md`.
