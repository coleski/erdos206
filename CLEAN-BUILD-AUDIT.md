# Independent clean rebuild audit — Erdős #206 explicit-example supplement

Date: 2026-09-12. Auditor: independent combinatorics subagent. Result: PASS.

The exact final theorem `ExplicitEgyptian.erdos206_explicit_resolution` and its actual supporting source modules rebuilt successfully from source in a newly created directory. The complete successful output is `build-clean.log`. This is a clean rebuild audit of the supplied proof, not a claim of an independent mathematical proof or a novelty determination.

## Freshness and trusted components

Audit directory: `/tmp/erdos206-clean-audit-fluyNL` (created with `mktemp -d`). Copied exactly eight `.lean` source files from the frozen candidate directory. No candidate `.olean`, `.ilean`, generated C, Lake build directory, or dependency directory was copied. The eight source hashes matched the frozen originals after the copy. An additional `AuditFinal.lean` imports the exact final module and only prints statements, definitions, and axiom dependencies; it introduces no replacement theorem.

The new `lakefile.toml` declares the Git dependency

    https://github.com/leanprover-community/mathlib4.git
    db584cd6d46c92f209a44c0f1c829460d327499d

`lake update` cloned fresh dependency source checkouts. Mathlib's HEAD was verified as the exact pinned commit, and `git status --short` in that checkout was empty. The generated `lake-manifest.json` records the exact transitive dependency revisions as well.

Trusted precompiled components were limited to:

- The installed Lean 4.33.0 release toolchain, including its standard library. Reported version: `Lean (version 4.33.0, arm64-apple-darwin24.6.0, commit d8b18978322de05a8f3dba51ef03cf5461676c17, Release)`.
- The external Mathlib/dependency cache selected by the pinned Mathlib cache program. Its output was: `Using cache from origin: (some leanprover-community/mathlib4)`, `Decompressing 8689 already-cached file(s) (1 already decompressed)`, `No files to download`, `Decompressed 8689 already-cached file(s)`, and `Completed successfully in 19148 ms!`. These cache archives were in the user's standard `.cache/mathlib` directory; they were not compiled artifacts from the candidate proof directory.

Thus this is a clean rebuild of ALL project proofs against explicitly trusted Lean/Mathlib release caches, not a full bootstrap of Lean and Mathlib from source. No project-proof cache was reused.

## Commands and recovery

Authored the pinned `lean-toolchain`, `lakefile.toml`, and print-only `AuditFinal.lean` with apply_patch. Copied the eight frozen Lean source files with explicit source filenames.

Commands, run from the fresh audit directory:

    lake update
    lake env lean --version
    git -C .lake/packages/mathlib rev-parse HEAD
    git -C .lake/packages/mathlib status --short
    env -u LEAN_PATH lake build Erdos206Audit

The first build attempt revealed a Lake configuration error: the initial library roots named only the final modules, so Lake did not know the independent `StageRecurrence` module. It failed before compiling any project theorem. The full failure is retained in `build-attempt1.log`. The audit manifest was corrected to list all eight project modules plus `AuditFinal`; NO Lean proof source was edited. The repeated build then succeeded with exit code0 and `Build completed successfully (8715 jobs).`

The explicit `env -u LEAN_PATH` prevents any inherited search path from resolving candidate `.olean` files. The initial environment also had no LEAN_PATH set.

Every project module has a fresh `Built` entry in the successful log: NestedIntervals, PriorErdos206, Density, RationalOptimizer, LocalObstruction, StepBounds, StageRecurrence, Erdos206Explicit, and the print-only AuditFinal. Executable checks were also rerun, returning `{4, 5}` for the two-term optimizer example and `125` for the step-index example.

## Exact final result checked

The final printed theorem asserts

    1/4 < ExplicitEgyptian.explicitNumber
    and ExplicitEgyptian.explicitNumber < 1/2
    and Irrational ExplicitEgyptian.explicitNumber
    and not Erdos206.EgyptianFractions.EventuallyGreedy ExplicitEgyptian.explicitNumber
    and for every n : Nat,
      |ExplicitEgyptian.explicitNumber - (ExplicitEgyptian.approximate n : Real)|
        <= (1/2)^n / 2.

The printed number is exactly `ExplicitEgyptian.nestedData.limit`. The printed approximation function is exactly the rational midpoint of `ExplicitEgyptian.state (n+1)`; it is a `def`, not a noncomputable choice of an approximant.

The final combined theorem, `explicit_example`, `approximate_error`, `explicitNumber_not_eventuallyGreedy`, and `explicitNumber_irrational` each report precisely

    [propext, Classical.choice, Quot.sound]

No `sorryAx` or custom axiom appears. A source scan across all eight copied modules and AuditFinal for whole-word `sorry`, whole-word `axiom`, `native_decide`, `unsafe`, `implemented_by`, and `extern` returned no matches. The kernel axiom reports are the decisive dependency check; the textual scan is supplementary.

## Frozen source SHA-256 values

    b2bed9fde71d4f4db51f6e2c79ea1ce8c2174ac51d99093aa345ea7460ec56f5  PriorErdos206.lean
    2b502182cc12109e48bc45978bf2cec558e8b52a1c335630d213db3f31c2ff80  RationalOptimizer.lean
    6efa856c3da651327b5d62eac90c406de2c5fcf6a30680f49ee741eaec7636ee  Density.lean
    ab552cbf23c6cca8107fdd0bb81f75546ed917f7d348b7a3bafceecd41d3447c  LocalObstruction.lean
    fe565576ee3f224c0d5c2e24f631899fd405172859c4355b9d904a0bac008a35  StepBounds.lean
    1dba70ff2f9e9019c4ebcf274d83a8a8259231e9e954942a8a432ce7e10a4700  NestedIntervals.lean
    a6b65ca80ff1f0c15486c596615a6f33e4acc09001afe7c590ed23c4733ce7a9  StageRecurrence.lean
    a02eb9801ff3f6efacb84cefc37be5761dea6b8cacdbcf167375d8b89e91b810  Erdos206Explicit.lean

Audit-only inputs:

    f46b968c53275ac6e6b4a9121915d3be748112d7af577bba238b0907cdc2e860  AuditFinal.lean
    723bce7e6495ae01d890df0811893d58d7844c9780798af4dd9198f61a8638b2  lakefile.toml
    71f8dcfe83219f73ceaa1b83aff8abaeed25c42cb320236cfb478e4271603ec3  lake-manifest.json
    302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  lean-toolchain

## Scope limitation

The build certifies the supplied theorem about the exact constructed number and original imported eventual-greediness predicate. It does not establish historical novelty or decide whether every reader uses “explicit example” to include a fully specified computable recurrence with a certified modulus. Those are separate source/meaning audits. It does not claim a new resolution of Kovač's already-proved almost-everywhere result.
