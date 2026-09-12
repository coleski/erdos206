# Completion and verification record

Date: 2026-09-12. Result: complete local resolution of the selected **explicit-example supplement to Erdős #206**, with "explicit" meaning the fully specified executable rational recurrence and certified convergence modulus in PROOF.md. At the time this verification record was finalized, no public submission or external acceptance had occurred. No claim is made to newly solve the already resolved main measure question or to provide a closed form.

## Exact conclusion

`ExplicitEgyptian.erdos206_explicit_resolution` is a closed theorem with no mathematical hypotheses. For the particular `explicitNumber` defined by the actual recurrence it proves:

- 1/4 < explicitNumber < 1/2;
- Irrational explicitNumber;
- not EventuallyGreedy explicitNumber, using the existing strict, distinct-positive-denominator definition;
- for every natural n, the executable rational `approximate n` differs from that same number by at most 2^(-n-1).

The theorem is in Erdos206Explicit.lean. StageRecurrence.lean supplies the entire bridge from the concrete optimizer and interval update to the original negative property. No uninstantiated interval hypothesis or structural lemma remains. IndependentMeaningAudit.lean additionally checks the expanded every-sequence/every-threshold statement and existence of optimal sums at every length, ruling out undefined-max or positivity vacuity.

## Actual builds inspected

1. Working-directory source compilation of the exact final module succeeded, printing the full theorem and its axiom report.
2. An independent agent created a new clean directory, copied only the eight frozen source modules, fetched fresh pinned dependency source checkouts, and ran `env -u LEAN_PATH lake build Erdos206Audit`. All eight modules and its print-only wrapper rebuilt successfully, exit 0, 8715 jobs. Root read the complete successful log and report. See CLEAN-BUILD-AUDIT.md and build-clean.log. A first Lake-roots wiring failure, corrected without any proof edit, is transparently retained in build-attempt1.log.
3. Root independently assembled this deliverable directory using source files only, with no local `.olean`, `.ilean`, or `.lake` copied. `lake update` fetched fresh pinned dependency sources. `env -u LEAN_PATH lake build` succeeded with exit 0 and 8715 jobs, freshly building all eight proof modules plus IndependentMeaningAudit. Root inspected the actual final theorem and all printed audit results in that output.

The final result in BOTH fresh builds was:

```text
'ExplicitEgyptian.erdos206_explicit_resolution' depends on axioms:
[propext, Classical.choice, Quot.sound]
Build completed successfully (8715 jobs).
```

No `sorryAx`, custom unproved axiom, unresolved placeholder, or unchecked computational inference occurs in the final theorem's transitive dependencies. The two small `#eval` outputs in supporting files are sanity checks only; their results are not used as proof premises. Global optimizer correctness and all interval facts have ordinary checked proofs.

## Pinned and trusted external components

- Lean 4.33.0 release, commit d8b18978322de05a8f3dba51ef03cf5461676c17, arm64-apple-darwin24.6.0.
- Mathlib 4.33.0, exact commit db584cd6d46c92f209a44c0f1c829460d327499d.
- Exact transitive revisions in the bundled lake-manifest.json (SHA-256 dd1065890d7aa8ae50e280228846c0fb2e80ca074b1ba35033223cbde5a10479).

Both clean builds trusted the installed Lean release/standard library and the official Mathlib cache mechanism's 8689 previously downloaded, hash-selected dependency archives. Neither reused compiled PROJECT proofs. This is not a bootstrap of the Lean compiler or all Mathlib source. The distinction is explicit and applies to the reproducibility claim.

Build commands from this directory are in README.md. Running them rechecks the actual final theorem, not a smaller substitute.

## Independent correspondence checks

INDEPENDENT-MEANING-AUDIT.md and IMPLEMENTATION-MEANING-AUDIT.md record separate reviews of the actual recurrence, exact source definition, ordering of quantifiers, deterministic first-max tie convention, irrationality, and computability. Reviewers disclose the supporting modules they authored; their review of the root-authored final construction and target bridge was independent of its author. Both found no meaning defect.

The source-meaning review inspected the original Erdős–Graham printed p.31, Kovač's precise definition and proof, and subsequent papers. It found no source requirement for a closed form or efficient running time. The recurrence is therefore a concrete answer under the stated constructive interpretation, not merely a new existence lemma. External community agreement has not been obtained and is not a prerequisite claimed by these local checks.

The mathematical content of the audited PROOF.md has not changed after review; its candidate-status header and scope wording were updated only after the successful clean builds. The historical audits retain their audit-time hashes and pending-build descriptions for transparency.

## Frozen proof-source identities

```text
b2bed9fde71d4f4db51f6e2c79ea1ce8c2174ac51d99093aa345ea7460ec56f5  PriorErdos206.lean
2b502182cc12109e48bc45978bf2cec558e8b52a1c335630d213db3f31c2ff80  RationalOptimizer.lean
6efa856c3da651327b5d62eac90c406de2c5fcf6a30680f49ee741eaec7636ee  Density.lean
ab552cbf23c6cca8107fdd0bb81f75546ed917f7d348b7a3bafceecd41d3447c  LocalObstruction.lean
fe565576ee3f224c0d5c2e24f631899fd405172859c4355b9d904a0bac008a35  StepBounds.lean
1dba70ff2f9e9019c4ebcf274d83a8a8259231e9e954942a8a432ce7e10a4700  NestedIntervals.lean
a6b65ca80ff1f0c15486c596615a6f33e4acc09001afe7c590ed23c4733ce7a9  StageRecurrence.lean
a02eb9801ff3f6efacb84cefc37be5761dea6b8cacdbcf167375d8b89e91b810  Erdos206Explicit.lean
52d61dbc8671f5d54c09d3b077cf865e51fa99ffe36cb709024e787cadd008b4  IndependentMeaningAudit.lean
```

## Prior work and novelty limits

Kovač's bad two-term construction and the Del Vecchio/Aristotle formalization are credited in the source and manuscript. The main almost-everywhere theorem and Kovač–Tang's rational theorem are already known and are not claimed as new. The identified addition is the individual deterministic computable witness, with complete proof of its failure of eventual greediness.

The current problem page explicitly lists the example request as open. The documented current primary-paper, forum, Jig, and GitHub checks found no equivalent explicit construction. These are substantive prior-art checks, not a guarantee against all unpublished or unindexed work. SOURCE-NOVELTY-AUDIT.md states the coverage limits.

No initial decimal expansion or practical runtime is claimed. Even the first stage uses an 11-term exact optimizer. Termination and the precision guarantee are proved; efficiency is not needed for the selected constructive question.
