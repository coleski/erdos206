# Explicit-example supplement to Erdős #206

The construction specifies a computable irrational real number in (1/4,1/2) whose best strict underapproximations by distinct unit fractions are not eventually compatible. It addresses the explicitly posed request for an individual counterexample, not the main almost-everywhere question already solved by Kovač.

Status: complete local proof package. Two fresh-source builds passed, the final theorem reports only standard axioms, and two independent implementation-to-statement reviews passed. See [VERIFICATION.md](VERIFICATION.md) for evidence and the precise scope of this claim.

## Read the proof

- [PROOF.md](PROOF.md) gives the complete deterministic recurrence and a self-contained mathematical proof.
- [TARGET.md](TARGET.md) records the selected original supplement and exact convention.
- [SOURCE-NOVELTY-AUDIT.md](SOURCE-NOVELTY-AUDIT.md) records the primary-source, Jig, and GitHub checks and their limits. No prior explicit construction was found; no exhaustive worldwide novelty or public acceptance is claimed.

An arithmetic recurrence with a proved convergence modulus is the sense of explicit construction used here. This is not a closed-form named constant or a practical runtime claim. The sources impose no more restrictive format; that correspondence was separately audited.

## Check the proof

From this directory, with Elan installed:

```sh
lake update
lake exe cache get
lake build
lake env lean Erdos206Explicit.lean
```

Lean is pinned to 4.33.0. Mathlib is pinned to commit db584cd6d46c92f209a44c0f1c829460d327499d (v4.33.0). The bundled lake-manifest.json also pins transitive dependencies.

The exact final theorem is `ExplicitEgyptian.erdos206_explicit_resolution` in Erdos206Explicit.lean. It states that the specifically defined `explicitNumber` is between 1/4 and 1/2, irrational, not eventually greedy, and is approximated by the executable rational function `approximate n` with error at most 2^(-n-1).

The final `#print axioms` must report only `propext`, `Classical.choice`, and `Quot.sound`. The construction's rational/natural data functions are ordinary computable definitions; only the real limit uses a noncomputable supremum. Its relationship to the executable approximations is proved, not assumed.

## Files and provenance

RationalOptimizer.lean certifies finite exact optimization; Density.lean provides the level cutoff; LocalObstruction.lean and StepBounds.lean certify the bad intervals; NestedIntervals.lean certifies the limit and irrationality; StageRecurrence.lean instantiates all of them with the concrete recurrence; Erdos206Explicit.lean packages the complete conclusion.

PriorErdos206.lean is vendored unchanged from [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos206.lean), accessed 2026-09-12. It credits Vjekoslav Kovač for the informal mathematics and Matteo Del Vecchio / Aristotle for the formalization, under Apache 2.0. The original upstream gist is recorded in its header. The new proof reuses its definitions, elementary best-approximation lemmas and competitor argument. It does not treat its known measure-zero theorem as a new result.

The bad two-term arithmetic is due to [Kovač](https://arxiv.org/abs/2406.07218). The contribution here is its effective nested-interval use to specify one individual irrational, together with exact executable optimization and a checked full bridge to the original eventual-greediness property. External mathematical/public review has not been obtained.

Publication links are recorded here after submission. Publication does not itself constitute external mathematical review or remote-verifier acceptance.

- GitHub: https://github.com/coleski/erdos206
