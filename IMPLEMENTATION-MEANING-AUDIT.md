# Implementation-to-statement audit

Auditor: Codex subagent `/root/new_misc_sep12`.
Date: 2026-09-12.
This is an attributed agent review, not a cryptographic signature or an assertion of human/community acceptance.

## Outcome

No mathematical meaning mismatch, weakened target, hidden choice of the witness, or alternate-optimal-representation loophole was found in the implementation listed below. The executable rational recurrence agrees with PROOF.md. The public approximation bound in the manuscript now agrees with `approximate_error`.

The root agent reported a clean final compilation of StageRecurrence.lean and standard-axiom output. A second agent's clean-directory rebuild was still in progress when this audit was written. This audit does not substitute for that rebuild, and the manuscript remains marked candidate until the final gate is cleared.

For transparency, this auditor authored Density.lean and PROOF.md. The review of the optimizer, step arithmetic, local obstruction, recurrence assembly and generic nested-interval module is independent of their authors; the two self-authored files are not being represented as independently authored and independently reviewed by this same agent.

## Files read and identity

Read the complete current source of StageRecurrence.lean, RationalOptimizer.lean, StepBounds.lean, LocalObstruction.lean and NestedIntervals.lean. Read the relevant exact definitions, namespace, monotonicity and gap-bound statements in PriorErdos206.lean; its full earlier formalization was not re-proved by this auditor. The published Kovač proof was read separately in full during the source audit.

SHA-256 digests at audit time:

```text
a6b65ca80ff1f0c15486c596615a6f33e4acc09001afe7c590ed23c4733ce7a9  StageRecurrence.lean
2b502182cc12109e48bc45978bf2cec558e8b52a1c335630d213db3f31c2ff80  RationalOptimizer.lean
6efa856c3da651327b5d62eac90c406de2c5fcf6a30680f49ee741eaec7636ee  Density.lean
fe565576ee3f224c0d5c2e24f631899fd405172859c4355b9d904a0bac008a35  StepBounds.lean
ab552cbf23c6cca8107fdd0bb81f75546ed917f7d348b7a3bafceecd41d3447c  LocalObstruction.lean
1dba70ff2f9e9019c4ebcf274d83a8a8259231e9e954942a8a432ce7e10a4700  NestedIntervals.lean
b2bed9fde71d4f4db51f6e2c79ea1ce8c2174ac51d99093aa345ea7460ec56f5  PriorErdos206.lean
f021aca73b8b29636dcb37d7047d4ec21d2c90b96bfdd4cc0c8a70c240a62e93  PROOF.md
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  lean-toolchain
c307dc2559ded567d155e0b32140412821251f5eaef5b962df3a9c9694694905  lake-manifest.json
```

The working manifest references a local Mathlib path. A distributable package should pin the intended external revision independently; this audit does not claim that the temporary workspace manifest is portable.

## Exact target and quantifiers

The imported `Erdos206.EgyptianFractions.EventuallyGreedy` says that x is positive and there exists ONE strictly increasing map m : Nat -> Nat, with all entries positive, whose first n entries form a best n-term underapproximation at every sufficiently large n. `IsBestNTerm` requires cardinality exactly n, positive denominators, a strict sum below x, and domination of EVERY competing valid n-element finite set.

These definitions match Kovač's precise version of the original informal question. They neither restrict to the greedy expansion begun at the first term nor select one maximizing representation and silently ignore the others.

The final theorem proves `(1/4)<explicitNumber<1/2`, irrationality, and the negation of that whole eventual property. The bad-interval criterion has the needed quantifier `forall N, exists t>=N`, not just one finite failing triple.

## Algorithm and equality with the manuscript

- `optimize 0 L z` is empty. For positive n the baseline is exactly K+1,...,K+n with K=L+ceil_nat(n/z).
- The candidate list enumerates a from 0 through floor_nat(n/B), filters `L<a` and `1/a<z`, and recursively appends the suffix optimum with denominator lower bound a. The filter excludes zero, regardless of Lean's totalized division at zero.
- The baseline is the first list element. `List.argmax` retains the earlier element on a tie. This was confirmed against the pinned Mathlib source `Mathlib/Data/List/MinMax.lean`, lines 39–41 and 82–90. Therefore the manuscript's baseline-first, first-max convention is exact; no global lexicographic rule is asserted.
- `nextLevel` expands to previous.level + ceil_nat(1/(middle-lower)) + 3, exactly as printed.
- `stepIndex` is exactly M+4+ceil_nat(2/(z-q))+2^(s+2)+2*q.den^(s+2)+1.
- `state (s+1)=nextState s (state s)`. Thus the first update uses s=0. `nestedData` reindexes its lower/upper sequence to state(s+1), while its approximant is nextQ(state s); this precisely matches q_s and the newly constructed interval in the manuscript.

## Executability and the real limit

The data-carrying path is composed of ordinary definitions on natural numbers, rational numbers, finite lists and finite sets. The optimizer is structurally recursive on its term count; `state` is structurally recursive on its stage index. There is no unbounded search or real-number comparison in either data computation. The state invariants are propositions, not oracle-provided data.

No `Classical.choose`, arbitrary maximizing-set choice, `sorry`, added axiom, unsafe implementation, or external oracle appears in these rational data-path definitions. The only explicitly noncomputable definition in StageRecurrence.lean is `explicitNumber`, the real supremum of the specified rational lower endpoints. This is appropriate: Lean's abstract real-number representation does not make the rational approximation procedure noncomputable.

Crucially, the executable `approximate n` is linked to that SAME real supremum by

    |explicitNumber - (approximate n : Real)| <= (1/2)^n / 2.

Thus the existence proof is not disconnected from the claimed algorithm. The bound gives a terminating precision-selection procedure. No practical runtime bound or evaluated first-stage decimal expansion is claimed.

## Local obstruction and nonunique maxima

The generic local lemma starts with an actual best t-set S at rational z and compares it against any alleged compatible chain at x. Equality of their t-term SUMS follows from mutual optimality at x; equality of denominator sets is never assumed.

The legal competitor S union {i} forces the next chain denominator to be at most i; the upper interval endpoint forces it to be at least i. The subsequent denominator is forced to be sufficiently large that the two-term competitor beats it. The imported competitor lemma is applied to the alleged chain, whose preceding denominators are all below its t-th denominator i. This avoids collision problems even when S and the chain represent the same rational sum differently.

The concrete pair uses natural division by 2 only on i(i+1); `half_product_cast` proves exact divisibility before the real arithmetic is applied. The recurrence makes i larger than every element of its computed best set and uses closed subintervals strictly inside the bad open intervals. Consequently neither repeated denominators nor a limit landing on a bad-interval boundary creates an escape.

## Limit, irrationality and positivity

The limit is the supremum of monotone lower endpoints, and `limit_mem` puts it in every closed interval. The geometric width bound proves uniqueness. Strict membership of state(1) inside the original interval proves the final strict bounds (1/4,1/2).

The generic nested-data theorem proves a positive approximation error smaller than den(q_n)^(-n-2), with den(q_n)>=2. It obtains `Liouville` and then `Irrational`; the human proof instead gives the direct rational-denominator contradiction. These are compatible proofs of the same required conclusion. Neither relies on the July 2026 rational eventual-greediness theorem.

## Scope limits

This verifies meaning and algorithm specification, not novelty in every unpublished source, practicality of the optimizer, or acceptance of the word explicit by the problem's authors. SOURCE-NOVELTY-AUDIT.md records the literature/public-source review and its limitations. The result must be described as the explicit-example supplement, not a new solution of the boxed almost-everywhere problem.
