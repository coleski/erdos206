# Erdős #206 explicit-example supplement: independent audit

Read-only public-source audit, 2026-09-12. No publication, external write, or unconditional novelty certification.

## Verdict

The frozen supplement is genuinely stated in the live problem commentary. I found no prior explicit non-eventually-greedy irrational construction in the primary papers or public repositories inspected. A deterministic rational recurrence with proved termination and a computable convergence modulus is a defensible interpretation of the requested construction. The primary sources impose no closed-form, named-constant, or efficient-runtime requirement. This interpretation is not a promise of acceptance by the authors or problem-page moderators.

Any eventual claim must say **explicit-example supplement to #206**, not a new solution of the already solved almost-everywhere question.

## Original source, inspected directly

Erdős–Graham, Old and New Problems and Results in Combinatorial Number Theory (1980), printed p.31:

https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf

This PDF is image-only. Printed p.31 is PDF page 27 (one-based), rendered and visually read in full; retained as original-printed31.png in this directory. It defines eventual optimal greedy extensions, asserts the rational case, conjectures the algebraic case, says that constructing failing irrationals is not difficult, and then speculates about almost all reals. It gives neither a construction nor a definition of explicitness. The selected construction request is therefore not an invented restricted subproblem.

## Primary follow-up literature

1. Kovač, arXiv:2406.07218v3, dated 2024-09-26; published J. Number Theory 268 (2025), 39–48.
   https://arxiv.org/pdf/2406.07218
   https://doi.org/10.1016/j.jnt.2024.09.004
   The complete seven-page arXiv text was read. Theorem 1 is the measure-zero result; Corollary 2 gives a transcendental non-eventually-greedy real nonconstructively. The author explicitly distinguishes this from finding a particular number. Section 2 gives the bad two-term intervals used by the candidate; these must be credited, not claimed as new. Section 3 uses a recursive partition/measure contraction, but does not specify an individual nested-hole recurrence, effective optimizer, or computable witness.

2. Kovač–Tang, arXiv:2607.28387v2, dated 2026-08-04.
   https://arxiv.org/pdf/2607.28387
   Read the introduction, exact theorem statements, and Section 5/Example 2, with relevant full-text searches. Theorem 1 solves rational eventual greediness under both denominator conventions. Example 2 constructs sum_{n>=1} 2^(-n!), whose unique best approximations are greedy at EVERY length. This is the opposite property and does not settle our supplement. The paper does not define explicitness to exclude arithmetic recurrences. No non-eventually-greedy irrational construction was found. The full optimal-control proof was not independently reverified; our candidate does not require it.

3. Nathanson, Underapproximation by Egyptian Fractions, arXiv:2202.00191v2 (2022), published 2023.
   https://arxiv.org/pdf/2202.00191
   Open problem (4), pp.17–18, quotes the construction assertion and asks for a proof or disproof. It does not demand a closed form. Open problem (3) separately asks for an efficient algorithm for finite optimization; this is a different question and must not be conflated with a merely terminating algorithm sufficient to specify a real number.

## Live problem page and forum

https://www.erdosproblems.com/206
https://www.erdosproblems.com/forum/discuss/206

Direct curl succeeded; browser search fetch returned 403. Read the full visible page/forum. The main status is DISPROVED (LEAN), five comments, zero proof claims and zero expositions. The commentary explicitly leaves the explicit example open. The rational-status paragraph is stale: the July 31 comment by Quanyu Tang links the rational solution. Thus the page's general freshness is imperfect; open wording alone is not sufficient novelty evidence.

## Jig, direct live API

https://jig.so/api/problems?limit=500&offset=0

Returned total=355, has_more=false, next=null. No visible root has erdos=206 or an eventually-greedy title. This is evidence about the current visible board, not proof that no related statement exists anywhere. Indexed search was inconsistent and was not used as the negative check.

## GitHub

- https://github.com/QuanyuTang/eventually-greedy-egyptian-candidate-proof
  Read README and inspected the preliminary main2.tex manuscript / relevant searches. This archive concerns the rational theorem. The two conversation PDFs are image-only, so empty text-search output was NOT treated as an exhaustive negative search. The first page of the successful transcript was rendered and inspected: its explicit task and proposed method concern the rational conjecture and Böttcher/optimal-control construction. I have not visually reviewed every transcript page; this is a residual coverage limit.

- https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos206.lean
  Inspected definitions, proof structure and explicit/irrational/nested/computable hits, plus its README. This is the Kovač measure-zero formalization, with noncomputable choices of best sums. The final theorem is a volume-zero statement, not a named computable irrational.

- https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/Erdos206Problem.lean
  Read entire file. It axiomatizes the best-sum function and Kovač theorem; it explicitly leaves an explicit irrational example open. Its proposition named explicit_nongreedy_example_exists is just bare existence, not an explicit construction and not a proof. Its rational-status prose is stale.

- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/206.lean
  The public status/link PRs #4385, #4529, #4718 concern the boxed measure question and links to plby; no construction claim found in those records.

Repository-name and issue searches were performed for erdos206, erdos-206, eventually greedy, and Egyptian/explicit combinations. GitHub's unauthenticated code-search API returned 401; it was not silently represented as a successful global code search.

## Meaning and mathematical audit of the candidate

The exact definition adopted by Kovač is existence of one strictly increasing positive denominator sequence whose prefixes equal the best sums at all sufficiently large lengths. The candidate negates that whole property, by forbidding compatible optimal prefixes at infinitely many triples of lengths. It does not merely show that greediness from the initial one-term optimum fails infinitely often. This matches the authoritative precise interpretation of the original informal wording.

The local argument correctly accommodates nonunique representations of the best t-sum: its computed optimal tuple supplies legal competitors, while any hypothetical compatible chain is separately forced to append the specific denominators. Choosing i above the computed tuple's maximum ensures that the alternate pair introduces no repeated denominator. If a hypothetical chain already uses a larger denominator, it loses at length t+1, as the proof notes.

The rational optimizer's induction is finite and valid: a feasible baseline B bounds the first denominator of every competitive tuple by t/B; the remaining optimization reduces the term count. Global lexicographic minimality is unnecessary. A deterministic first-max choice from a fixed finite traversal is enough; the written recurrence and implementation should use the same convention.

The stage search terminates because best t-sums tend to z. In fact the candidate's strict greedy residual estimate gives an elementary explicit bound: any t with 2^t>z/(z-L) has R_t(z)>L. This can replace an unbounded-looking search if useful, though a proved-terminating search is already computable.

Nested closed intervals lie strictly inside each bad open interval, with an explicit width bound, so endpoint escape cannot undo a local failure. The approximation inequality 0<x-q_s<D_s^(-s-2) proves irrationality directly; there is no dependency on the 2026 rational theorem.

I found no mathematical meaning mismatch in CANDIDATE-PROOF.md as read. This is not a completed Lean audit or a proof that the implementation and written recurrence coincide.

## Reporting and acceptance limits

Recommended wording after verification: an explicit computable irrational, specified by a deterministic rational recurrence with a convergence modulus, resolving the explicit-example supplement as understood here. Credit Kovač's bad two-term construction and explain the effective diagonal/nested-interval addition.

Do not call the construction closed-form. Do not claim a practical digit-computation rate without measurements. Do not claim complete literature exclusion, full transcript coverage, or formal verification until those gates are actually met. The genuine contribution would be the individual effective witness, not reproving the measure theorem or rational theorem.
