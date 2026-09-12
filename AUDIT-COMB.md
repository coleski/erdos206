# Independent adversarial audit: candidate #206 explicit-example supplement

Auditor: combinatorics subagent, 2026-09-12. Read TARGET.md, the full CANDIDATE-PROOF.md, the current official statement by direct GET, and the relevant credited prior Lean definitions/lemmas. This audit accepts the mathematical mechanism below. It does not settle the source's intended meaning of “explicit” or rule out equivalent prior constructions.

## Finite optimizer

The recursive denominator search is finite and exact. The feasible initial tuple has sum B>0. Every competing t-term tuple of sum at least B has first denominator at most t/B, since its sum is at most t/a. Candidates with smaller sum cannot maximize. After fixing a, the remaining target z−1/a is strictly positive, and recursion reduces t. The initial tuple's first denominator is in the finite enumeration, ensuring nonemptiness. Induction also justifies lexicographic tie-breaking: all maximizers lie in the finite first-denominator list, and each branch uses the lexicographically least maximizing tail. No oracle or unjustified uniform bound on all denominators is being assumed.

## Density and stage termination

For z∈(0,1), strict greedy choices a=floor(1/r)+1 yield 0<r−1/a<r/2, and the new remainder is less than 1/a. Thus the next denominator is strictly larger; all prefixes are legitimate distinct-unit-fraction candidates. Consequently R_t(z) tends to z, so the stage's unbounded search for R_t(z)>L terminates. All i inequalities are finite arithmetic lower bounds. The recurrence stays inside the initial interval (1/4,1/2), as required by the density proof.

## Alternate representations do not evade the obstruction

Only ONE computed optimal representation S of q is needed, with its denominators below i. It supplies the legal competitor S∪{i}; it is not necessary to bound the denominators in every alternative representation of q.

If a compatible chain is optimal at t, its prefix sum equals q by mutual maximality. At t+1, the competitor q+1/i forces the appended denominator to be at most i, while the upper interval bound forces it to be at least i. Hence it is i. If the chain's prefix already contains i or a larger denominator, strict monotonicity makes this impossible immediately.

At t+2 the upper bound forces the next denominator to be at least T+5. Hence the chain sum is at most q+w. It is unnecessary to claim that the next denominator is exactly T+5. The legal alternative with denominators i+1 and T/2+1 beats q+w and lies strictly below x. These alternative denominators are distinct and both exceed i, so neither conflicts with a chain prefix or the computed S.

The exact positive difference is

    u−w = (T−10)/[T(T+2)(T+5)],  T=i(i+1)≥20.

The interval length is positive because

    v−u = 8/[T(T+2)(T+4)].

This also covers reciprocal boundary concerns: the limit lies in a closed middle subinterval strictly inside the open bad interval; equality at u or v cannot occur.

## Nested limit and irrationality

Every new closed interval lies strictly within the preceding interval and has length <2^(−s−1). Completeness therefore gives a unique common real; rational midpoints provide a specified convergence modulus. Since t_s≥3s, the local failures occur beyond every proposed eventual threshold.

The rational-approximation argument proves irrationality without using any theorem about rational eventual greediness. Write q_s=c_s/D_s in reduced form. Since q_s∈(1/4,1/2), D_s≥2. If x=a/b, positivity of x−q_s implies x−q_s≥1/(bD_s). The construction gives x−q_s<D_s^(−s−2); together these force D_s^(s+1)<b, contradicted once 2^(s+1)>b. Strict inequalities and denominator signs are correct.

## Formalized local result

LocalObstruction.lean imports the existing credited PriorErdos206 definitions. It contains:

- `local_pair_obstruction`: generic finite-set competitor argument, requiring optimality only at exactly t,t+1,t+2, not at earlier lengths.
- `explicit_pair_bounds`: the exact formulas for i≥4, with natural-number division in T/2 proved correct using evenness of i(i+1).
- `explicit_interval_no_chain`: full local wrapper taking a finite optimal S for z, all its denominators below i, and x in the explicit bad interval with x≤z.

The file compiled successfully with Lean 4.33.0 / Mathlib 4.33.0; axiom reports for the explicit bounds and final local theorem list only propext, Classical.choice, Quot.sound. No sorry or extra axiom was added. This is a local theorem, not yet a formal proof of the complete computable recurrence and its limit.

## Remaining nonlocal gates

The exact optimizer's total correctness, the actual specified recurrence, and its link to the nested-limit theorem still require their own clean formal build. The historical/semantic question whether this effective construction is the requested “explicit example” is being audited separately. No claim that the original almost-everywhere question is newly solved is warranted.
