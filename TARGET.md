# Frozen target: Erdős 206 explicit-example supplement

Frozen 2026-09-12 before developing the candidate proof below. Fresh selection from current public problem and forum, not earlier local research.

Sources: https://www.erdosproblems.com/206 and https://www.erdosproblems.com/forum/thread/206 (read in full today). This numbered problem is not in the excluded Epoch list.

For real x>0 and integer n>=1, R_n(x) is the largest sum of n distinct reciprocals of positive integers strictly below x. Call x eventually greedy if there exist a strictly increasing sequence m:N->N of positive integers and N0 such that for every n>=N0, the sum over i<n of 1/m(i) is R_n(x).

Selected existing question: give an explicit irrational positive real number which is NOT eventually greedy. The webpage explicitly says that giving any explicit example remains open. We will specify a deterministic rational recurrence with proved termination and a computable convergence modulus; a bare existential measure argument or an unspecified witness will not qualify. Whether this construction meets the source's intended meaning of 'explicit' requires a separate meaning audit.

Exact negative property: for every strictly increasing positive integer sequence m and every N0, some n>=N0 has prefix sum different from R_n(x).

Not selected: the main almost-everywhere question (already disproved by Kovač 2024 and formalized); the rational eventual-greediness question (solved by Kovač–Tang July 2026). Do not claim to newly solve either. We seek only the independently posed explicit-example supplement, without weakening the definition of eventual greediness.

Candidate mechanism to investigate: effective exact finite optimization for R_n at rational arguments, nested rational intervals on which optimal prefixes cannot remain compatible through three consecutive lengths, and an explicit shrinking-interval recurrence forcing infinitely many such failures.

Status at freeze: no resolution claimed. Subsequent result: all local proof, adversarial review, source-meaning, current-status, and clean-build gates have been completed; see VERIFICATION.md. This final status does not change the frozen mathematical question or claim public acceptance.
