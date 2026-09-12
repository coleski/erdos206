# A computable irrational with non-eventually-greedy best Egyptian underapproximations

**Locally verified construction.** This proof addresses the explicit-example supplement to Erdős Problem #206. The complete formal theorem passed two fresh-source builds and independent implementation-to-statement audits; see VERIFICATION.md. It is not a claim to newly solve the main almost-everywhere question, which Kovač already resolved, or a claim of external community acceptance.

## Statement and provenance

For a positive real number \(x\), let \(R_n(x)\) be the largest sum of \(n\) distinct reciprocals of positive integers that is strictly smaller than \(x\). Following Kovač's precise formulation, say that \(x\) is *eventually greedy* if there are a strictly increasing sequence of positive integers \((m_k)_{k\geq0}\) and an integer \(N\) such that
\[
R_n(x)=\sum_{k=0}^{n-1}\frac1{m_k}\qquad(n\geq N).
\]
Thus the issue is whether one compatible sequence of optimal prefixes exists eventually, not whether the greedy sequence started at its first term is optimal.

Erdős and Graham asserted that one can construct irrationals failing this property, without supplying a construction. Kovač proved that almost every positive real fails it, but explicitly distinguished his measure-theoretic existence result from finding an individual example. The current problem commentary asks for an explicit example. [Erdős–Graham, printed p.31](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf); [Kovač, §§1–3](https://arxiv.org/abs/2406.07218); [Problem #206](https://www.erdosproblems.com/206).

**Theorem.** The deterministic rational recurrence specified below defines a computable irrational number \(x\in(1/4,1/2)\) that is not eventually greedy. Its finite stages give a proved error bound for approximating \(x\).

Here *computable* means that, given any requested positive rational accuracy, a terminating algorithm returns a rational approximation within that accuracy. No closed-form expression or practical running-time bound is claimed. The two-term obstruction used below is a specialization of Kovač's construction; the addition is the individual effective nested-interval witness.

## 1. An exact terminating rational optimizer

Write
\[
\sigma(S)=\sum_{a\in S}\frac1a
\]
for a finite set of positive integers. We specify an algorithm \(\mathcal O(n,L,z)\), for integers \(n,L\geq0\) and rational \(z>0\). It returns a maximizing set of \(n\) distinct denominators greater than \(L\), with reciprocal sum strictly below \(z\).

Set \(\mathcal O(0,L,z)=\varnothing\). For \(n\geq1\), form
\[
K=L+\left\lceil\frac nz\right\rceil,\qquad
S_0=\{K+1,\ldots,K+n\},\qquad B=\sigma(S_0).
\]
Here and below, ceilings and floors with natural-number outputs agree with ordinary ceilings and floors on the positive inputs where they are used. We have \(0<B<z\).

Starting with \(S_0\), construct a finite ordered list by appending, in increasing order of \(a\), the sets
\[
\{a\}\cup\mathcal O\left(n-1,a,z-\frac1a\right)
\]
for all integers
\[
0\leq a\leq\left\lfloor\frac nB\right\rfloor,
\qquad L<a,\qquad \frac1a<z.
\]
Return the first set in this list with largest reciprocal sum. The baseline is first even when it ties another maximizer. No global lexicographic convention is imposed.

**Correctness.** The recursion decreases \(n\), and every list is finite and nonempty. Each listed set has the required cardinality and strict denominator separation, by induction. The baseline is feasible because \(K+1>n/z\).

Consider any feasible competitor with smallest denominator \(a\). If its sum is below \(B\), it loses to the baseline. Otherwise its sum is at most \(n/a\), so \(a\leq n/B\), and its first denominator is enumerated. By induction, the recursive suffix is at least as good as the competitor's suffix. This proves maximality and termination. In particular,
\[
\sigma(\mathcal O(n,0,z))=R_n(z).
\]

The same finite-branch argument, interpreted mathematically rather than algorithmically, also proves existence of best sums for arbitrary positive real targets.

## 2. A quantitative density observation

Suppose \(0<z<1\). Starting with \(r_0=z\), define the strict greedy denominators and remainders by
\[
a_k=\lfloor1/r_k\rfloor+1,\qquad
r_{k+1}=r_k-1/a_k.
\]
These remainders are positive. Since \(a_k\leq1/r_k+1\),
\[
\frac1{a_k}\geq\frac{r_k}{1+r_k}>\frac{r_k}{2},
\qquad 0<r_{k+1}<\frac{r_k}{2}.
\]
The denominators strictly increase. Indeed,
\(1/a_k<r_k\leq1/(a_k-1)\), so
\[
r_{k+1}\leq\frac1{a_k(a_k-1)}\leq\frac1{a_k},
\]
and the last overall inequality is strict: equality would require \(a_k=2\) and \(r_k=1\), excluded by \(r_k<1\). Thus \(a_{k+1}>a_k\).

The first \(t\) greedy terms therefore form a legal competitor, giving
\[
0<z-R_t(z)\leq r_t<z2^{-t}<\frac1t\qquad(t\geq1),
\]
where the last inequality uses \(2^t\geq t\) and \(z<1\). Consequently, if \(0<L<z<1\) and
\[
t>\frac1{z-L},
\]
then \(R_t(z)>L\).

## 3. An explicit interval on which three optimal prefixes cannot be compatible

For an integer \(i\geq4\), put \(T=i(i+1)\), which is even, and define
\[
u_i=\frac1{i+1}+\frac1{T/2+1},\quad
v_i=\frac1i+\frac1{T+4},\quad
w_i=\frac1i+\frac1{T+5}.
\]
A direct calculation gives
\[
u_i-\frac1i=\frac{T-2}{T(T+2)}
=\frac1{T+4+8/(T-2)}.
\]
Because \(T\geq20\), we have \(0<8/(T-2)<1\). Hence
\[
\frac1i<w_i<u_i<v_i<\frac1{i-1},
\qquad v_i<\frac2i.
\]
This is the \(k=1\) specialization of Kovač's bad two-term approximation construction. [Kovač, §2](https://arxiv.org/abs/2406.07218).

Let \(z\in(0,1)\) be rational, let \(S=\mathcal O(t,0,z)\), and put \(q=\sigma(S)\), where \(t\geq1\). Choose \(i\geq4\) larger than every denominator in \(S\), and assume \(q+v_i<z\).

**Local obstruction.** For every
\[
x\in(q+u_i,q+v_i),
\]
no strictly increasing sequence of positive denominators can have optimal prefixes at all three lengths \(t,t+1,t+2\).

**Proof.** First \(R_t(x)=q\): the set \(S\) is admissible below \(x\), and every competitor below \(x<z\) is also a competitor below \(z\).

Suppose a compatible sequence exists. Its \(t\)-term sum is \(q\). Its next denominator must be \(i\). A smaller denominator overshoots \(x\), since \(x-q<v_i<1/(i-1)\). A larger denominator loses to the legal competitor \(S\cup\{i\}\), whose sum is \(q+1/i<x\). This also disposes of the case where that sequence's own representation of \(q\) already has a last denominator at least \(i\): its next denominator would be too large.

Its following denominator must be \(T+5\). A denominator at most \(T+4\) overshoots \(x\); one larger than \(T+5\) loses to the admissible extension of its current prefix by \(1/(T+5)\). The claimed \((t+2)\)-term optimum is therefore \(q+w_i\).

But \(S\cup\{i+1,T/2+1\}\) is a legal \((t+2)\)-term competitor with sum \(q+u_i\), and
\[
q+w_i<q+u_i<x.
\]
Both added denominators exceed \(i\) and are distinct. This is a contradiction. Notice that the argument never assumes uniqueness of the representation of \(q\). ∎

## 4. The deterministic recurrence

Use zero-based step indices \(s=0,1,2,\ldots\). Initialize
\[
(L_0,U_0,\ell_0)=(1/4,1/2,0).
\]
Given \((L_s,U_s,\ell_s)\), compute the following rational and integer quantities, in this order:
\[
\begin{aligned}
z_s&=(L_s+U_s)/2,\\
t_s&=\ell_s+\left\lceil\frac1{z_s-L_s}\right\rceil+3,\\
S_s&=\mathcal O(t_s,0,z_s),\qquad q_s=\sigma(S_s),\\
M_s&=\max S_s.
\end{aligned}
\]
Write \(q_s\) in lowest terms with positive denominator \(D_s\). Define
\[
i_s=M_s+4+
\left\lceil\frac2{z_s-q_s}\right\rceil+
2^{s+2}+2D_s^{s+2}+1.
\]
Using the values \(u_s=u_{i_s}\) and \(v_s=v_{i_s}\) from §3, set
\[
\boxed{
L_{s+1}=q_s+\frac{2u_s+v_s}{3},\qquad
U_{s+1}=q_s+\frac{u_s+2v_s}{3},\qquad
\ell_{s+1}=t_s.
}
\]
These formulas, including the optimizer's specified tie rule, define the number completely. There are no choices of an unspecified good point, an unspecified optimal representation, or an unspecified member of a full-measure set.

**Well-definedness and nesting.** Inductively assume
\(1/4\leq L_s<U_s\leq1/2\). Then \(0<L_s<z_s<1\), and §2 gives
\[
L_s<q_s<z_s.
\]
Thus every division and maximum in the recurrence is valid. The integer \(i_s\) satisfies
\[
i_s\geq4,\quad i_s>M_s,\quad
i_s>\frac2{z_s-q_s},\quad
i_s>2^{s+2},\quad i_s>2D_s^{s+2}.
\]
In particular \(q_s+v_s<q_s+2/i_s<z_s\). Hence
\[
[L_{s+1},U_{s+1}]
\subset(q_s+u_s,q_s+v_s)
\subset(L_s,z_s)
\subset(L_s,U_s).
\]
All stages exist, and all intervals are nonempty.

Their lengths satisfy
\[
0<U_{s+1}-L_{s+1}
=\frac{v_s-u_s}{3}
<\frac2{i_s}<2^{-s-1}.
\]
Consequently the nested closed intervals have exactly one common point. Define
\[
x=\lim_{s\to\infty}L_s=\lim_{s\to\infty}U_s,
\]
which is that point. The strict first nesting gives \(1/4<x<1/2\).

**Computability and modulus.** Every finite stage consists of terminating exact rational arithmetic and the finite optimizer. The midpoint
\[
c_s=(L_{s+1}+U_{s+1})/2
\]
satisfies the certified bound
\[
|x-c_s|\leq\frac{(1/2)^s}{2}=2^{-s-1}.
\]
Indeed the interval estimate above is slightly stronger than needed for this bound; the displayed modulus is the one stated by the formal theorem `approximate_error`. Therefore these formulas are an algorithm for approximating \(x\) to any prescribed accuracy. The proof gives a precision bound in the stage index, not a claim that the stages run quickly.

## 5. Failure of eventual greediness

For every \(s\), the point \(x\) lies strictly inside \((q_s+u_s,q_s+v_s)\). The local obstruction therefore forbids a compatible optimal-prefix sequence at the lengths
\[
t_s,\quad t_s+1,\quad t_s+2.
\]
Moreover \(\ell_{s+1}=t_s\geq\ell_s+3\), so \(t_s\to\infty\).

If \(x\) were eventually greedy, its witnessing increasing denominator sequence would have optimal prefixes at every sufficiently large length. Choosing \(s\) with \(t_s\) beyond that threshold contradicts the local obstruction. Thus \(x\) is not eventually greedy.

## 6. Irrationality

The same construction gives
\[
0<x-q_s<v_s<\frac2{i_s}<D_s^{-s-2}.
\]
Since \(1/4<q_s<1/2\), we have \(D_s\geq2\). Suppose \(x=a/b\) were rational with \(b\geq1\). The positive difference between this number and the reduced rational \(q_s\) is at least \(1/(bD_s)\). Choose \(s\) with \(2^{s+1}>b\). Then \(D_s^{s+1}>b\), and
\[
\frac1{bD_s}\leq x-q_s<D_s^{-s-2}<\frac1{bD_s},
\]
a contradiction. This proves irrationality directly, without using the later theorem that every positive rational is eventually greedy. ∎

## Scope of the claim

The proof concerns the entire explicit-example supplement in the constructive sense stated above: one fully specified irrational is shown to fail eventual optimal-prefix compatibility, not merely to fail at one length or along one preselected greedy expansion. Kovač's almost-everywhere theorem and Kovač–Tang's rational theorem are prior results, not conclusions claimed as new here. The source-meaning audit found no requirement excluding an effective recurrence. External acceptance remains outstanding and is not represented by the local proof checks or by public posting of this package.
