# REAL-002 — live Erdős #902 continuation

## Word discovered from the full mask language

For either possible 23-vertex DRT core carrying \(S_3\), exhaust **every**
admissible mask \(W\) with \(|W|\le 12\). Let \(R(W)\) count internally
undominated 4-subsets of the core contained in \(W\).

The exact global maxima are:

\[
\max R(W)=65\quad\text{(row 35)},\qquad
\max R(W)=66\quad\text{(row 36)}.
\]

So the language compresses the entire layer structure into

\[
\boxed{\texttt{ADMISSIBLE-REPAIR-CAPACITY}=66.}
\]

The complete size-by-size profiles are in `results.json`.

## Reframed \(f(4)\ge49\)

A hypothetical order-48 \(S_4\) tournament has, by the existing kernel-checked
reduction, a 23-vertex DRT core \(H\) carrying \(S_3\), and 24 outside vertices
whose masks are admissible.

Using published completeness of the 37 DRT(23) isomorphism classes, \(H\) is
row 35 or row 36. They contain 2475 and 2530 internally undominated 4-sets.

Every bad 4-set must be repaired by an outside vertex. Each outside vertex can
repair at most 66. Hence

\[
\#\mathrm{bad}(H)\le24\cdot66=1584,
\]

contradicting \(2475,2530>1584\).

Thus

\[
\boxed{f(4)\ge49}.
\]

This strictly simplifies the earlier 2448-envelope proof.

## The next sentence: order 49 must be regular

Let \(T\) be an order-49 \(S_4\) tournament. Existing formal mathematics gives
\(d^-(v)\ge23\) for every vertex.

If some vertex has indegree 23, its in-neighbourhood is the same 23-vertex DRT
core and there are now 25 outside vertices. The universal word gives total
repair capacity at most

\[
25\cdot66=1650<2475.
\]

So no vertex can have indegree 23.

Therefore every vertex has indegree at least 24. The average indegree in every
49-vertex tournament is exactly 24. Hence every vertex has indegree 24:

\[
\boxed{\text{Every hypothetical order-49 }S_4\text{ tournament is regular}.}
\]

The repository's previous unrestricted order-49 assault explicitly split into
an indegree-23 branch and a regular branch; the former ran for 5.37 CPU-hours
without a verdict. This theorem deletes that branch outright.
