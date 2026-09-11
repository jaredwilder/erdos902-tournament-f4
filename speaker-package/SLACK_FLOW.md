# SLACK-FLOW — exact extension conservation in regular tournaments

Let \(T\) be a \(d\)-regular tournament and let

\[
c(A)=|\{y:y\to a\text{ for every }a\in A\}|
\]

be the common-dominator count of a finite set \(A\), with \(|A|=r\).

Then

\[
\boxed{
\sum_{x\notin A}c(A\cup\{x\})=(d-r)c(A).
}
\]

## Double-counting proof

Count ordered pairs \((y,x)\) such that:

- \(y\) dominates every vertex of \(A\);
- \(x\notin A\);
- \(y\to x\).

Fix \(x\). The possible \(y\)'s are precisely the common dominators of
\(A\cup\{x\}\), giving the left-hand side.

Fix \(y\). Since \(y\) dominates all \(r\) vertices of \(A\) and has exactly
\(d\) out-neighbours total, exactly \(d-r\) of its out-neighbours lie outside
\(A\). There are \(c(A)\) choices of \(y\), giving the right-hand side.

## Order 49

A surviving order-49 \(S_4\) tournament must be 24-regular.

Write

\[
e_2(P)=c(P)-11,\qquad e_3(Q)=c(Q)-5,\qquad e_4(R)=c(R)-1.
\]

The existing multiplicity theory gives all three slacks nonnegative.

For a pair \(P\), there are \(47\) one-vertex extensions and \(d-r=22\):

\[
\sum_{x\notin P}e_3(P\cup\{x\})
=22c(P)-47\cdot5
=7+22e_2(P).
\]

For a triple \(Q\), there are \(46\) extensions and \(d-r=21\):

\[
\sum_{x\notin Q}e_4(Q\cup\{x\})
=21c(Q)-46
=59+21e_3(Q).
\]

Thus:

\[
\boxed{e_2\mapsto 7+22e_2\mapsto 59+21e_3.}
\]

These are local exact conservation laws, not averages.

Globally, regularity fixes:

\[
\sum_{|P|=2}e_2(P)=588,
\]

\[
\sum_{|Q|=3}e_3(Q)=7056,
\]

\[
\sum_{|R|=4}e_4(R)=308798.
\]

The local laws sum consistently:

\[
3\cdot7056
=
\binom{49}{2}\cdot7+22\cdot588,
\]

and

\[
4\cdot308798
=
\binom{49}{3}\cdot59+21\cdot7056.
\]

## Why this matters

The order-49 problem is no longer merely "search all regular tournaments."
Every unit of pair-level excess has an exactly prescribed amount of
higher-order consequence. Any future private-witness, capacity, or
third-moment obstruction can therefore charge against a conserved slack flow.
