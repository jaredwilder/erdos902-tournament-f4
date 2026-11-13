# New theorem: a 49-vertex S4 tournament cannot have a cloned DRT23 in-neighborhood

**13 November 2026 — research addendum; new independent candidate theorem for the next case of Erdős #902.** The previously established proposed f(4)>=49 bound and the published 37-class DRT(23,11,5) classification are assumed. This is **not** a claim that f(4)>=50 has been proved. This addendum gives a new general combinatorial rigidity lemma and a complete finite exclusion of a precisely stated structural family of 49-vertex configurations.

## The exact theorem and its scope

Assume T is a *regular* tournament on 49 vertices with Schütte property S4. Let v be any vertex and H=I_T(v), so |H|=24. Suppose a vertex w in H has precisely 11 in-neighbors inside H, and suppose U=H\{w} induces a doubly regular 23-vertex tournament. **Then no such T exists**, given the published exhaustive classification of 37 DRT(23,11,5) isomorphism classes.

The 49-regularity premise is already forced by the stronger earlier f(4)>=49 result plus the existing 25*85<2475 exclusion of an indegree-23 vertex, within the same published classification dependency. The current theorem does *not* establish that every 24-vertex H has a deletion U that is DRT23. It eliminates the entire family in which that happens with w of internal indegree 11.

## Pure mathematical lemma: a universal principal-neighborhood rigidity law

Let D be any doubly regular tournament on n=4t+3 vertices, where every vertex has indegree/outdegree r=2t+1 and every pair of vertices has exactly t common in-neighbors. Suppose W is a subset of size r such that

    |W intersect I_D(x)| >= t    for every vertex x.

Define a_x=|W intersect I_D(x)| and b_x=a_x-t >= 0. By degree and pair-intersection double counting,

    sum_x a_x = r^2
    sum_x binom(a_x,2) = t*binom(r,2).

Consequently

    sum_x b_x = t+1
    sum_x b_x^2 = (t+1)^2.

But (sum b_x)^2=sum b_x^2 +2 sum_(x<y) b_x*b_y. Therefore all pairwise products b_x*b_y vanish. Exactly one vertex a has b_a=t+1; every other b_x=0. Thus a_a=r, so W=I_D(a). The vertex a is unique, because two distinct in-neighborhoods intersect in only t<r points.

**Rigidity theorem:** Every size-(2t+1) subset satisfying the uniform t-intersection lower bound is one of the tournament's actual in-neighborhoods, and there are exactly 4t+3 such subsets. This is classification-free, for every t>=1. Independent exhaustive test checks all C(23,11) possible W in each of 37 DRT23 rows: **851 principal masks and zero nonprincipal successes**.

## Why w must clone one vertex of U

Because H=I_T(v) and T has S4, every triple has at least five common in-neighbors (existing formal structural lemma). As w has exactly eleven in-neighbors in H, W=I_U(w) is an 11-subset of U, and for every h in U:

    |I_U(w) intersect I_U(h)| >= 5.

The rigidity theorem at t=5 gives W=I_U(a) for some unique a in U. Therefore w behaves exactly as a *clone* of a relative to the 22 other vertices of U: w beats a, and w and a agree on their orientation toward every other vertex of U. In particular, W_w=O_U(w)=O_U(a) union {a}, of size 12.

Since T is 24-regular, w beats v and twelve vertices of U; hence among X=O_T(v), |X|=24, exactly **11 vertices are beaten by w** and **13 beat w**.

## Independent finite exclusion: 46 out of 46 possible clone extensions

H must have S3: append v to any triple inside H and apply S4. A separate full 37x23 finite test constructs the cloned 24-vertex H for every catalogue class and every pivot a, then checks every triple. Exactly **46** clones have S3: all 23 choices for row35 and all 23 choices for row36; zero clones in the other 35 classes.

Let B be the collection of four-subsets of U with *no* common dominator inside U. Every such quadruple must be beaten by w or by some vertex of X; v cannot beat any U vertex. Write C_w for those already beaten by w, and B'=B\C_w. It is essential to count only NEW repairs to B', so overlap with w is never double-counted.

For each x in X, let M_x={u in U: x beats u}. The common-in-neighbor >=5 inequality for the triple (v,x,h) gives

    |M_x intersect I_U(h)| <= 6 + indicator(w beats x and w beats h)

for every h in U.

There are precisely 13 x with x beats w: they obey the **uniform** cap <=6 for every h. Eleven x with w beats x obey a **hybrid** cap <=7 for h in O_U(w) and <=6 otherwise.

The independent C++17 program builds the bad-four-set indicator on each selected DRT23 row, applies exact 23-bit subset zeta summation, subtracts the sets already repaired by w, then exhaustively maximizes remaining repair capacity over *all 2^23 subsets* in each of the 46 row/pivot pairs subject to the respective uniform/hybrid constraints.

It checks the strict inequality:

    |B'| > 13 * maxUniformNewRepair + 11 * maxHybridNewRepair.

**All 46 inequalities hold**, with a minimum positive gap of **30** in class35/pivot4. Class36 (the Paley type) has a gap of **110** for all pivots. There are no untested masks or probabilistic failure estimates within this finite case court.

The original naive capacity sum overcounts w's repairs; some naive cases are tied or inconclusive. The *overlap subtraction* is the decisive mathematical invention that closes all 46 cases.

## Interpretation and remaining frontier

This is a precise new **49-vertex exclusion theorem**, within the published classification dependency, not the global bound f(4)>=50. A putative 49-vertex S4 tournament must avoid any 24-vertex in-neighborhood formed by cloning a DRT23 in the stated internal-indegree-11 way. The next remaining target is to exclude general 24-vertex S3 in-neighborhoods without that DRT deletion, or those with DRT deletion but different internal degree.

The universal principal-neighborhood rigidity lemma does not depend on the classification or the finite computer program. The 46-case exclusion depends on the published 37-class completeness theorem and independently certified finite computation. These claims have not been externally refereed or fully integrated into one unconditional Lean kernel theorem.

## Reproduction and negative controls

    cd independent-review-20261113
    g++ -std=c++17 -O3 verify_drt_rigidity.cpp -o /tmp/verify_rigidity
    /tmp/verify_rigidity drtourn23.txt
    g++ -std=c++17 -O3 verify_clone49.cpp -o /tmp/verify_clone49
    /tmp/verify_clone49 drtourn23.txt

Expected concluding lines:

    GENERAL_RIGIDITY_37_CLASS_FINITE_COURT=PASS
    CATALOGUE_CLASSES=37
    S3_CLONE_EXTENSIONS=46
    MIN_GAP=30 WORST_ROW=35 WORST_PIVOT=4
    NO_49_S4_TOURNAMENT_WITH_DRT23_CLONED_INNEIGHBORHOOD=PASS

The catalogue input is the same 37-row data independently distinguished by the prior six-/eight-subtournament fingerprint court; frozen SHA-256: 20dbad06e128f968e87ce5bec9ca3128b8d2e9a9f25152b29d82c48c967b45d0. A mutated catalogue bit must be rejected by the DRT parameter checks. No model, frontier inference, GPU or network is involved in the mathematical finite verification.
