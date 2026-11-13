# Uniform 37-class incidence proof of f(4) >= 49

**13 November 2026; research addendum.** New proof strategy for the earlier candidate by Jared Wilder, not an independently accepted record or an unconditional Lean closure. Uses one named published mathematical theorem: there are exactly 37 nonisomorphic DRT(23,11,5) tournaments. The prior independent certificate in this PR distinguishes all 37 supplied representatives by induced-subtournament fingerprints.

## Lemma A: A general rigidity identity, NO classification

A doubly regular tournament T on 4t+3 vertices has every outdegree 2t+1 and every pair of outneighborhoods intersecting in t vertices. For any W subset T with |W|=w, put a_x = |W intersect I(x)|, where I(x) is the set of vertices beating x. Exact double counting gives:

   sum_x a_x = (2t+1)w
   sum_x C(a_x,2) = t C(w,2)

Hence **sum_x a_x(t+1-a_x) = t w (2t+2-w)**.

When every a_x<=t+1, the left side is nonnegative, so w<=2t+2. At equality, every a_x is 0 or t+1, exactly one vertex x has a_x=0, and that vertex must be in W: if it were outside, it would beat 2t+2 vertices, despite outdegree 2t+1. Thus W={x} union O(x). Conversely every such closed outneighborhood is admissible. The equality case has precisely 4t+3 masks.

At t=5, **admissible W has at most 12 vertices, with precisely 23 admissible W of size 12**. This applies to every DRT(23,11,5), not just the two S3 survivors.

## Lemma B: Every DRT23 has at least 2,109 undominated quadruples; NO classification

Write B_u=O(u), so |B_u|=11 and |B_u intersect B_v|=5. If four distinct vertices all beat a four-set Q, the four reduced sets B_ui minus Q each have 7 vertices and each pair has exactly one shared vertex. Their union has size at least 4*7-C(4,2)=22; there are only 23-4=19 available vertices. Contradiction. Thus each four-set has at most **3 common dominators**.

Let n_j be the number of four-sets with j common dominators. Double counting yields

   sum n_j = C(23,4) = 8855
   sum j*n_j = 23*C(11,4) = 7590
   sum C(j,2)*n_j = C(23,2)*C(5,4) = 1265.

Eliminating gives n_0 = 2530 - n_3. As 3*n_3 <=1265, n_3 <=421, and **n_0>=2109**.

## Lemma C: Uniform computational capacity <=85, over ALL 37 classes

An independent C++17 court, uniform_f4.cpp, reads drtourn23.txt and verifies all 37 DRT structures. Every four-set with no internal dominator is marked. Integer subset-zeta summation provides the exact number of those bad four-sets contained in each 23-bit mask W. For EVERY class and EVERY W satisfying |W intersect I(h)|<=6 for all h, the maximum repair count is **85**. The maximizing row is 18, for an 11-set. There is no S3 row filter or assumption.

All 37 rows are pairwise nonisomorphic by the existing six-/eight-vertex fingerprint court. Together with the published 37-class total, this is exhaustive up to isomorphism. The original frozen catalogue SHA-256 is 20dbad06e128f968e87ce5bec9ca3128b8d2e9a9f25152b29d82c48c967b45d0.

## Consequence

The original structural argument in F4Struct.lean proves that an S4 tournament on 48 vertices contains an indegree-23 vertex v whose 23 in-neighbors form a DRT(23,11,5). Every undominated quadruple in that core must be covered by one of the 24 outside vertices x, with each outside neighborhood W_x admissible. Lemma B gives at least 2109 such quadruples; Lemma C gives at most 24*85=2040 possible repairs.

**2040 < 2109. Therefore f(4)>=49, assuming the published 37-class classification.**

This proof no longer needs to identify the two S3 classes, nor their precise 2475/2530 bad-four-set counts. The remaining finite proof is one uniform 85 capacity bound.

**Further restriction at n=49:** If an S4 tournament of order 49 has a vertex of indegree23, the same analysis gives 25 outside vertices. The separate catalogue-wide exact minimum of 2475 bad sets and maximum cap85 gives 25*85=2125<2475, contradiction. All indegrees must then be at least24; their average is24, so **any S4 tournament on 49 vertices must be 24-regular**. This does NOT prove f(4)>=50.

## How to replay

Compile uniform_f4.cpp with g++ -O3 -std=c++17, run on drtourn23.txt. Confirm final output:

    UNIVERSAL_BAD_LOWER=2109
    ALL_37_CAP_UPPER=85
    OUTSIDE_24_MAX_REPAIR=2040
    CLASSIFICATION_UNIFORM_GAP=69
    THEOREM_CONDITIONAL_ON_PUBLISHED_37_CLASS_COUNT=PASS

The independent Python file verify_general_rigidity.py exhausts all subsets of Paley tournaments on 7,11,19 vertices and tests Paley23 on randomized masks; all passed locally. The finite cap audit took ~8.5 CPU seconds, under 20MB resident memory. **Not yet externally reviewed or fully Lean-kernel checked.** Original f(4)>=49 candidate predates this addendum; prior-art review remains necessary before announcing a record.
