# A 48-vertex obstruction for Schütte's tournament property \(S_4\)

**Research note / independent finite audit — November 13, 2026**  
Original research candidate: Jared Wilder, [`erdos902-tournament-f4`](https://github.com/jaredwilder/erdos902-tournament-f4).  
Independent computational reproduction and editorial proof reconstruction: November 13, 2026.  
**Status:** Complete *mathematical argument* relying on a published exhaustive classification of doubly regular 23-vertex tournaments, with a new independently executable finite verification. **Not yet externally refereed, and not yet a complete single-file Lean-kernel proof.** The broader Erdős problem #902 remains open.

## Statement

Write \(S_k\) for the property that every \(k\)-element set of tournament vertices has a common dominator outside the set. Let \(f(k)\) be the smallest number of vertices in a tournament with \(S_k\). A published result of Reid, McRae, Hedetniemi and Hedetniemi (2004) gives \(f(4)\ge48\), while the Paley tournament on 67 vertices gives \(f(4)\le67\).

**Proposed strengthened theorem.** \(f(4)\ge49\). Equivalently, no tournament on 48 vertices satisfies \(S_4\).

The proof reduces a hypothetical 48-vertex tournament to one of **37 published doubly regular tournament classes** on 23 vertices. A complete independent program verifies that 35 classes violate \(S_3\); for the two remaining classes, there are respectively **2,475** and **2,530** internally undominated 4-sets, while each admissible outside vertex can dominate at most **65** or **66** of these. At most 24 outside vertices exist, so \(24\times66=1,584<2,475\).

The classification (37 nonisomorphic classes) is published by Spence/McKay and independently tabulated by Al-Azemi (2012); it is a **named external mathematical theorem**, not something this finite code claims to prove from scratch. This pack does independently establish that its own 37 valid DRT representatives are pairwise nonisomorphic, which combined with the published count implies they exhaust the classes.

## Hand proof of the structural reduction

For vertex \(v\), let \(I(v)=\{u:u\to v\}\). A subset \(D\) is *dominating* when every vertex outside \(D\) is beaten by at least one member of \(D\). By reversing the all-versus-one quantifier, \(D\) is dominating if and only if **no** outside vertex beats every member of \(D\). Consequently \(S_4\) implies no dominating set of size at most four (extend a smaller such set to four).

1. **Triple in-neighborhoods contain at least five vertices.** Let \(a,b,c\) be arbitrary vertices and \(R=I(a)\cap I(b)\cap I(c)\). Suppose \(x\notin R\) beats every vertex of \(R\). Then \(\{a,b,c,x\}\) dominates the tournament: vertices in \(R\) lose to \(x\), and vertices outside \(R\) lose to one of \(a,b,c\). This contradicts \(S_4\). Thus no vertex outside \(R\) beats all of \(R\), so \(R\) is itself dominating and \(|R|\ge5\).
2. **Pair in-neighborhoods have at least 11 vertices.** In \(K=I(a)\cap I(b)\), every vertex \(c\in K\) has at least five in-neighbors inside \(K\) by step 1. Average in-degree in a tournament on \(|K|\) vertices equals \((|K|-1)/2\), so \(|K|\ge11\).
3. **Each vertex has in-degree at least 23.** In \(H=I(a)\), every \(b\in H\) has at least 11 in-neighbors in \(H\) by step 2. Hence \(|H|\ge23\).
4. **A 48-vertex counterexample has a 23-vertex doubly regular core.** The average in-degree on at most 48 vertices is at most \(23.5\), so some vertex \(v\) has in-degree exactly 23. Let \(H=I(v)\). Each vertex of \(H\) has internal in-degree at least 11, and the average equals 11, hence exactly 11. Likewise each 11-vertex common-in-neighborhood \(I(v)\cap I(h)\), \(h\in H\), has internal in-degree exactly 5 by the triple bound. Thus every pair in \(H\) has exactly five common in-neighbors, and \(H\) is a \(\mathrm{DRT}(23,11,5)\). Moreover \(H\) has \(S_3\): apply \(S_4\) to \(\{v\}\cup S\) for any three-subset \(S\subset H\); the dominator beats \(v\) and therefore lies in \(H\).
5. **Outside vertices have constrained masks.** For each \(x\) such that \(v\to x\), write \(W_x=\{h\in H:x\to h\}\). For any \(h\in H\), the set \(K_h=\{u\in H:u\to h\}\) has size 11. The triple bound on \((v,x,h)\) implies at least five vertices of \(K_h\) beat \(x\); therefore \(|W_x\cap K_h|\le6\). Summing over all \(h\) gives \(11|W_x|\le23\cdot6=138\), so \(|W_x|\le12\).
6. **The finite obstruction.** Call a 4-subset of \(H\) *bad* if no vertex inside \(H\) beats all four. Every such subset must be dominated by some vertex outside \(H\), because the full tournament has \(S_4\). That vertex cannot be \(v\) (each vertex of \(H\) beats \(v\)), hence is among the at most 24 vertices \(x\) with \(v\to x\). Each such \(x\) has a mask \(W_x\) constrained as in step 5. By the finite certificate below, the two possible \(S_3\) cores have at least 2,475 bad 4-sets and each admissible mask contains at most 66 bad 4-sets. The maximum union coverage is thus \(24\cdot66=1,584\), strictly smaller than 2,475. Contradiction.

This proves the proposed \(f(4)\ge49\) bound using the complete published DRT23 classification and the independently verifiable finite certificate.

## Finite certificate and catalogue completeness

The 37 rows in `drtourn23.txt` contain 253 orientation bits per row (one bit for each unordered pair). Original source data SHA-256:

```
20dbad06e128f968e87ce5bec9ca3128b8d2e9a9f25152b29d82c48c967b45d0
```

The independent C++ audit computes rather than imports its conclusions:

| Test | Result |
|---|---:|
| Catalog entries | 37 |
| Entries satisfying out-degree 11 and common out-degree 5 | 37 / 37 |
| Representatives satisfying \(S_3\) | Rows 35 and 36 only |
| Row 35: bad 4-subsets | 2,475 |
| Row 36: bad 4-subsets | 2,530 |
| Row 35: exact maximum over all admissible masks | 65 |
| Row 36: exact maximum over all admissible masks | 66 |
| Row 35: admissible masks | 1,153,310 |
| Row 36: admissible masks | 1,152,232 |
| Six-vertex subtournament class-profile signatures | 35 distinct signatures, two collisions |
| Two remaining collision pairs | 1 vs 35 and 26 vs 37 |
| Eight-vertex out-degree-sequence profiles distinguish each remaining pair | Yes |
| Independent exact upper-bound control: Paley \(P_{67}\) | 766,480 / 766,480 4-sets dominated |
| Mutated orientation in catalogue | Rejected |

The 6-vertex signatures are histograms over all 56 isomorphism classes of 6-vertex tournaments, with each class constructed by exhaustively relabeling the \(2^{15}\) possible edge patterns. Since isomorphic 23-vertex tournaments must share those signatures, 35 distinct signatures prove 35 distinct classes. The two collision pairs are independently separated by different histograms of degree sequences among all \(\binom{23}{8}\) induced 8-vertex subtournaments. Therefore all **37** representative rows are pairwise nonisomorphic. The established published theorem that there are exactly 37 such classes completes the exhaustive reduction.

For each survivor, the independent code enumerates all \(\binom{23}{4}=8,855\) 4-sets to mark internally undominated sets; computes a subset-zeta transform over \(2^{23}=8,388,608\) bitmasks; then, independently of the original DFS implementation, exhaustively checks every 23-bit mask satisfying \(|W|\le12\) and \(|W\cap K_h|\le6\) for every \(h\). No floating-point arithmetic or statistical confidence claim is used.

## Reproduce in one command

Requires Python 3, a C++17 compiler (`g++`), and approximately 32 MB RAM for the main zeta transform. From this folder:

```bash
python verify_all.py
```

The script recompiles its own independent checkers in a temporary directory, verifies the source data hash, checks the catalogue and two survivors, checks distinctness signatures, independently reproduces the known Paley67 positive control, mutates the catalogue and verifies rejection, and prints PASS or raises an error. It writes an immutable-like dated JSON receipt in the proof folder.

## Publication/verification boundary

- **Mathematical status:** a complete *written proof* conditional only on an established published classification, with exact independently reproduced finite arithmetic. The original `F4Struct.lean` builds the structural contradiction conditional on `hExt`; an **unconditional end-to-end Lean theorem has not been kernel-checked**. A proof by ordinary mathematical standards may use published classification results, but specialist review of the reduction and source correspondence is still required.
- **Novelty:** the available 2026 Erdős database and 2004 literature still cite 48 as the best lower bound. This is a potentially new *finite bound* rather than resolution of the asymptotic Erdős #902 question. A detailed prior-art search and external specialist assessment are needed before declaring a new record.
- **Evidence provenance:** the candidate bound and source DRT rows were already in Jared Wilder's public repository before this independent audit. The November 13 audit independently recomputed the finite mathematics and removed the **data-file trust dependency** by distinguishing all 37 rows and invoking the published number of classes.

### Bibliography

- K. B. Reid, A. A. McRae, S. M. Hedetniemi, S. T. Hedetniemi, *Domination and irredundance in tournaments*, Australasian Journal of Combinatorics **29** (2004), 157–172 (published bound \(f(4)\ge48\)).
- E. Spence, *Classification of Hadamard matrices of order 24 and 28*, Discrete Mathematics **140** (1995), 185–243. DRT23 enumeration is equivalent to the relevant skew-Hadamard classification.
- A. Al-Azemi, *Classification of regular digraphs, normally regular digraphs, and strongly regular digraphs*, International Journal of Pure and Applied Mathematics **78** (2012), Table 4: exactly 37 DRT(23,11,5) classes.
- Brendan McKay, *Combinatorial Data*, [doubly regular tournaments](https://users.cecs.anu.edu.au/~bdm/data/digraphs.html), public 23-vertex representatives.
- T. F. Bloom, [Erdős problem #902](https://www.erdosproblems.com/902).
- J. Wilder, [original candidate and conditional Lean proof](https://github.com/jaredwilder/erdos902-tournament-f4).