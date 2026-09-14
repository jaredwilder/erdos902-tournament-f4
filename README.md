# Erdős 902: a candidate improvement for `f(4)`

A computational candidate for improving the published lower bound on the tournament function `f(4)`, together with kernel-checked structural lemmas for the surrounding problem.

Author: Jared Wilder. First public timestamp: 2026-09-10.

## Candidate bound

Reid, McRae, Hedetniemi and Hedetniemi (2004) prove

```text
f(4) >= 48.
```

This repository contains a computational argument for

```text
f(4) >= 49,
```

together with a second candidate consequence: every hypothetical 49-vertex `S_4` tournament is 24-regular.

### Evidence for the candidate

The central finite calculation is independently reproduced by `speaker-package/verify_real_002.py`, which reports the exact global admissible repair capacity **66**.

The counting step is:

```text
24 × 66 = 1584 < 2475,
```

where 2475 is the minimum core requirement. The indegree-23 case is excluded separately by

```text
25 × 66 = 1650 < 2475,
```

and the Szekeres bound supplies the lower indegree constraint.

A load-bearing external dependency remains: completeness of the 37 relevant tournament classes from McKay and Spence is cited rather than independently reconstructed here. For that reason the `f(4) >= 49` statement is presented as a **candidate result**, not as a fully sealed theorem.

A literature search found no published `49` lower bound; historical priority should still be checked independently.

## The structural proof in Lean

[`structural-proof/`](structural-proof/) has the whole argument as one Lean theorem. It shows that no S4 tournament has 4 to 48 vertices, assuming a single named input about the two surviving DRT(23,11,5) classes. The folder also has the 35 certificates that knock out the other classes.

## Kernel-checked mathematics in the repository

The candidate sits inside a larger body of formal work:

- `kernel/` — `F4Seal`, `F4Rows`, `F4Catalogue`, and `F4SealPlus`, with axiom footprints, hashes and verification logs replicated across two Mathlib environments;
- `press/f4_bridge.lean` — seven theorems from `S_4` and tournament axioms, including the covering lemma, counting corollaries, mass/deficit bounds, and the pigeonhole step producing an indegree at most 23;
- `press/m19_kill.lean` — five theorems excluding the indegree-19 case via the order-19 doubly regular tournaments and the exact capacity inequality `28 × 51 = 1428 < 1653`;
- `lean-proofs/` — 25 Lean files, roughly 150 theorems, zero `sorry`, including `f(3) >= 19` and regularity at the relevant extremal boundary.

## Remaining finite cases

For a hypothetical 48-vertex `S_4` tournament, the minimum indegree lies in `{19,20,21,22,23}`.

The current work excludes the endpoint cases `19` and `23`. The middle cases `{20,21,22}` remain the unresolved finite layer for this approach. Their cores are not extremal in the same way, so the rigidity used at the endpoints is unavailable; in particular, order 21 cannot be doubly regular because doubly regular tournaments have order `3 mod 4`.

That identifies the next mathematical task cleanly: replace endpoint rigidity with a structural argument that also controls the three middle indegrees.

## Reproduce the finite calculation

```bash
python speaker-package/verify_real_002.py
```

The script should exit successfully and report `ADMISSIBLE_REPAIR_CAPACITY = 66`.

## License

Apache-2.0.