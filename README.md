# erdos902-tournament-f4

Work on Erdos problem 902 and the domination number of score-sequence-constrained tournaments,
including a **candidate improvement to the published lower bound on f(4)**.

Author: Jared Wilder. First public timestamp: 2026-09-10.

## The candidate result, stated with its exact status

The published record is **f(4) >= 48**, Reid, McRae, Hedetniemi and Hedetniemi (2004), Corollary 7.

This repository contains a computational argument for **f(4) >= 49**, together with a second
candidate: **every hypothetical 49-vertex S4 tournament is 24-regular.**

**Status, precisely:**

- The argument is **replicated in Python, not sealed in Lean.** Run
  `speaker-package/verify_real_002.py`. It exits 0, prints `"verdict": "PASS"`, and reports the
  exact global `ADMISSIBLE_REPAIR_CAPACITY` of **66**, obtained by sweeping all admissible masks
  per core. Confirmed reproducing 2026-09-10.
- The counting argument: 24 x 66 = 1584 < 2475, the minimum core need. Margin 891. The
  indegree-23 branch dies separately because 25 x 66 = 1650 < 2475, and Szekeres gives
  indegree >= 23, so equality is forced.
- **McKay and Spence's 37-class completeness is CITED, not re-derived here.** The argument
  depends on it.
- A novelty search found no published 49. That is the author's search, not an adjudicated
  novelty claim. **If this is known, the correct response is an issue on this repository and the
  claim is withdrawn.**

Because it is not kernel-sealed, treat `f(4) >= 49` as a **candidate**, not a theorem.

## What IS kernel-verified here

- `kernel/` - F4Seal, F4Rows, F4Catalogue, F4SealPlus, with axiom footprints, shas and
  verification logs, replicated across two independent Mathlib kernels.
- `press/f4_bridge.lean` - 7 theorems from S4 and tournament axioms: the covered lemma, a
  counting corollary, a double count, mass >= 276, deficit <= 12, and the pigeonhole giving
  an indegree <= 23.
- `press/m19_kill.lean` - 5 theorems killing the m = 19 branch: McKay's DRT(19) has exactly two
  rows, one carries S3, bad4 = 1653, admissible capacity 51, and 28 x 51 = 1428 < 1653.
- `lean-proofs/` - 25 Lean files on Erdos 902, roughly 150 theorems, zero sorries, including
  f(3) >= 19 tight via Szekeres and the regular-at-bound rigidity result.

## The open surface, stated plainly

The minimum indegree of a 48-vertex S4 tournament lies in {19, ..., 23}. The m = 19 and m = 23
branches are killed. **m in {20, 21, 22} remains open and needs a new weapon**: those cores are
non-extremal so there is no rigidity to exploit, and order 21 cannot be doubly regular at all,
since DRTs exist only at orders 3 mod 4. The catalogue-and-capacity method jams there by
construction.

## License

Apache-2.0.
