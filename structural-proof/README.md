# f(4) ≥ 49: the structural argument in Lean

The front page of this repo describes f(4) ≥ 49 as a computational candidate. This folder holds the Lean version of the argument. A tournament has property S4 if every set of 4 vertices is beaten by some single vertex outside the set.

**`F4.no_S4_of_card_le_48`** (in `F4Struct.lean`): no tournament with property S4 has between 4 and 48 vertices, **given one named input, `hExt`**.

It builds in about 3 seconds on Lean 4 v4.31.0-rc1 with Mathlib, using only the standard axioms, with no `sorry` and no `native_decide`.

## How the proof goes

Assume S4 and at most 48 vertices. Then:

1. Every triple has at least 5 common in-neighbours, every pair at least 11, and every vertex has in-degree at least 23.
2. With 48 or fewer vertices, some vertex has in-degree exactly 23.
3. The counts are tight, and that forces the 23 in-neighbours of that vertex to form a doubly regular tournament DRT(23,11,5) with property S3.
4. Each outside vertex can repair only a limited number of the core's "bad" 4-sets, and the repairs have to cover all of them. There aren't enough outside vertices, so the configuration is impossible.

The argument also rules out 47 vertices directly, without the Reid–Brown theorem the published proof uses for that step.

## The one outside input

`hExt` says two things about a DRT(23,11,5) core with S3: it has at least 2475 bad 4-sets, and any single outside vertex repairs at most 66 of them. Then 24 × 66 = 1584 < 2475 finishes it.

Removing `hExt` needs:
- the published classification of DRT(23,11,5) into 37 classes (McKay/Spence), which is cited here, not reproved;
- the finite computation on the two classes that survive. It's done in `kernel/` using `native_decide`, and reproduced in Python.

`F4Reject.lean` handles the other 35 classes. For each one it gives an explicit triple with no common dominator, so that class fails S3. It depends on `propext` only.

## The other files

- `F4Cap35.lean`, `F4CapT35.lean`, `genbv*.py`: an attempt to prove the "at most 66" capacity for class 35 with `bv_decide` instead of `native_decide`. The encoding elaborates, but the SAT solve did not finish on a 7.8 GB machine. See `notes/BVDECIDE-ATTEMPT.md`. It will likely go through with more RAM.
- `F4Neg_*.lean`: mutation checks. Changing 2475, 66 or 48 makes the build fail, so each number actually matters.
- `F4Ax.lean`, `probe*.lean`, `notes/HEXT-BLOCKER.md`: work toward removing `hExt` entirely.
- `f4receipt.txt`: the build receipt, with file hashes and the axiom list.
- `s3_certificates.json`: the 35 rejection witnesses.
