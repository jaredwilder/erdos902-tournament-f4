# Erdős #902 — finite structure at `f(4)`

A finite/computational program around the lower bound for Schütte's tournament function `f(4)`, together with Lean formalizations of the structural reductions used near the 48-vertex boundary.

Reid, McRae, Hedetniemi and Hedetniemi proved

\[
f(4)\ge48.
\]

This repository develops a candidate strengthening to

\[
\boxed{f(4)\ge49}
\]

whose remaining external dependency is completeness of the cited McKay–Spence tournament classification used in the final finite reduction.

## Finite capacity calculation

The central repair-capacity computation gives

```text
ADMISSIBLE_REPAIR_CAPACITY = 66.
```

The decisive inequalities are

\[
24\cdot66=1584<2475
\]

and

\[
25\cdot66=1650<2475.
\]

The first is the global capacity comparison; the second excludes the indegree-23 endpoint in the relevant reduction.

Replay:

```bash
python speaker-package/verify_real_002.py
```

## Lean structural theorem

[`structural-proof/`](structural-proof/) packages the 4–48-vertex exclusion as one Lean theorem conditional on a single named input about the two surviving `DRT(23,11,5)` classes.

The same folder contains 35 finite certificates eliminating the other classes used by the reduction.

## Formalized surrounding structure

The repository also contains:

- `kernel/` — `F4Seal`, `F4Rows`, `F4Catalogue`, and `F4SealPlus`, with hashes and axiom reports;
- `press/f4_bridge.lean` — covering, mass/deficit, and pigeonhole lemmas reducing to indegree at most 23;
- `press/m19_kill.lean` — exclusion of the indegree-19 case using order-19 doubly regular tournaments and

  \[
  28\cdot51=1428<1653;
  \]

- `lean-proofs/` — 25 Lean files with roughly 150 theorems and no `sorry`, including `f(3)>=19` and regularity statements at the finite boundary.

## Remaining middle indegrees

For a hypothetical 48-vertex `S_4` tournament, the minimum indegree lies in

\[
\{19,20,21,22,23\}.
\]

The endpoint cases 19 and 23 are eliminated by the current structure. The middle cases `20,21,22` are the remaining finite layer for the same approach; they lack the endpoint rigidity used in the current proofs.

## Relation to the main #902 repository

The broader theorem package—classical asymptotic bounds, exact `f(1),f(2)`, QR67, DRT23 structure, dominator cubes, and other reductions—is collected in [`erdos902`](https://github.com/jaredwilder/erdos902).

The candidate `f(4)>=49` statement in this repository should be read with the stated catalogue-completeness dependency; the finite capacity calculations and Lean lemmas are independently checkable at their displayed scopes.

Author: Jared Wilder. License: Apache-2.0.
