# hExt CLOSURE ATTEMPT — MEASURED BLOCKER

Mission: eliminate `hExt` by wiring H2 + the 37-row catalogue + the 35 rejection certificates
+ transport into an arbitrary-core finite theorem.

`hExt` has two halves. They do NOT have the same status.

## HALF 1 — badCount >= 2475 : ABSTRACTLY DECIDABLE (probe.lean)

    theorem probe_bad : (F4.badSets R35 (univ : Finset (Fin 23))).card = 2475 := by native_decide
    -> EXIT 0, wall 4.87s, maxrss 6.5 GB

The abstract `F4.badSets` over `Finset (Fin 23)` decides directly. No encoding bridge needed.
C(23,4) = 8855 subsets is well inside range.

## HALF 2 — capacity <= 66 : NOT ABSTRACTLY DECIDABLE. THIS IS THE BLOCKER.

The bound quantifies over ALL subsets of the core (2^23 = 8,388,608), not over 4-subsets.

Measured, both on this machine (WSL, 7 GB RAM):

| formulation | result |
|---|---|
| `∀ W : Finset (Fin 23), Adm W → repairOf W ≤ 65` (probe2.lean) | TIMEOUT at 420s (24 GB ulimit) |
| bitmask `Nat` reformulation, 8.4M masks (probe3.lean) | TIMEOUT at 540s |
| `F4Finite.maxRepair row35 = 65` (drop's own, zeta+DFS) | **EXIT 0, wall 173.68s, maxrss 6.85 GB** |

The efficient computation DOES exist and IS kernel-accepted:
  F4Finite.capacity_row35 : [propext, native_decide.ax]
  F4Finite.capacity_row36 : [propext, native_decide.ax]

## EXACT BLOCKER

There is no verified bridge from `F4Finite.maxRepair` (List Nat / Array bit encoding, a
subset-sum "zeta" transform plus a pruned DFS over admissible masks) to the abstract
`repairOf` over `Finset (Fin 23)`.

Closing it requires two proofs that do not exist in this estate:
 1. ZETA CORRECTNESS: `zeta[m] = #{b ∈ badMasks : b &&& m == b}` after the 23-round in-place
    transform — an invariant proof over mutable `Array` loops.
 2. DFS COMPLETENESS: the pruned DFS enumerates EXACTLY the masks satisfying
    `|W| ≤ 12 ∧ ∀ h, |W ∩ I_H(h)| ≤ 6`, and returns the max of `zeta` over them.

Plus the encoding bijection `Finset (Fin 23) ↔ Nat` with `s ⊆ W ↔ toMask s &&& toMask W = toMask s`.

This is NOT a provenance gap and NOT a mathematical gap. It is an unwritten verified-bitset
formalization. Brute force is ruled out by measurement, not by assumption: the abstract form
needs ~2.8e9 boxed-Nat operations and does not finish.

## NOT ATTEMPTED, and therefore NOT claimed
- subtype transport (V, T, H) <-> (Fin 23, R, univ). The existing transport theorems assume a
  FULL-type equivalence `V ≃ W`; the core is a 23-subset of a 48-element type, so they do not
  apply as stated. Generalizing them to `Set.InjOn` is required and was not done.
- the H2 axiom has not been stated in Lean.
