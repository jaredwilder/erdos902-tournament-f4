# S3-REJECTION LAYER — closes DRT(23,11,5) + S3 => row 35 or row 36

`f4_finite.lean` proves rows 35/36 HAVE S3. It never showed the other 35 catalogue rows
FAIL S3, so "H is a DRT with S3" did not pin H to the two surviving classes. Gap found
2026-08-31 in external review; closed here.

Each rejected row carries one explicit nondominated triple (a 3-set with no dominator),
refuting S3 for that row. 35 witnesses, no classification computation.

## Status
- `F4Reject.lean` compiles under Lean 4.31.0-rc1, exit 0, ~4s. No Mathlib needed.
- `all_rejects_valid` + count/distinctness/avoidance: axioms = [propext] ONLY.
  Pure kernel. Strictly stronger trust than the native_decide tier of f4_finite.lean.
- Only the two survivor S3 re-checks use native_decide.
- NEGATIVE CONTROL: corrupting one certificate makes `decide` prove the statement FALSE
  and compilation fail. The gate discriminates; it is not a green light by construction.
- Decode self-check: catalogue[34]/[35] reproduce f4_finite.lean's own row35/row36 literals.

## Non-vacuity
`rejects_count = 35`, `rejects_distinct` (35 distinct row indices), and
`rejects_avoid_survivors` (no index is 34 or 35) together force the 35 certificates to
cover exactly the 35 non-surviving rows. Without these `.all` over an empty list is true.

## STILL OPEN (not closed here)
1. Lean seal of the Reid Prop-14 structural bridge + admissible-mask derivation.
2. Lean seal of isomorphism transport (bad4 / admissibility / repair / capacity invariance).
   Currently only sampled by random relabeling — evidence, NOT a theorem.
3. H2: completeness of the 37 DRT(23,11,5) classes. External (McKay/Spence), cited.
4. `native_decide` compiler trust boundary on f4_finite.lean.

## STALE HEADERS to fix in the drop (documentation, not mathematics)
- f4_finite.lean header says the capacity 66 "remains Python-replicated only"; the same
  file now proves capacity_row35/36 by native_decide.
- f4_reduction.lean header describes the finite facts as "not yet Lean" for the same reason.
