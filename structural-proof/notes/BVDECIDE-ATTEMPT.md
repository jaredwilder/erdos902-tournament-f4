# CAPACITY BRIDGE via bv_decide — BLOCKED (measured)

Question lock: oracle/ledger/question-locks/f4-capacity-bv.json (budget 3600s, NOT a proxy —
admissibility stated with ONLY the per-vertex <=6 condition, no |W|<=12 conjunct, which is
STRICTLY STRONGER than the drop's family and is what F4Struct.mask_admissible actually proves).

Target: `∀ w : BitVec 23, adm_row35 w = true → (repair_row35 w).ult 67 = true`
2475 indicator terms (row35) / 2530 (row36), 23 admissibility conjuncts, 23 free SAT variables.

## What worked
- bv_decide + CaDiCaL are present and functional. Toy analogue (3 terms): PASS 6.66s.
- Dropping Mathlib cut import cost; `import Std.Tactic.BVDecide` suffices.
- Definitions must be `unfold`ed or bv_decide abstracts them as unconstrained SAT variables
  (observed and fixed).
- maxRecDepth 4000000 + maxHeartbeats 0 required to elaborate the 2475-term expression.

## What blocked — THREE independent encodings, all measured on this machine (WSL, 7.8 GB)
| encoding | result |
|---|---|
| ripple chain, 2475 twelve-bit adders | elaborates (1.1 GB), SAT UNRESOLVED at 480s, still running at 540s |
| balanced adder tree, minimal widths | **OOM-KILLED (signal 9) at 7.27 GB, 469.94s** — died in elaboration, never reached SAT |
| (earlier) Finset (Fin 23) native_decide | TIMEOUT 420s |
| (earlier) Nat bitmask native_decide | TIMEOUT 540s |

The balanced tree — the standard fix for SAT cardinality counting — is the one that should have
helped, and it is precisely the one that exhausts RAM during Lean elaboration (deep nesting over
many distinct BitVec widths). The memory-cheap encoding is the SAT-hard one. That is the bind.

## Status of each handoff deliverable
- ROW35_BV: not closed (SAT unresolved within budget on the only encoding that fits in RAM)
- ROW36_BV: NOT ATTEMPTED (row35 did not close; running it would burn the machine for nothing)
- ROW36 NEGATIVE CONTROL (<66 must fail): NOT ATTEMPTED, same reason
- LRAT: none produced
- SEMANTIC BRIDGE (encode : Finset (Fin 23) → BitVec 23, 6 lemmas): NOT WRITTEN — it is
  downstream of a theorem that does not exist yet

## Honest read
This is a RESOURCE blocker, not a mathematical one. 23 free variables is small; the obstruction
is that the counting network is large and this box has 7.8 GB. The next thing to try is a machine
with more RAM (the balanced tree likely elaborates fine at 32 GB), or the DIMACS fallback where
the circuit is emitted directly rather than built as a Lean term — that sidesteps Lean
elaboration entirely, which is what actually died.

NOTHING in Jobs 1-3 was reopened or changed by this attempt.
