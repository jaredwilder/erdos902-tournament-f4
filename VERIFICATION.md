# Re-run of the verifier, 2026-09-10

`speaker-package/verify_real_002.py` was run from committed source on 2026-09-10, hours after this
repository was made public. It exits **0** with `"verdict": "PASS"`.

## What it reproduces

| quantity | value |
|---|---|
| admissible global repair capacity | **66** |
| minimum core need (`bad4`) | **2475** |
| order-48 total repair capacity | **1584** |
| order-49 indegree-23 branch capacity | **1650** |
| order-49 structure if S4 | **24-regular** |

## The arithmetic, checked independently of the verifier

```
24 rows x 66 capacity = 1584   <  2475   margin 891
25 rows x 66 capacity = 1650   <  2475   margin 825   -> indegree-23 branch IMPOSSIBLE
```

Both inequalities are strict, and both were recomputed here rather than read out of the receipt.

## The boundary is in the receipt's own field name

The receipt does not emit a field called `f4_ge_49`. It emits

```
"f4_ge_49_given_catalogue_completeness": true
```

That conditional is the honest statement of what this establishes. The argument consumes the
McKay-Spence classification of the 37 doubly-regular tournament classes as an external input. That
classification is **cited, not re-derived here**, and if it were incomplete the conclusion would not
follow.

## What this is and is not

It **is** a reproduction: the committed code runs, exits 0, and produces the numbers this
repository claims.

It is **not** a proof. The result is Python-replicated and **not kernel-sealed**. It stands against
a published record of 48 (Reid, McRae, Hedetniemi and Hedetniemi, 2004). A candidate that
contradicts a published record deserves more scepticism than its author can supply, and this one has
not had it. If f(4) >= 49 is already known, or if the argument has a gap, the right outcome is that
this repository is corrected or withdrawn, and that is offered in advance rather than defended.
