/-
Erdos 902 -- KERNEL AUDIT OF THE SUBMITTED PROOF ("f(k) = O(k 2^k)" drop).

The drop names its own kill point:

    "Formalize the following implication first: the charge from (2) can be reduced from 8k^2
     to 8k ... That factor-k cancellation is the entire proposed solution."

So that is what is put on the kernel here.  Every quantity of the drop is carried as an opaque
natural number, and only the drop's OWN inequality chain (2)-(5) is asserted.  Nothing about
tournaments is assumed, so nothing about tournaments is smuggled in.  Only the drop's own inequality chain
(2)-(5) is asserted.

  sumDelta  = sum over deficient k-sets of delta_D(A)          (the drop's  sum_A delta_D(A))
  N / 2^(k+1)  = the repair mass coefficient of (3)
  8*k*k     = the upward charge of (2), as the drop derives it
  8*k       = the upward charge of (5), the ASSERTED sharpening

THE THREE RESULTS:
  1. drop_closes_given_sharpening -- granting (5), the contradiction really does follow.
     The arithmetic of the drop is VALID.  The proof is not broken downstream of (5).
  2. sharpening_is_load_bearing   -- withOUT (5), at the drop's own N = 64k2^k, the bracket in
     (4) is NON-NEGATIVE for every k >= 4.  So there is no contradiction and no proof.
     The sharpening is not a refinement; it carries the entire theorem for all k >= 4.
  3. drop_verdict                 -- the two facts side by side: the drop reduces exactly to (5).

(5) IS NOT PROVED HERE, AND THE DROP DOES NOT PROVE IT EITHER.  It is asserted by a charging
sentence ("Charge a destroyed witness to the least difference of A-x under a fixed ordering.
Every destroyed low-reservoir witness is then charged exactly once").  That sentence is the
whole claim.  It appears in this file ONLY as a hypothesis, never as a theorem, which is
exactly the formalization wall.
-/

import Mathlib

namespace Erdos902DropAudit

/-! ### Step A: the drop's N converts to its repair mass -/

/-- The drop takes `N >= 64 k 2^k` and uses `N / 2^(k+1) >= 32k`.  That step is correct,
even with truncated natural division. -/
theorem repair_mass_of_N (k N : Nat) (hN : 64 * k * 2 ^ k <= N) :
    32 * k <= N / 2 ^ (k + 1) := by
  have hpow : 0 < 2 ^ (k + 1) := pow_pos (by norm_num) _
  refine (Nat.le_div_iff_mul_le hpow).mpr ?_
  calc 32 * k * 2 ^ (k + 1) = 64 * k * 2 ^ k := by ring
    _ <= N := hN

/-! ### Step B: GRANTING the sharpening (5), the drop's contradiction follows -/

/-- **The drop's arithmetic is valid downstream of (5).**  With the sharpened charge `8k`
and the repair mass `N / 2^(k+1) >= 32k`, the bracket of (4) is strictly negative whenever
some deficiency exists, which is what the drop needs. -/
theorem drop_closes_given_sharpening (k N sumDelta : Nat)
    (hk : 1 <= k) (hpos : 0 < sumDelta) (hN : 64 * k * 2 ^ k <= N) :
    8 * k * sumDelta < (N / 2 ^ (k + 1)) * sumDelta := by
  have hmass : 32 * k <= N / 2 ^ (k + 1) := repair_mass_of_N k N hN
  have hlt : 8 * k < N / 2 ^ (k + 1) :=
    Nat.lt_of_lt_of_le (by omega) hmass
  exact mul_lt_mul_of_pos_right hlt hpos

/-! ### Step C: WITHOUT the sharpening the proof has no content -/

/-- The drop's own `N = 64 k 2^k` gives repair mass exactly `32k`. -/
theorem repair_mass_exact (k : Nat) : (64 * k * 2 ^ k) / 2 ^ (k + 1) = 32 * k := by
  have hpow : 0 < 2 ^ (k + 1) := pow_pos (by norm_num) _
  rw [show 64 * k * 2 ^ k = 32 * k * 2 ^ (k + 1) by ring, Nat.mul_div_cancel _ hpow]

/-- **THE SHARPENING IS LOAD-BEARING.**  With the drop's UNsharpened charge `8k^2` from (2),
at the drop's own `N = 64 k 2^k`, the upward charge DOMINATES the repair mass for every
`k >= 4`.  The bracket of (4) is then non-negative, the sum is not forced negative, no
sign-pair switch is produced, and the minimality of `D` is not contradicted.

So for all `k >= 4` the drop proves nothing unless (5) holds. -/
theorem sharpening_is_load_bearing (k : Nat) (hk : 4 <= k) :
    (64 * k * 2 ^ k) / 2 ^ (k + 1) <= 8 * k * k := by
  rw [repair_mass_exact k]
  nlinarith [hk]

/-! ### Step D: the verdict -/

/-- **THE AUDIT.**  Both halves at once, for every `k >= 4` and the drop's own `N`:

* granting the asserted sharpening (5), the drop's contradiction follows;
* denying it -- i.e. using only (2), which the drop actually derives -- the bracket is
  non-negative and there is no contradiction.

Hence the drop is EXACTLY as strong as its unproved sharpening, no more and no less. -/
theorem drop_verdict (k sumDelta : Nat) (hk : 4 <= k) (hpos : 0 < sumDelta) :
    -- (5) granted: strict decrease, the proof runs
    (8 * k * sumDelta < ((64 * k * 2 ^ k) / 2 ^ (k + 1)) * sumDelta)
    -- (2) only: the charge dominates, the proof stalls
    /\ ((64 * k * 2 ^ k) / 2 ^ (k + 1) <= 8 * k * k) := by
  constructor
  · exact drop_closes_given_sharpening k (64 * k * 2 ^ k) sumDelta (by omega) hpos (Nat.le_refl _)
  · exact sharpening_is_load_bearing k hk

#print axioms drop_closes_given_sharpening
#print axioms sharpening_is_load_bearing
#print axioms drop_verdict

end Erdos902DropAudit
