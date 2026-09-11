import Mathlib

/-!
THE GENERIC REDUCTION for f(4) >= 49, kernel-sealed as a CONDITIONAL theorem. 2026-08-31.

⛔ HONESTY HEADER. This does NOT prove f(4) >= 49 outright. It proves the COMBINATORIAL CORE of
the candidate argument, with the two finite/external facts as explicit hypotheses:
  (H_cap)  every outside vertex repairs at most 66 bad 4-sets;
  (H_cov)  every bad 4-set is repaired by some outside vertex (so badCount <= sum of repairs);
  (H_bad)  the core has at least 2475 bad 4-sets.
Given those, `no_order_48_core` derives False from |O| = 24. What remains OUTSIDE the kernel:
H_cap and H_bad are the FINITE COMPUTATION (Python-replicated, not yet Lean), and the reduction
of a real 48-vertex S4 tournament to this shape is the DRT-23 bridge (also not yet Lean). This
file is the connective tissue between those, made real.
-/

namespace F4Reduction

open Finset

/-- The counting contradiction at order 48. `O` is the set of 24 outside vertices; `repair x`
    is how many bad 4-sets vertex `x` can fix; `badCount` is the number that must be fixed.
    If each repairs <= 66, all are covered, and there are >= 2475, that is impossible. -/
theorem no_order_48_core {α : Type*} (O : Finset α) (repair : α → ℕ) (badCount : ℕ)
    (hO : O.card = 24)
    (hcap : ∀ x ∈ O, repair x ≤ 66)
    (hcov : badCount ≤ ∑ x ∈ O, repair x)
    (hbad : 2475 ≤ badCount) :
    False := by
  have hsum : ∑ x ∈ O, repair x ≤ 24 * 66 := by
    calc ∑ x ∈ O, repair x ≤ ∑ _x ∈ O, 66 := Finset.sum_le_sum hcap
      _ = O.card * 66 := by rw [Finset.sum_const, smul_eq_mul]
      _ = 24 * 66 := by rw [hO]
  omega

/-- The order-49 indegree-23 branch dies the same way, with 25 outside vertices instead of 24.
    This is the arithmetic that deletes the 5.37-CPU-hour branch. -/
theorem no_order_49_indeg23_core {α : Type*} (O : Finset α) (repair : α → ℕ) (badCount : ℕ)
    (hO : O.card = 25)
    (hcap : ∀ x ∈ O, repair x ≤ 66)
    (hcov : badCount ≤ ∑ x ∈ O, repair x)
    (hbad : 2475 ≤ badCount) :
    False := by
  have hsum : ∑ x ∈ O, repair x ≤ 25 * 66 := by
    calc ∑ x ∈ O, repair x ≤ ∑ _x ∈ O, 66 := Finset.sum_le_sum hcap
      _ = O.card * 66 := by rw [Finset.sum_const, smul_eq_mul]
      _ = 25 * 66 := by rw [hO]
  omega

/-- REGULARITY FORCING, generic: a 49-vertex tournament whose every indegree is >= 24 and whose
    indegrees sum to C(49,2) = 1176 is 24-regular. (Every vertex must attain the average.) -/
theorem order49_regular_core {α : Type*} [DecidableEq α] (V : Finset α) (indeg : α → ℕ)
    (hV : V.card = 49)
    (hmin : ∀ v ∈ V, 24 ≤ indeg v)
    (hsum : ∑ v ∈ V, indeg v = 1176) :
    ∀ v ∈ V, indeg v = 24 := by
  intro v hv
  by_contra hne
  have hv25 : 25 ≤ indeg v := lt_of_le_of_ne (hmin v hv) (fun h => hne h.symm)
  have hsplit : ∑ w ∈ V, indeg w = indeg v + ∑ w ∈ V.erase v, indeg w :=
    (Finset.add_sum_erase V indeg hv).symm
  have hrest : ∑ w ∈ V.erase v, indeg w ≥ 48 * 24 := by
    calc ∑ w ∈ V.erase v, indeg w ≥ ∑ _w ∈ V.erase v, 24 :=
          Finset.sum_le_sum (fun w hw => hmin w (Finset.mem_of_mem_erase hw))
      _ = (V.erase v).card * 24 := by rw [Finset.sum_const, smul_eq_mul]
      _ = 48 * 24 := by rw [Finset.card_erase_of_mem hv, hV]
  omega


/-- ⭐ THE CHAIN, wired inside Lean: IF a hypothetical order-48 S4 tournament yields (per the
    DRT-23 bridge, the one remaining unformalized step) a core whose bad count is one of the
    kernel-sealed values {2475, 2530} and 24 outside vertices whose repair function is bounded
    by the kernel-sealed capacity 66 and covers all bad sets - THEN False. Every NUMBER here is
    now a Lean fact (f4_finite.lean); only the structural bridge and the cited catalogue
    completeness remain outside. -/
theorem no_order_48_with_sealed_numbers {α : Type*} (O : Finset α) (repair : α → ℕ)
    (badCount : ℕ)
    (hO : O.card = 24)
    (hcap : ∀ x ∈ O, repair x ≤ 66)
    (hcov : badCount ≤ ∑ x ∈ O, repair x)
    (hbad : badCount = 2475 ∨ badCount = 2530) :
    False := by
  rcases hbad with h | h <;>
    exact no_order_48_core O repair badCount hO hcap hcov (by omega)

end F4Reduction
