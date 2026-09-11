import Mathlib

/-!
THE ARITHMETIC SHELL of the f(4) >= 49 candidate - kernel-sealed. 2026-08-31.

The candidate's chain has three layers:
  (1) our pre-existing kernel-checked structural reduction (48-vertex S4 -> 23-vertex DRT core
      + admissible masks) - ALREADY Lean;
  (2) the finite catalogue computations (37 DRTs, rows 35/36, capacity 66, bad-set counts) -
      replicated in Python, kernel closure pending on the box;
  (3) the closing ARITHMETIC - sealed HERE, so the only open layer left is (2).

Everything below is proved. No sorry. `decide`-clean footprint.
-/

namespace F4Shell

/-- Layer 3a - THE 48-KILLER: 24 outside vertices at global repair capacity 66 cannot repair
    the 2475 bad 4-sets of the smaller core. -/
theorem repair_deficit_48 : 24 * 66 < 2475 := by norm_num

/-- ...and the larger core is further out of reach. -/
theorem repair_deficit_48' : 24 * 66 < 2530 := by norm_num

/-- Layer 3b - THE ORDER-49 BRANCH-KILLER: even 25 outside vertices cannot repair either
    core. This is the arithmetic that deletes the indegree-23 branch (5.37 CPU-hours of
    unresolved search, ended by one inequality). -/
theorem repair_deficit_49_branch : 25 * 66 < 2475 := by norm_num

/-- Layer 3c - REGULARITY FORCING, in full generality: if every vertex of a 49-vertex
    tournament has indegree at least 24 and total indegree is C(49,2) = 1176, then every
    vertex has indegree EXACTLY 24. The "attain the average" step, kernel-proved. -/
theorem regularity_forced (f : Fin 49 → ℕ)
    (hmin : ∀ v, 24 ≤ f v)
    (hsum : Finset.univ.sum f = 1176) :
    ∀ v, f v = 24 := by
  by_contra hne
  push_neg at hne
  obtain ⟨v, hv⟩ := hne
  have hv25 : 25 ≤ f v := lt_of_le_of_ne (hmin v) (Ne.symm hv)
  have h1 : Finset.univ.sum f = f v + (Finset.univ.erase v).sum f := by
    rw [Finset.add_sum_erase _ f (Finset.mem_univ v)]
  have h2 : 48 * 24 ≤ (Finset.univ.erase v).sum f := by
    have hc := Finset.card_nsmul_le_sum (Finset.univ.erase v) f 24 (fun i _ => hmin i)
    have he : (Finset.univ.erase v).card = 48 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ v)]
      simp
    rw [he, smul_eq_mul] at hc
    exact hc
  omega

/-- Layer 3d - SLACK-FLOW's global closures, exact: the pair-to-triple and triple-to-quad
    conservation identities land on the digit for the 24-regular 49-vertex survivor. -/
theorem slack_flow_closure_pair_triple :
    3 * 7056 = Nat.choose 49 2 * 7 + 22 * 588 := by
  norm_num [Nat.choose]

theorem slack_flow_closure_triple_quad :
    4 * 308798 = Nat.choose 49 3 * 59 + 21 * 7056 := by
  norm_num [Nat.choose]

end F4Shell
