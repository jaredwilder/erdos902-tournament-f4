/-
Erdos 902 -- RIGIDITY AT THE RECURSION BOUND.  The extremal case has no freedom left.

Nine closures said where the factor of `n` is not.  Every one of them was an INEQUALITY, and
every one was satisfiable at `N ~ 2^(n+1)`.  This file changes the question: instead of asking
what the inequalities forbid, it asks what happens when the recursion is TIGHT.

The answer is that everything is forced at once.

⭐ REGULARITY (`regular_at_bound`).  If every in-degree is at least `F` and `N = 2F+1`, then
every in-degree is EXACTLY `F`.  The sum of in-degrees is `C(N,2) = (2F+1)F = N*F` -- exactly
the minimum -- so no vertex has a single spare in-neighbour.  The tournament is regular, every
`N-(v)` has exactly `F` vertices, and if `F = f(n-1)` then EVERY in-neighbourhood is an extremal
`S_(n-1)` tournament.  That is the configuration that kills small cases by hand: at `n = 3`,
`N = 15` forces all fifteen in-neighbourhoods to be the Paley tournament on 7 points.

⭐ THE EQUALITY CASE OF THE COUPLING (`reach_eq_internal_indeg`).  In that regular situation,
for every `w` in `N-(v)`:

      |N+(w) cap N+(v)|  =  |N-(w) cap N-(v)|.

A vertex's reach INTO `N+(v)` equals its in-degree INSIDE `N-(v)`, on the nose.  This is
`Erdos902Reach.external_reach_paid_internally` at equality: when the recursion is tight the
inequality has no slack anywhere, and external reach is not merely bought with internal
in-degree, it IS internal in-degree.

Both partitions used are proved here (`outN_card_split`, `inN_card_split`), so the identity is
not an assumption about regular tournaments -- it is forced by `N = 2F+1` alone.

⛔ STILL NOT THE SOLVE, and the reason is again worth recording.  Rigidity gives the identity but
not a contradiction: feeding `b_w = |N-(w) cap N-(v)|` into the external covering law gives
`C(F,n-1) <= sum_w C(b_w, n-1)`, and the `b_w` are the in-degrees of the sub-tournament on
`N-(v)`, so `Erdos902Mass.sum_choose_outdeg_le` applied to its reverse caps that sum by `C(F,n)`.
The result is `C(F,n-1) <= C(F,n)`, i.e. `F >= 2n-1` -- linear, far below `2^(n-1)`.

The pattern across ten rounds is now unmistakable and worth stating plainly: every correction
term this estate can produce has size `exp(n^2/N)`, which tends to 1 the moment `N` reaches
`2^n`, because `n^2` is negligible against `2^n`.  A factor of `n` cannot come from any of them.
Szekeres's argument must produce a correction that is multiplicative in `n` rather than
exponentially small, and nothing of that shape has appeared anywhere in this estate.

TENTH CLOSURE.  What rigidity does give is the right OBJECT: at the bound the tournament is
regular with all in-neighbourhoods extremal and reach determined by internal in-degree.  Any
proof of the Szekeres order has to contradict that specific configuration, and it is now
pinned down exactly rather than described.
-/
import Mathlib
import Erdos902Counting
import Erdos902Reach

open Finset

namespace Erdos902Rigid

variable {V : Type*} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T]

abbrev inN (v : V) : Finset V := Erdos902Cover.inN T v
abbrev outN (v : V) : Finset V := Erdos902Mass.outN T v

theorem mem_inN {v u : V} : u ∈ inN T v ↔ T u v := Erdos902Reach.mem_inN T
theorem mem_outN {v u : V} : u ∈ outN T v ↔ T v u := Erdos902Reach.mem_outN T

/-! ### Regularity is forced -/

/-- The in-degrees sum to `C(N,2)`: every arc is counted once, at its head. -/
theorem sum_indeg (h : IsTournament T) :
    ∑ v : V, (inN T v).card = (Fintype.card V).choose 2 := by
  have hsum : ∑ v : V, (indeg T v + outdeg T v + 1) = Fintype.card V * Fintype.card V := by
    simp only [indeg_add_outdeg_succ T h]
    simp [Finset.card_univ, mul_comm]
  have hsplit : ∑ v : V, (indeg T v + outdeg T v + 1)
      = (∑ v : V, indeg T v) + (∑ v : V, outdeg T v) + Fintype.card V := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp [Finset.card_univ]
  have hswap := sum_indeg_eq_sum_outdeg T
  have hid : ∀ v : V, (inN T v).card = indeg T v := fun v => rfl
  have h2 : 2 * (∑ v : V, indeg T v) + Fintype.card V
      = Fintype.card V * Fintype.card V := by
    rw [← hsum, hsplit, ← hswap]; omega
  have hchoose : (Fintype.card V).choose 2 * 2
      = Fintype.card V * (Fintype.card V - 1) := by
    obtain ⟨r, hr⟩ := Nat.even_mul_pred_self (Fintype.card V)
    rw [Nat.choose_two_right, hr]; omega
  have hpos : Fintype.card V * Fintype.card V
      = Fintype.card V * (Fintype.card V - 1) + Fintype.card V := by
    rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hp
    · simp [h0]
    · have : Fintype.card V - 1 + 1 = Fintype.card V := by omega
      calc Fintype.card V * Fintype.card V
          = Fintype.card V * ((Fintype.card V - 1) + 1) := by rw [this]
        _ = Fintype.card V * (Fintype.card V - 1) + Fintype.card V := by ring
  simp only [hid]
  omega

/-- **REGULARITY IS FORCED.**  At `N = 2F+1` with every in-degree at least `F`, every in-degree
is exactly `F`: the total is exactly `N*F`, so there is no spare arc anywhere. -/
theorem regular_at_bound (h : IsTournament T) (F : ℕ)
    (hmin : ∀ v : V, F ≤ (inN T v).card) (hN : Fintype.card V = 2 * F + 1) (v : V) :
    (inN T v).card = F := by
  have hsum := sum_indeg T h
  have hchoose : (Fintype.card V).choose 2 = Fintype.card V * F := by
    rw [hN, Nat.choose_two_right]
    have h1 : 2 * F + 1 - 1 = 2 * F := by omega
    rw [h1]
    have h2 : (2 * F + 1) * (2 * F) = ((2 * F + 1) * F) * 2 := by ring
    rw [h2, Nat.mul_div_cancel _ (by norm_num)]
  have heq : ∑ _v : V, F = ∑ v : V, (inN T v).card := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, hsum, hchoose, Nat.mul_comm]
  have := (Finset.sum_eq_sum_iff_of_le (fun i _ => hmin i)).mp heq
  exact (this v (Finset.mem_univ v)).symm

/-! ### The two partitions -/

/-- `N⁺(w)` splits as `{v}`, what `w` beats inside `N⁻(v)`, and what `w` beats inside `N⁺(v)`. -/
theorem outN_card_split (h : IsTournament T) (v w : V) (hw : w ∈ inN T v) :
    (outN T w).card
      = 1 + ((outN T w) ∩ (inN T v)).card + ((outN T w) ∩ (outN T v)).card := by
  classical
  have hwv : T w v := (mem_inN T).mp hw
  have hvout : v ∈ outN T w := (mem_outN T).mpr hwv
  have hdisj : Disjoint ((outN T w) ∩ (inN T v)) ((outN T w) ∩ (outN T v)) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    have h1 : T u v := (mem_inN T).mp (Finset.mem_inter.mp hu).2
    have h2 : T v u := (mem_outN T).mp (Finset.mem_inter.mp hu').2
    exact h.asymm u v h1 h2
  have hnotv : v ∉ ((outN T w) ∩ (inN T v)) ∪ ((outN T w) ∩ (outN T v)) := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hm | hm
    · exact h.irrefl v ((mem_inN T).mp (Finset.mem_inter.mp hm).2)
    · exact h.irrefl v ((mem_outN T).mp (Finset.mem_inter.mp hm).2)
  have hset : outN T w
      = insert v (((outN T w) ∩ (inN T v)) ∪ ((outN T w) ∩ (outN T v))) := by
    ext u
    constructor
    · intro hu
      by_cases huv : u = v
      · exact Finset.mem_insert.mpr (Or.inl huv)
      · refine Finset.mem_insert.mpr (Or.inr ?_)
        rcases h.total u v huv with h1 | h1
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hu, (mem_inN T).mpr h1⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hu, (mem_outN T).mpr h1⟩)
    · intro hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hvout
      · rcases Finset.mem_union.mp hu with hm | hm
        · exact (Finset.mem_inter.mp hm).1
        · exact (Finset.mem_inter.mp hm).1
  conv_lhs => rw [hset]
  rw [Finset.card_insert_of_notMem hnotv, Finset.card_union_of_disjoint hdisj]
  omega

/-- `N⁻(v)` splits as `{w}`, what `w` beats inside it, and what beats `w` inside it. -/
theorem inN_card_split (h : IsTournament T) (v w : V) (hw : w ∈ inN T v) :
    (inN T v).card
      = 1 + ((outN T w) ∩ (inN T v)).card + ((inN T w) ∩ (inN T v)).card := by
  classical
  have hdisj : Disjoint ((outN T w) ∩ (inN T v)) ((inN T w) ∩ (inN T v)) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    have h1 : T w u := (mem_outN T).mp (Finset.mem_inter.mp hu).1
    have h2 : T u w := (mem_inN T).mp (Finset.mem_inter.mp hu').1
    exact h.asymm w u h1 h2
  have hnotw : w ∉ ((outN T w) ∩ (inN T v)) ∪ ((inN T w) ∩ (inN T v)) := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hm | hm
    · exact h.irrefl w ((mem_outN T).mp (Finset.mem_inter.mp hm).1)
    · exact h.irrefl w ((mem_inN T).mp (Finset.mem_inter.mp hm).1)
  have hset : inN T v
      = insert w (((outN T w) ∩ (inN T v)) ∪ ((inN T w) ∩ (inN T v))) := by
    ext u
    constructor
    · intro hu
      by_cases huw : u = w
      · exact Finset.mem_insert.mpr (Or.inl huw)
      · refine Finset.mem_insert.mpr (Or.inr ?_)
        rcases h.total w u (fun hEq => huw hEq.symm) with h1 | h1
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨(mem_outN T).mpr h1, hu⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨(mem_inN T).mpr h1, hu⟩)
    · intro hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hw
      · rcases Finset.mem_union.mp hu with hm | hm
        · exact (Finset.mem_inter.mp hm).2
        · exact (Finset.mem_inter.mp hm).2
  conv_lhs => rw [hset]
  rw [Finset.card_insert_of_notMem hnotw, Finset.card_union_of_disjoint hdisj]
  omega

/-! ### The equality case -/

/-- **REACH IS INTERNAL IN-DEGREE.**  At the recursion bound, a vertex's reach into `N⁺(v)`
equals its in-degree inside `N⁻(v)`, exactly.  This is
`Erdos902Reach.external_reach_paid_internally` with every inequality collapsed. -/
theorem reach_eq_internal_indeg (h : IsTournament T) (F : ℕ)
    (hmin : ∀ x : V, F ≤ (inN T x).card) (hN : Fintype.card V = 2 * F + 1)
    (v w : V) (hw : w ∈ inN T v) :
    ((outN T w) ∩ (outN T v)).card = ((inN T w) ∩ (inN T v)).card := by
  have hinw : (inN T w).card = F := regular_at_bound T h F hmin hN w
  have hinv : (inN T v).card = F := regular_at_bound T h F hmin hN v
  have hout : (inN T w).card + (outN T w).card + 1 = Fintype.card V :=
    indeg_add_outdeg_succ T h w
  have h1 := outN_card_split T h v w hw
  have h2 := inN_card_split T h v w hw
  omega

#print axioms sum_indeg
#print axioms regular_at_bound
#print axioms outN_card_split
#print axioms inN_card_split
#print axioms reach_eq_internal_indeg

end Erdos902Rigid
