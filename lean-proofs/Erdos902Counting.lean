/-
Erdos 902 — THE COUNTING STEP.

The in-neighbourhood lemma (proved separately, mathlib-free, in
oracle/math/lean/erdos902/InNeighbourhood.lean) gives: every in-degree is at least f(n-1).
This file supplies the other half of the lower bound:

    in a tournament on N vertices, if EVERY in-degree is at least k, then N >= 2k+1.

Together: f(n) >= 2 f(n-1) + 1.

The argument: in-degrees and out-degrees sum to the same total (each arc is counted once
from each end), and indeg v + outdeg v + 1 = N for every v. So 2 * (sum of in-degrees) = N(N-1).
If every in-degree is at least k then N*k <= sum, giving 2k <= N-1.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A tournament: irreflexive, and exactly one arc between any two distinct vertices. -/
structure IsTournament (T : V → V → Prop) [DecidableRel T] : Prop where
  irrefl : ∀ a, ¬ T a a
  total  : ∀ a b, a ≠ b → T a b ∨ T b a
  asymm  : ∀ a b, T a b → ¬ T b a

variable (T : V → V → Prop) [DecidableRel T]

/-- Vertices that beat `v`. -/
def indeg (v : V) : ℕ := (univ.filter (fun u => T u v)).card
/-- Vertices that `v` beats. -/
def outdeg (v : V) : ℕ := (univ.filter (fun u => T v u)).card

/-- Each arc is counted once from each end. -/
theorem sum_indeg_eq_sum_outdeg : ∑ v, indeg T v = ∑ v, outdeg T v := by
  simp only [indeg, outdeg, card_filter]
  exact Finset.sum_comm

/-- Every other vertex either beats `v` or is beaten by `v`, and `v` itself is neither. -/
theorem indeg_add_outdeg_succ (h : IsTournament T) (v : V) :
    indeg T v + outdeg T v + 1 = Fintype.card V := by
  classical
  have hsplit : (univ.filter (fun u => ¬ T u v)) = (univ.filter (fun u => T v u)) ∪ {v} := by
    ext u
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_singleton]
    constructor
    · intro hu
      by_cases huv : u = v
      · exact Or.inr huv
      · exact Or.inl ((h.total u v huv).resolve_left hu)
    · rintro (hu | rfl)
      · exact h.asymm v u hu
      · exact h.irrefl u
  have hdisj : Disjoint (univ.filter (fun u => T v u)) ({v} : Finset V) := by
    simp only [disjoint_singleton_right, mem_filter, mem_univ, true_and]
    exact h.irrefl v
  have hcard : (univ.filter (fun u => ¬ T u v)).card = outdeg T v + 1 := by
    rw [hsplit, card_union_of_disjoint hdisj, card_singleton]
    rfl
  have := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset V)) (p := fun u => T u v)
  rw [hcard] at this
  simpa [indeg, card_univ, ← Nat.add_assoc] using this

/-- **The counting step.** Every in-degree at least `k` forces `N >= 2k+1`. -/
theorem card_ge_two_mul_succ (h : IsTournament T) (k : ℕ)
    (hk : ∀ v, k ≤ indeg T v) (hne : Nonempty V) :
    2 * k + 1 ≤ Fintype.card V := by
  classical
  set N := Fintype.card V with hN
  have hNpos : 0 < N := Fintype.card_pos
  -- 2 * (sum of in-degrees) = N * (N - 1), via  indeg + outdeg + 1 = N  summed over v
  have hsum : ∑ v : V, (indeg T v + outdeg T v + 1) = N * N := by
    simp only [indeg_add_outdeg_succ T h]
    simp [hN, mul_comm]
  have hsplit : ∑ v : V, (indeg T v + outdeg T v + 1)
      = (∑ v : V, indeg T v) + (∑ v : V, outdeg T v) + N := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp [hN, card_univ]
  have h2 : 2 * (∑ v : V, indeg T v) + N = N * N := by
    rw [← hsum, hsplit, ← sum_indeg_eq_sum_outdeg]
    omega
  -- every in-degree at least k  =>  N * k <= sum
  have hlb : N * k ≤ ∑ v : V, indeg T v := by
    calc N * k = ∑ _v : V, k := by simp [hN, card_univ, mul_comm]
    _ ≤ ∑ v : V, indeg T v := Finset.sum_le_sum (fun v _ => hk v)
  -- N*(2k+1) = 2*(N*k) + N <= 2*S + N = N*N, then cancel the positive factor N
  have step : N * (2 * k + 1) ≤ N * N := by
    have expand : N * (2 * k + 1) = 2 * (N * k) + N := by ring
    calc N * (2 * k + 1) = 2 * (N * k) + N := expand
      _ ≤ 2 * (∑ v : V, indeg T v) + N := by omega
      _ = N * N := h2
  exact Nat.le_of_mul_le_mul_left step hNpos



/-! ## The composition: lemma + counting = the lower bound

Two proved pieces are not a bound. This section joins them.

`HasS T n` is the Schutte property. `InNbhd T v` is the in-neighbourhood of `v` as a subtype,
and `induced T v` the tournament it carries.

`f(m)` is NOT defined here — defining it needs a minimum over all tournaments, which is exactly
the definitional machinery that would have to be trusted. Instead `k` is taken as ANY lower bound
on the size of an S_m sub-tournament, which is precisely what `f(m)` is. The theorem then reads
`f(n+1) >= 2 f(n) + 1` with no definition to audit.
-/

/-- Every `n`-element duplicate-free list is dominated by some vertex outside it. -/
def HasS (T : V → V → Prop) (n : Nat) : Prop :=
  ∀ S : List V, S.length = n → S.Nodup → ∃ v, v ∉ S ∧ ∀ s ∈ S, T v s

/-- The in-neighbourhood of `v` as a type. -/
abbrev InNbhd (T : V → V → Prop) (v : V) : Type _ := {u : V // T u v}

/-- The tournament induced on the in-neighbourhood. -/
def induced (T : V → V → Prop) (v : V) : InNbhd T v → InNbhd T v → Prop :=
  fun a b => T a.val b.val

/-- **The in-neighbourhood lemma.**  A dominator of `S ∪ {v}` must beat `v`, so it lies INSIDE
the in-neighbourhood of `v`. -/
theorem inNbhd_hasS (h : IsTournament T) (n : Nat) (hS : HasS T (n + 1)) (v : V) :
    HasS (induced T v) n := by
  intro S hlen hnd
  have hvnot : v ∉ S.map Subtype.val := by
    intro hv
    obtain ⟨x, _, hx⟩ := List.mem_map.mp hv
    have hx' : T x.val v := x.property
    rw [hx] at hx'
    exact h.irrefl v hx'
  have hmapnd : (S.map Subtype.val).Nodup :=
    List.Pairwise.map Subtype.val (fun a b hab hEq => hab (Subtype.ext hEq)) hnd
  have hlen' : (v :: S.map Subtype.val).length = n + 1 := by simp [hlen]
  have hnd' : (v :: S.map Subtype.val).Nodup := List.nodup_cons.mpr ⟨hvnot, hmapnd⟩
  obtain ⟨u, hunot, hubeats⟩ := hS (v :: S.map Subtype.val) hlen' hnd'
  have huv : T u v := hubeats v List.mem_cons_self
  refine ⟨⟨u, huv⟩, ?_, ?_⟩
  · intro hmem
    exact hunot (List.mem_cons_of_mem _ (List.mem_map_of_mem hmem))
  · intro s hs
    exact hubeats s.val (List.mem_cons_of_mem _ (List.mem_map_of_mem hs))

/-- The in-neighbourhood's cardinality IS the in-degree. -/
theorem card_inNbhd (v : V) : Fintype.card (InNbhd T v) = indeg T v := by
  simp [indeg, Fintype.card_subtype]

/-- **f(n+1) >= 2 f(n) + 1.**

`k` is any lower bound on the number of vertices of a sub-tournament with property `S_n` — that is
exactly what `f(n)` is. The conclusion bounds the size of any tournament with `S_(n+1)`. -/
theorem schutte_lower_bound (h : IsTournament T) (n k : ℕ) (hS : HasS T (n + 1))
    (hne : Nonempty V)
    (hk : ∀ v : V, HasS (induced T v) n → k ≤ Fintype.card (InNbhd T v)) :
    2 * k + 1 ≤ Fintype.card V := by
  refine card_ge_two_mul_succ T h k (fun v => ?_) hne
  have := hk v (inNbhd_hasS T h n hS v)
  rwa [card_inNbhd] at this

#print axioms card_ge_two_mul_succ
#print axioms inNbhd_hasS
#print axioms schutte_lower_bound
