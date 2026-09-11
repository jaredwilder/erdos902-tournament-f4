/-
Erdos 902 (Schutte's problem) -- THE CLOSED FORM.  f(n) >= 2^(n+1) - 1.

Erdos902Counting.lean proves the RECURSION f(n+1) >= 2 f(n) + 1 and deliberately stops:
"f(m) is NOT defined here". This file supplies the missing induction and the closed form,
which is the Erdos [Er63c] lower bound.

WHY "AT MOST n" AND NOT "EXACTLY n".  With the exactly-n property (HasS, in the other file)
the closed form is FALSE: on an empty vertex type there is no n-element set at all, so the
property holds vacuously while the cardinality is 0.  The downward-closed form HasSle is the
honest hypothesis.  It is equivalent to the literature's definition on any tournament with at
least n vertices, and that equivalence is PROVED below (hasSle_of_hasS / hasS_of_hasSle) --
not asserted.

THIS IS THE LOWER BOUND ONLY.  Erdos 902 asks for the order of f(n) and is OPEN; the upper
bound f(n) << n^2 2^n is probabilistic and is not touched here.
-/
import Erdos902Counting
import Mathlib.Data.Nat.Lattice

open Finset

universe u

variable {V : Type*} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T]

/-- Schutte's property, downward closed: every set of AT MOST `n` vertices has a dominator
outside it. -/
def HasSle {V : Type*} (T : V → V → Prop) (n : ℕ) : Prop :=
  ∀ S : Finset V, S.card ≤ n → ∃ v, v ∉ S ∧ ∀ s ∈ S, T v s

/-- The induced relation on an in-neighbourhood is decidable when `T` is. -/
instance instDecidableRelInduced (v : V) : DecidableRel (induced T v) :=
  fun a b => inferInstanceAs (Decidable (T a.val b.val))

/-- An in-neighbourhood of a tournament is itself a tournament. -/
theorem induced_isTournament (hT : IsTournament T) (v : V) : IsTournament (induced T v) where
  irrefl := fun a => hT.irrefl a.val
  total := fun a b hab => hT.total a.val b.val (fun hEq => hab (Subtype.ext hEq))
  asymm := fun a b hab => hT.asymm a.val b.val hab

/-- **Descent.**  If every set of at most `n+1` vertices is dominated, then inside the
in-neighbourhood of any `v` every set of at most `n` vertices is dominated: a dominator of
`S ∪ {v}` must beat `v`, hence lives in the in-neighbourhood. -/
theorem hasSle_induced (hT : IsTournament T) (n : ℕ) (hS : HasSle T (n + 1)) (v : V) :
    HasSle (induced T v) n := by
  classical
  intro S hcard
  have hcard' : (insert v (S.image Subtype.val)).card ≤ n + 1 := by
    calc (insert v (S.image Subtype.val)).card ≤ (S.image Subtype.val).card + 1 :=
          card_insert_le _ _
      _ ≤ S.card + 1 := Nat.add_le_add_right Finset.card_image_le 1
      _ ≤ n + 1 := Nat.add_le_add_right hcard 1
  obtain ⟨w, hwnot, hwbeat⟩ := hS _ hcard'
  have hwv : T w v := hwbeat v (mem_insert_self _ _)
  refine ⟨⟨w, hwv⟩, ?_, ?_⟩
  · intro hmem
    exact hwnot (mem_insert_of_mem (mem_image_of_mem Subtype.val hmem))
  · intro s hs
    exact hwbeat s.val (mem_insert_of_mem (mem_image_of_mem Subtype.val hs))

/-- **THE CLOSED FORM.**  Any tournament in which every set of at most `n` vertices has a
dominator has at least `2^(n+1) - 1` vertices. -/
theorem card_ge_two_pow_sub_one :
    ∀ (n : ℕ) {V : Type u} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T],
      IsTournament T → HasSle T n → 2 ^ (n + 1) - 1 ≤ Fintype.card V := by
  intro n
  induction n with
  | zero =>
      intro V _ _ T _ _ hS
      obtain ⟨v, -, -⟩ := hS ∅ (by simp)
      have : Nonempty V := ⟨v⟩
      rw [show (2 : ℕ) ^ (0 + 1) - 1 = 1 from by norm_num]
      exact Fintype.card_pos
  | succ n ih =>
      intro V _ _ T _ hT hS
      obtain ⟨v0, -, -⟩ := hS ∅ (by simp)
      have hne : Nonempty V := ⟨v0⟩
      have hk : ∀ v : V, 2 ^ (n + 1) - 1 ≤ indeg T v := by
        intro v
        have hsub := ih (induced T v) (induced_isTournament T hT v)
          (hasSle_induced T hT n hS v)
        rwa [card_inNbhd T v] at hsub
      have hmain := card_ge_two_mul_succ T hT (2 ^ (n + 1) - 1) hk hne
      have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow (n + 1) 2 (by norm_num)
      have h2 : (2 : ℕ) ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
      omega

/-! ## Bridge to the literature's definition (exactly-`n` sets) -/

/-- Exactly-`n` domination implies at-most-`n` domination, once there are at least `n`
vertices: pad the small set up to size `n` and dominate that. -/
theorem hasSle_of_hasS (n : ℕ) (hn : n ≤ Fintype.card V) (hS : HasS T n) : HasSle T n := by
  classical
  intro S hcard
  obtain ⟨U, hSU, hU⟩ := Finset.exists_superset_card_eq hcard hn
  obtain ⟨w, hwnot, hwbeat⟩ := hS U.toList (by rw [Finset.length_toList, hU]) U.nodup_toList
  exact ⟨w, fun hmem => hwnot (Finset.mem_toList.mpr (hSU hmem)),
    fun s hs => hwbeat s (Finset.mem_toList.mpr (hSU hs))⟩

/-- The converse, with no side condition. -/
theorem hasS_of_hasSle (n : ℕ) (hS : HasSle T n) : HasS T n := by
  classical
  intro L hlen hnd
  obtain ⟨w, hwnot, hwbeat⟩ := hS L.toFinset (by rw [List.toFinset_card_of_nodup hnd, hlen])
  exact ⟨w, fun hmem => hwnot (List.mem_toFinset.mpr hmem),
    fun s hs => hwbeat s (List.mem_toFinset.mpr hs)⟩

/-! ## f(n) itself -/

/-- There is a tournament on `m` vertices with Schutte's property `S_n`. -/
def SchutteAt (n m : ℕ) : Prop :=
  ∃ (T : Fin m → Fin m → Prop) (inst : DecidableRel T),
    (letI := inst; IsTournament T ∧ HasSle T n)

/-- **f(n) >= 2^(n+1) - 1** in the form that needs no definition of `f`: EVERY vertex count
admitting such a tournament is at least `2^(n+1) - 1`. -/
theorem schutte_card_bound (n m : ℕ) (h : SchutteAt n m) : 2 ^ (n + 1) - 1 ≤ m := by
  obtain ⟨T, inst, hT, hS⟩ := h
  letI := inst
  have := card_ge_two_pow_sub_one n T hT hS
  simpa using this

/-- `f n` as the least admissible vertex count. -/
noncomputable def f (n : ℕ) : ℕ := sInf {m | SchutteAt n m}

/-- The Erdos lower bound for `f` itself, given that some tournament with `S_n` exists at all
(existence is the probabilistic upper-bound half, which is NOT proved here). -/
theorem f_ge (n : ℕ) (hne : {m | SchutteAt n m}.Nonempty) : 2 ^ (n + 1) - 1 ≤ f n :=
  schutte_card_bound n (f n) (Nat.sInf_mem hne)

/-- f(1) >= 3, f(2) >= 7, f(3) >= 15.  (The true values are 3, 7, 19.) -/
example (m : ℕ) (h : SchutteAt 1 m) : 3 ≤ m := by simpa using schutte_card_bound 1 m h
example (m : ℕ) (h : SchutteAt 2 m) : 7 ≤ m := by simpa using schutte_card_bound 2 m h
example (m : ℕ) (h : SchutteAt 3 m) : 15 ≤ m := by simpa using schutte_card_bound 3 m h

#print axioms card_ge_two_pow_sub_one
#print axioms hasSle_of_hasS
#print axioms hasS_of_hasSle
#print axioms schutte_card_bound
#print axioms f_ge
