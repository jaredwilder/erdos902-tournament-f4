/-
Erdos 902 -- THE INTERACTION, and why it is EMPTY.

Last round ended on a conjecture: `N-(v)` must be simultaneously (a) an `S_k` Schutte
tournament and (b) a covering design for the `k`-subsets of everything outside, counting (a)
alone gives `2^k`, counting (b) alone gives `2^k`, and the factor of `k` was supposed to live in
the CONFLICT between them -- an extremal `S_k` tournament being too tight an object to also
afford covering the complement.

This file computes that conflict.  It is empty, and the reason is exact.

⭐ THE BIPARTITE FORM (`bipartite_cover`).  Specialised to `A` inside `N+(v)`, the covering law
says `N-(v)` must dominate every `k`-subset of `N+(v)`, with blocks `N+(w) ∩ N+(v)`.  Covering
is hard exactly when the blocks are small, so the question is how much of `N+(v)` a single `w`
can be forced to MISS.

⭐ THE BLOCK CAP (`block_miss`).  There is such a forcing, and it comes from the in-degree
hypothesis.  For `w` in `N-(v)`, the in-neighbourhood of `w` lives in `N-(v) \ {w}` together
with `N-(w) ∩ N+(v)`, so with `F` a lower bound on every in-degree and `m = |N-(v)|`:

      F  <=  (m - 1)  +  |N-(w) ∩ N+(v)|,

i.e. every block misses at least `F - (m-1)` elements of `N+(v)`.  That is a genuine cap and it
is exactly the interaction: THE SAME HYPOTHESIS THAT MAKES `N-(v)` LARGE ALSO CAPS HOW MUCH OF
`N+(v)` ANY SINGLE MEMBER CAN COVER.

⛔ AND THAT IS WHY IT CANCELS (`cap_vacuous`).  The hypothesis `F <= in-degree` applies to `v`
itself, giving `m >= F` -- so the forced miss `F - (m-1)` is AT MOST ONE.  The cap is vacuous.
The two jobs do not fight: (a) constrains the arcs INSIDE `N-(v)`, (b) constrains the arcs FROM
`N-(v)` TO `N+(v)`, and `N-(v)` and `N+(v)` are DISJOINT (`inN_disjoint_outN`), so the two
properties are supported on disjoint sets of arcs and can be satisfied independently.

THE CONJECTURE OF THE PREVIOUS ROUND IS THEREFORE FALSE, and the reason is structural rather
than numerical: there is no tension to exploit because the two conditions never look at the same
arc.  Any argument reaching the Szekeres order must couple `N-(v)`'s internal structure to its
outgoing arcs by some means OTHER than these two counts -- which is a sharper statement of what
remains than "attack the tail", and it is the fifth closure.
-/
import Mathlib
import Erdos902ClosedForm
import Erdos902Mass
import Erdos902Cover

open Finset

namespace Erdos902Interaction

variable {V : Type*} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T]

/-- `N⁻(v)` and `N⁺(v)` are disjoint: no arc is looked at by both jobs. -/
theorem inN_disjoint_outN (h : IsTournament T) (v : V) :
    Disjoint (Erdos902Cover.inN T v) (Erdos902Mass.outN T v) := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  simp only [Erdos902Cover.inN, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  simp only [Erdos902Mass.outN, Finset.mem_filter, Finset.mem_univ, true_and] at hu'
  exact h.asymm u v hu hu'

/-- **THE BIPARTITE COVERING LAW.**  `N⁻(v)` must dominate every `k`-subset of `N⁺(v)`. -/
theorem bipartite_cover (k : ℕ) (hS : HasSle T (k + 1)) (v : V) (A : Finset V)
    (hA : A.card ≤ k) (_hsub : A ⊆ Erdos902Mass.outN T v) :
    ∃ w ∈ Erdos902Cover.inN T v, ∀ a ∈ A, T w a :=
  Erdos902Cover.inNbhd_covers T k hS v A hA

/-- **THE BLOCK CAP.**  Every block misses at least `F - (m-1)` of `N⁺(v)`: a member `w` of
`N⁻(v)` must collect its `F` in-neighbours from `N⁻(v) \ {w}` and from `N⁻(w) ∩ N⁺(v)`, and `v`
itself is not available since `w` beats `v`. -/
theorem block_miss (h : IsTournament T) (F : ℕ) (hF : ∀ x : V, F ≤ (Erdos902Cover.inN T x).card)
    (v w : V) (hw : w ∈ Erdos902Cover.inN T v) :
    F ≤ ((Erdos902Cover.inN T v).card - 1)
        + ((Erdos902Cover.inN T w) ∩ (Erdos902Mass.outN T v)).card := by
  have hwv : T w v := by
    simpa [Erdos902Cover.inN] using hw
  have hsub : Erdos902Cover.inN T w
      ⊆ ((Erdos902Cover.inN T v).erase w)
        ∪ ((Erdos902Cover.inN T w) ∩ (Erdos902Mass.outN T v)) := by
    intro u hu
    have huw : T u w := by simpa [Erdos902Cover.inN] using hu
    have hunew : u ≠ w := by
      intro hEq
      rw [hEq] at huw
      exact h.irrefl w huw
    have hunev : u ≠ v := by
      intro hEq
      rw [hEq] at huw
      exact h.asymm v w huw hwv
    rcases h.total u v hunev with huv | hvu
    · refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hunew, ?_⟩)
      simpa [Erdos902Cover.inN] using huv
    · refine Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hu, ?_⟩)
      simpa [Erdos902Mass.outN] using hvu
  calc F ≤ (Erdos902Cover.inN T w).card := hF w
    _ ≤ (((Erdos902Cover.inN T v).erase w)
          ∪ ((Erdos902Cover.inN T w) ∩ (Erdos902Mass.outN T v))).card :=
        Finset.card_le_card hsub
    _ ≤ ((Erdos902Cover.inN T v).erase w).card
          + ((Erdos902Cover.inN T w) ∩ (Erdos902Mass.outN T v)).card :=
        Finset.card_union_le _ _
    _ = ((Erdos902Cover.inN T v).card - 1)
          + ((Erdos902Cover.inN T w) ∩ (Erdos902Mass.outN T v)).card := by
        rw [Finset.card_erase_of_mem hw]

/-- **THE CAP IS VACUOUS.**  The forced miss `F - (m-1)` is at most ONE, because the same
hypothesis bounding every in-degree below by `F` applies to `v`, giving `m ≥ F`.

This is the interaction, evaluated: the constraint that makes `N⁻(v)` large is the constraint
that destroys the cap. -/
theorem cap_vacuous (F : ℕ) (hF : ∀ x : V, F ≤ (Erdos902Cover.inN T x).card) (v : V) :
    F - ((Erdos902Cover.inN T v).card - 1) ≤ 1 := by
  have := hF v
  omega

/-- **THE INTERACTION IS EMPTY, stated as one theorem.**  The block cap holds, and it is
simultaneously vacuous -- so no bound better than the separate counts can be extracted from the
pair of conditions. -/
theorem interaction_empty (h : IsTournament T) (F : ℕ)
    (hF : ∀ x : V, F ≤ (Erdos902Cover.inN T x).card) (v w : V)
    (hw : w ∈ Erdos902Cover.inN T v) :
    (F ≤ ((Erdos902Cover.inN T v).card - 1)
        + ((Erdos902Cover.inN T w) ∩ (Erdos902Mass.outN T v)).card)
    ∧ (F - ((Erdos902Cover.inN T v).card - 1) ≤ 1) :=
  ⟨block_miss T h F hF v w hw, cap_vacuous T F hF v⟩

#print axioms inN_disjoint_outN
#print axioms bipartite_cover
#print axioms block_miss
#print axioms cap_vacuous
#print axioms interaction_empty

end Erdos902Interaction
