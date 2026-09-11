/-
Erdos 902 -- GOING FOR THE SOLVE.  The non-vacuous coupling, and an honest failure report.

TARGET: `f(n) = Theta(n 2^n)`.  The lower half reduces cleanly.  The estate's recursion
`f(n) >= 2 f(n-1) + 1` iterates to `2^(n+1) - 1`; the Szekeres order `n 2^n` is exactly what an
ADDITIVE gain of `2^(n-1)` per step would give.  So the entire lower half is:

      beat pure doubling by an additive 2^(n-1).

That needs a cap on how much of `N+(v)` a member of `N-(v)` can reach.
`Erdos902Interaction.cap_vacuous` killed the obvious cap: bounding external reach against a
CONSTANT in-degree floor `F` is worthless, because the same floor applies to `v` and forces
`m >= F`, leaving a forced miss of at most 1.

⭐ THE FIX, AND IT IS THE THEOREM OF THIS FILE (`external_reach_paid_internally`).  Do not pay
for external reach with a constant.  Pay for it with `w`'s OWN INTERNAL in-degree.  For `v` of
minimum in-degree `m` and any `w` in `N-(v)`:

      |N+(w) cap N+(v)|  +  m   <=   |N-(w) cap N-(v)|  +  |N+(v)|.

Every vertex `w` beaten into `N-(v)` must collect `m` in-neighbours, and it has only two places
to find them: inside `N-(v)`, or among the vertices of `N+(v)` it fails to beat.  So external
reach is bought with internal in-degree, one for one.  THIS COUPLING IS NOT VACUOUS: the right
side is not a constant but a quantity averaging `(m-1)/2` over `N-(v)`, since the internal arcs
number `C(m,2)`.  Averaged, every member of `N-(v)` misses at least `(m+1)/2` of `N+(v)` -- half
of it, not one element of it.

⛔ AND IT STILL DOES NOT SOLVE THE PROBLEM.  I could not close the gap, and here is exactly
where the attempt dies, so that nobody repeats it.

Feed the cap into the covering law.  With `d_w := m - |N-(w) cap N-(v)|` the missing amount, the
theorem gives `|N+(w) cap N+(v)| <= p - d_w`, and summing the internal-arc count gives
`sum_w d_w = m(m+1)/2`, so the average `d_w` is about `m/2` -- a genuinely large deficit.  But
the covering requirement is

      C(p, n-1)  <=  sum over w of C(p - d_w, n-1),

and `C(p-d, n-1)` is CONVEX in `d`.  Convexity lets an adversary concentrate: hold `d_w = 1` on
`m-1` of the blocks and dump the entire deficit on one.  The constraint is on the SUM of the
`d_w`, so nothing forbids it, and the covering requirement is then satisfied with room to spare.
The bound that survives is `m >~ 2^(n-1)` -- the same barrier as every previous round.

To finish one needs the deficits to be SPREAD, not merely large in total: a pointwise lower
bound on `d_w`, or a bound on the number of `w` with `d_w` small.  The estate has no such
statement, and this file does not supply one.  That is the precise shape of the remaining gap,
and it is smaller than "attack the tail" or "find a coupling" -- both of which are now done.

VERDICT: NOT SOLVED.  A real, non-vacuous coupling is proved.  The step from "the deficits are
large on average" to "the deficits are spread" is missing, and that step is the whole problem.
-/
import Mathlib
import Erdos902Mass
import Erdos902Cover

open Finset

namespace Erdos902Reach

variable {V : Type*} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T]

abbrev inN (v : V) : Finset V := Erdos902Cover.inN T v
abbrev outN (v : V) : Finset V := Erdos902Mass.outN T v

theorem mem_inN {v u : V} : u ∈ inN T v ↔ T u v := by
  simp [Erdos902Cover.inN]

theorem mem_outN {v u : V} : u ∈ outN T v ↔ T v u := by
  simp [Erdos902Mass.outN]

/-- `N⁺(v)` splits, relative to any `w` it does not contain, into what `w` beats and what beats
`w`. -/
theorem outN_split (h : IsTournament T) (v w : V) (hw : w ∈ inN T v) :
    ((inN T w) ∩ (outN T v)).card + ((outN T w) ∩ (outN T v)).card = (outN T v).card := by
  classical
  have hwv : T w v := (mem_inN T).mp hw
  have hne : ∀ u ∈ outN T v, u ≠ w := by
    intro u hu hEq
    have hvu : T v u := (mem_outN T).mp hu
    rw [hEq] at hvu
    exact h.asymm w v hwv hvu
  have h1 : (inN T w) ∩ (outN T v) = (outN T v).filter (fun u => T u w) := by
    ext u
    simp only [Finset.mem_inter, Finset.mem_filter, mem_inN]
    tauto
  have h2 : (outN T w) ∩ (outN T v) = (outN T v).filter (fun u => ¬ T u w) := by
    ext u
    simp only [Finset.mem_inter, Finset.mem_filter, mem_outN]
    constructor
    · rintro ⟨hwu, huv⟩
      exact ⟨huv, fun hcon => h.asymm w u hwu hcon⟩
    · rintro ⟨huv, hnot⟩
      exact ⟨(h.total w u (fun hEq => hne u ((mem_outN T).mpr huv) hEq.symm)).resolve_right hnot, huv⟩
  rw [h1, h2]
  exact Finset.card_filter_add_card_filter_not _

/-- **THE NON-VACUOUS COUPLING.**  External reach is bought with internal in-degree, one for one.

`w` must find `m` in-neighbours, and has only two sources: inside `N⁻(v)`, or among the members
of `N⁺(v)` that it fails to beat.  Unlike `Erdos902Interaction.cap_vacuous`, the right-hand side
is not a constant: it is `|N⁻(w) ∩ N⁻(v)|`, which averages `(m-1)/2` across `N⁻(v)` because the
internal arcs number `C(m,2)`. -/
theorem external_reach_paid_internally (h : IsTournament T) (m : ℕ)
    (hmin : ∀ x : V, m ≤ (inN T x).card) (v w : V) (hw : w ∈ inN T v) :
    ((outN T w) ∩ (outN T v)).card + m
      ≤ ((inN T w) ∩ (inN T v)).card + (outN T v).card := by
  classical
  have hwv : T w v := (mem_inN T).mp hw
  -- `v` is not an in-neighbour of `w`, so `N⁻(w)` lies in the two blocks
  have hsub : inN T w ⊆ ((inN T w) ∩ (inN T v)) ∪ ((inN T w) ∩ (outN T v)) := by
    intro u hu
    have huw : T u w := (mem_inN T).mp hu
    have hunev : u ≠ v := by
      intro hEq
      rw [hEq] at huw
      exact h.asymm w v hwv huw
    rcases h.total u v hunev with huv | hvu
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hu, (mem_inN T).mpr huv⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hu, (mem_outN T).mpr hvu⟩)
  have hcard : m ≤ ((inN T w) ∩ (inN T v)).card + ((inN T w) ∩ (outN T v)).card := by
    calc m ≤ (inN T w).card := hmin w
      _ ≤ (((inN T w) ∩ (inN T v)) ∪ ((inN T w) ∩ (outN T v))).card := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
  have hsplit := outN_split T h v w hw
  omega

/-- The same statement as a MISS bound: `w` fails to beat at least `m - |N⁻(w) ∩ N⁻(v)|` members
of `N⁺(v)`.  Averaged over `N⁻(v)` that deficit is about `m/2`, because the internal arcs number
`C(m,2)` -- large, but the covering law needs it SPREAD, and nothing here spreads it. -/
theorem miss_bound (h : IsTournament T) (m : ℕ)
    (hmin : ∀ x : V, m ≤ (inN T x).card) (v w : V) (hw : w ∈ inN T v) :
    ((outN T w) ∩ (outN T v)).card + (m - ((inN T w) ∩ (inN T v)).card) ≤ (outN T v).card := by
  have hkey := external_reach_paid_internally T h m hmin v w hw
  have hle : ((outN T w) ∩ (outN T v)).card ≤ (outN T v).card :=
    Finset.card_le_card Finset.inter_subset_right
  omega

#print axioms outN_split
#print axioms external_reach_paid_internally
#print axioms miss_bound

end Erdos902Reach
