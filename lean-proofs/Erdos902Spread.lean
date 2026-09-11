/-
Erdos 902 -- THE SPREAD LEMMA: the statement the previous round said was missing.

`Erdos902Reach` proved the non-vacuous coupling and then died at a named point:

    "the deficits must be SPREAD, not merely large in total -- a pointwise lower bound on d_w,
     or a bound on how many w have d_w small.  The estate has no such statement."

The estate does have such a statement; it just had it in the `t = 0` case only.
`Erdos902Mass.source_unique` says AT MOST ONE vertex of a set beats all the others.  That is
the `t = 0` instance of a Landau-type counting fact, and the general case is three lines.

⭐ THE SPREAD LEMMA (`low_outdeg_card_le`).  In any tournament, inside any set `S`,

      #{ w in S : w beats at most t others of S }   <=   2t + 1.

Proof: let `W` be that set, `s = |W|`.  The arcs INSIDE `W` number `C(s,2)` and every one of
them is counted by some member's out-degree within `S`, so `C(s,2) <= s * t`, so `s <= 2t+1`.
At `t = 0` this returns `source_unique`'s dual: at most one sink.

⭐ WHAT IT GIVES (`deficit_spread`).  Applied to `N-(v)`, the internal out-degrees cannot bunch
at the bottom: at most `2t+1` members of `N-(v)` beat `t` or fewer of the others.  Equivalently
the sorted deficits grow at least like `i/2`.  That is EXACTLY the missing statement of the
previous round, and it is now proved rather than wished for.

⛔ AND IT STILL DOES NOT FINISH.  I checked before writing it down, and the reason is worth more
than the lemma.  The covering requirement is

      C(m, n-1)  <=  sum over w of C(a_w, n-1),

and `C(a, n-1)` is CONVEX in `a`.  Spreading the out-degrees therefore moves mass AWAY from the
few large blocks that were doing all the covering.  Concentration HELPS the adversary here, so a
theorem forcing spread cannot contradict the covering requirement -- it makes it easier to
satisfy, not harder.  Running the numbers: with the dual spread bound the sorted out-degrees
obey `a_[i] <= m-1-(i-1)/2`, and the hockey-stick sum gives
`sum_i C(m-1-(i-1)/2, n-1) ~ 2 C(m,n)`, so the covering requirement collapses to `m >~ n/2`,
which is far WEAKER than the `2^(n-1)` the regular case already supplies.

NINTH CLOSURE, and the sharpest correction of my own reasoning in this whole run: I asked for
spread because I assumed spread was the enemy of covering.  It is the ally.  The previous
round's stated gap was therefore not the real gap -- the real obstruction is that the covering
inequality is convex, so NO redistribution theorem of any kind, spread or concentration, can
close it.  What is needed is a bound that is not a redistribution: something that caps
`sum_w C(a_w, n-1)` directly rather than constraining the profile of `a`.

VERDICT: STILL NOT SOLVED, and one plausible route is now eliminated rather than merely untried.
-/
import Mathlib
import Erdos902Mass

open Finset

namespace Erdos902Spread

variable {V : Type*} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T]

/-- Arcs inside `W` number at least `C(|W|,2)`: every pair contributes one. -/
theorem arcs_inside_ge (h : IsTournament T) (W : Finset V) :
    (W.card).choose 2 ≤ ∑ w ∈ W, ((Erdos902Mass.outN T w) ∩ W).card := by
  classical
  have hsig : ∑ w ∈ W, ((Erdos902Mass.outN T w) ∩ W).card
      = (W.sigma (fun w => (Erdos902Mass.outN T w) ∩ W)).card := by
    rw [Finset.card_sigma]
  rw [hsig, ← Finset.card_powersetCard]
  refine Finset.card_le_card_of_surjOn (fun p => {p.1, p.2}) ?_
  intro S hS
  simp only [Finset.mem_coe, Finset.mem_powersetCard] at hS
  obtain ⟨hsub, hcard⟩ := hS
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have ha : a ∈ W := hsub (by simp)
  have hb : b ∈ W := hsub (by simp)
  rcases h.total a b hab with hT | hT
  · refine ⟨⟨a, b⟩, ?_, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_inter]
    exact ⟨ha, by simpa [Erdos902Mass.outN] using hT, hb⟩
  · refine ⟨⟨b, a⟩, ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_inter]
      exact ⟨hb, by simpa [Erdos902Mass.outN] using hT, ha⟩
    · exact Finset.pair_comm b a

/-- **THE SPREAD LEMMA.**  At most `2t+1` members of `S` beat `t` or fewer of the others.

At `t = 0` this is the dual of `Erdos902Mass.source_unique`: at most one sink. -/
theorem low_outdeg_card_le (h : IsTournament T) (S : Finset V) (t : ℕ) :
    (S.filter (fun w => ((Erdos902Mass.outN T w) ∩ S).card ≤ t)).card ≤ 2 * t + 1 := by
  classical
  set W := S.filter (fun w => ((Erdos902Mass.outN T w) ∩ S).card ≤ t) with hW
  have hWS : W ⊆ S := Finset.filter_subset _ _
  have hlow : ∑ w ∈ W, ((Erdos902Mass.outN T w) ∩ W).card ≤ W.card * t := by
    calc ∑ w ∈ W, ((Erdos902Mass.outN T w) ∩ W).card
        ≤ ∑ w ∈ W, ((Erdos902Mass.outN T w) ∩ S).card := by
          refine Finset.sum_le_sum (fun w _ => Finset.card_le_card ?_)
          exact Finset.inter_subset_inter_left hWS
      _ ≤ ∑ _w ∈ W, t := by
          refine Finset.sum_le_sum (fun w hw => ?_)
          exact (Finset.mem_filter.mp hw).2
      _ = W.card * t := by rw [Finset.sum_const, smul_eq_mul]
  have hge := arcs_inside_ge T h W
  have hchoose : (W.card).choose 2 * 2 = W.card * (W.card - 1) := by
    obtain ⟨r, hr⟩ := Nat.even_mul_pred_self W.card
    rw [Nat.choose_two_right, hr]
    omega
  rcases Nat.eq_zero_or_pos W.card with h0 | hpos
  · omega
  · have hmul : W.card * (W.card - 1) ≤ W.card * (2 * t) := by
      calc W.card * (W.card - 1) = (W.card).choose 2 * 2 := hchoose.symm
        _ ≤ (W.card * t) * 2 := by omega
        _ = W.card * (2 * t) := by ring
    have := Nat.le_of_mul_le_mul_left hmul hpos
    omega

/-- **THE DEFICITS ARE SPREAD.**  Inside `N⁻(v)` the internal out-degrees cannot bunch at the
bottom -- exactly the statement `Erdos902Reach` recorded as missing. -/
theorem deficit_spread (h : IsTournament T) (v : V) (t : ℕ) :
    ((Erdos902Mass.outN T v)ᶜ.filter
        (fun w => ((Erdos902Mass.outN T w) ∩ (Erdos902Mass.outN T v)ᶜ).card ≤ t)).card
      ≤ 2 * t + 1 :=
  low_outdeg_card_le T h _ t

#print axioms arcs_inside_ge
#print axioms low_outdeg_card_le
#print axioms deficit_spread

end Erdos902Spread
