/-
Erdos 902 -- THE COUPLING: one vertex, both jobs, on the same set.

`Erdos902Interaction` showed the two demands on `N-(v)` are supported on DISJOINT arc sets --
(a) the `S_k` property uses arcs inside `N-(v)`, (b) the covering property uses arcs from
`N-(v)` to `N+(v)` -- so they never fight.  That closure came with a precise instruction: any
argument reaching the Szekeres order must couple the two by some means OTHER than those counts.

Here is the means.  A `k`-set need not lie entirely inside `N+(v)` or entirely inside `N-(v)`.
It can STRADDLE.  And a straddling set has ONE dominator, which must beat its internal part
using internal arcs and its external part using external arcs -- AT THE SAME TIME, with the same
out-neighbourhood.  Disjointness of the arc sets cannot separate that, because it is a single
existential quantifier ranging over both.

⭐ THE COUPLING (`straddle_cover`).  For `A₁ ⊆ N-(v)` and `A₂ ⊆ N+(v)` with
`|A₁| + |A₂| ≤ k`, some single `w ∈ N-(v)` beats all of `A₁` AND all of `A₂`.

⭐ THE COUPLED COUNT (`split_cover_count`).  Writing `a_w = |N+(w) ∩ N-(v)|` and
`b_w = |N+(w) ∩ N+(v)|`, for every `j ≤ k`:

    C(m,j) * C(p,k-j)   <=   sum over w in N-(v) of  C(a_w, j) * C(b_w, k-j)

with `m = |N-(v)|`, `p = |N+(v)|`.  This is a PRODUCT, not a sum: a block is useless for
straddling sets unless it is simultaneously large inside and large outside.  Summing over `j`
collapses it back to the old law by Vandermonde -- `sum_j C(a,j)C(b,k-j) = C(a+b,k)` -- so the
family is a strict refinement of the covering law, one instance per split.

⛔ AND THE MEASUREMENT, WHICH IS THE SIXTH CLOSURE.  The refinement is real but every instance
is subsumed.  The internal factor is capped by the internal `S`-property (`a_w` is an
out-degree inside `N-(v)`, so it is at most `m - 1` minus the internal in-degree floor, roughly
`m/2` in the extremal regime), and the external factor is capped by nothing better than `p`
(`Erdos902Interaction.cap_vacuous`).  So instance `j` demands about `m >= 2^j`, binding at
`j = k`, giving `m >= 2^k` -- while the recursion already supplies `m >= f(k-1) >= 2^k - 1`.
Every split is dominated by a bound the estate had before it.

So the coupling EXISTS, is exact, and is the correct object -- and it still does not produce the
factor of `k`.  What that leaves is sharp: the deficiency is not in which sets are counted
(entire, split, or straddling) but in the fact that all of these are FIRST-MOMENT statements
about a single vertex `v`.  Every closure in this estate bounds `|N-(v)|` for one `v` and then
averages.  The factor of `k` must come from a statement about how the in-neighbourhoods of
DIFFERENT vertices overlap -- which no count in this file, or any before it, ever mentions.
-/
import Mathlib
import Erdos902ClosedForm
import Erdos902Mass
import Erdos902Cover

open Finset

namespace Erdos902Coupling

variable {V : Type*} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T]

/-- `N⁻(v)`, `N⁺(v)`. -/
abbrev inN (v : V) : Finset V := Erdos902Cover.inN T v
abbrev outN (v : V) : Finset V := Erdos902Mass.outN T v

/-! ### The coupling -/

/-- **THE COUPLING.**  A straddling set has ONE dominator, which must beat its internal part and
its external part simultaneously.  Disjointness of the two arc sets cannot separate this,
because it is a single existential ranging over both. -/
theorem straddle_cover (k : ℕ) (hS : HasSle T (k + 1)) (v : V) (A₁ A₂ : Finset V)
    (hcard : A₁.card + A₂.card ≤ k) :
    ∃ w ∈ inN T v, (∀ a ∈ A₁, T w a) ∧ (∀ a ∈ A₂, T w a) := by
  have hun : (A₁ ∪ A₂).card ≤ k :=
    le_trans (Finset.card_union_le _ _) hcard
  obtain ⟨w, hw, hbeat⟩ := Erdos902Cover.inNbhd_covers T k hS v (A₁ ∪ A₂) hun
  exact ⟨w, hw, fun a ha => hbeat a (Finset.mem_union_left _ ha),
    fun a ha => hbeat a (Finset.mem_union_right _ ha)⟩

/-! ### The coupled count -/

/-- **THE COUPLED COUNT.**  A product, not a sum: a block is useless for straddling sets unless
it is simultaneously large inside `N⁻(v)` and large inside `N⁺(v)`. -/
theorem split_cover_count (k j : ℕ) (hS : HasSle T (k + 1)) (v : V) (hj : j ≤ k) :
    ((inN T v).card).choose j * ((outN T v).card).choose (k - j)
      ≤ ∑ w ∈ inN T v,
          (((outN T w) ∩ (inN T v)).card).choose j
            * (((outN T w) ∩ (outN T v)).card).choose (k - j) := by
  classical
  set L := ((inN T v).powersetCard j) ×ˢ ((outN T v).powersetCard (k - j)) with hL
  have hsub : L ⊆ (inN T v).biUnion (fun w =>
      (((outN T w) ∩ (inN T v)).powersetCard j)
        ×ˢ (((outN T w) ∩ (outN T v)).powersetCard (k - j))) := by
    intro P hP
    rw [hL, Finset.mem_product] at hP
    obtain ⟨hP1, hP2⟩ := hP
    rw [Finset.mem_powersetCard] at hP1 hP2
    obtain ⟨hs1, hc1⟩ := hP1
    obtain ⟨hs2, hc2⟩ := hP2
    have hcard : P.1.card + P.2.card ≤ k := by omega
    obtain ⟨w, hw, hb1, hb2⟩ := straddle_cover T k hS v P.1 P.2 hcard
    refine Finset.mem_biUnion.mpr ⟨w, hw, ?_⟩
    rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
    refine ⟨⟨fun a ha => ?_, hc1⟩, ⟨fun a ha => ?_, hc2⟩⟩
    · exact Finset.mem_inter.mpr
        ⟨by simpa [Erdos902Mass.outN] using hb1 a ha, hs1 ha⟩
    · exact Finset.mem_inter.mpr
        ⟨by simpa [Erdos902Mass.outN] using hb2 a ha, hs2 ha⟩
  calc ((inN T v).card).choose j * ((outN T v).card).choose (k - j)
      = L.card := by
        rw [hL, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard]
    _ ≤ ∑ w ∈ inN T v, ((((outN T w) ∩ (inN T v)).powersetCard j)
          ×ˢ (((outN T w) ∩ (outN T v)).powersetCard (k - j))).card :=
        le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    _ = _ := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard]

/-- Summing the coupled count over every split collapses it back to the covering law: the
family is a strict refinement, not a different statement.  (Vandermonde.) -/
theorem split_sums_to_total (a b k : ℕ) :
    ∑ ij ∈ Finset.antidiagonal k, a.choose ij.1 * b.choose ij.2 = (a + b).choose k :=
  (Nat.add_choose_eq a b k).symm

#print axioms straddle_cover
#print axioms split_cover_count
#print axioms split_sums_to_total

end Erdos902Coupling
