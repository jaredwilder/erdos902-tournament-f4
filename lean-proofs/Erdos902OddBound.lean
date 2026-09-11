/-
Erdos 902 -- THE ODD-ORDER UPPER BOUNDS.  A dominant j-set is unique, so every factorial moment
is capped with no distributional input at all.

`Erdos902Order` left one thing missing: upper bounds on `T_j = sum over j-sets S of
C(|comN S|, n)` for `j >= 3`.  The estate had exact values only at `j = 1, 2`, and for `j >= 3`
only the TOTAL of the codegrees was pinned while their distribution was free -- which blocks any
upper bound, since `C(-, n)` is convex.

This file supplies the bound, and it needs no distribution.

⭐ UNIQUENESS OF A DOMINANT SET (`dominant_unique`).  If `S` and `S'` are `j`-subsets of the same
`U`, each beating everything of `U` outside itself, then `S = S'`.  Take `x` in `S \ S'` and `x'`
in `S' \ S`: then `x'` lies outside `S` so `x` beats it, and `x` lies outside `S'` so `x'` beats
it -- impossible.  At `j = 1` this is exactly `Erdos902Mass.source_unique`; the general case is
the same two lines.

⭐ THE CAP (`factorial_moment_le`).  Send the pair `(A, S)` -- an `n`-set `A` and a `j`-set `S`
dominating it -- to the `(n+j)`-set `A ∪ S`.  The two are disjoint by irreflexivity, and
uniqueness makes the map injective, so

      T_j  =  sum over n-sets A of C(c(A), j)  <=  C(N, n+j)

for EVERY `j`, odd or even, with no hypothesis beyond being a tournament.  Every term of
`Erdos902Order.bonferroni_general` is now bounded above.

⛔ AND IT IS NOT TIGHT ENOUGH TO CLOSE, which I checked before writing it down.  `C(N,n+j)/C(N,n)`
is about `(N/n)^j`, whereas the true size of `T_j / C(N,n)` is about `t^j / j!` with
`t = N/2^n`.  The cap therefore exceeds the truth by roughly `(2^n/n)^j * j!` -- enormous.  The
reason is structural and worth stating: the map's image is the set of `(n+j)`-sets that HAVE a
dominant `j`-set, and in a Schutte tournament almost none do.  The bound throws away exactly the
information that makes the problem hard.

FIFTEENTH CLOSURE.  The missing family is now supplied in the only distribution-free form that
exists, and it is provably too weak.  That settles the shape of what is left: an upper bound on
`T_j` sharp enough to close must count `(n+j)`-sets with a dominant `j`-set to within a factor
`(n/2^n)^j j!` of the truth, i.e. it must know how RARE dominant sets are -- which is a
statement about the codegree distribution, not about the tournament axioms.  No distribution-free
argument can do it, and this file is the proof of that, since it is the best such argument.
-/
import Mathlib
import Erdos902Bonferroni

open Finset

namespace Erdos902OddBound

variable {V : Type*} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T]

/-- `S` beats everything of `U` lying outside `S`. -/
def Dominant (U S : Finset V) : Prop := ∀ x ∈ S, ∀ a ∈ U, a ∉ S → T x a

/-- **A DOMINANT SET IS UNIQUE.**  Two of the same size in the same `U` would contain vertices
beating each other.  At `j = 1` this is `Erdos902Mass.source_unique`. -/
theorem dominant_unique (h : IsTournament T) {U S S' : Finset V}
    (hS : S ⊆ U) (hS' : S' ⊆ U) (hcard : S.card = S'.card)
    (hd : Dominant T U S) (hd' : Dominant T U S') : S = S' := by
  classical
  by_contra hne
  -- if either difference is empty, equal cardinalities force equality
  have hsub : ¬ (S ⊆ S') := by
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm))
  obtain ⟨x, hxS, hxS'⟩ := Finset.not_subset.mp hsub
  have hsub' : ¬ (S' ⊆ S) := by
    intro hsub'
    exact hne (Finset.eq_of_subset_of_card_le hsub' (le_of_eq hcard)).symm
  obtain ⟨x', hx'S', hx'S⟩ := Finset.not_subset.mp hsub'
  -- `x` beats `x'` because `x'` is outside `S`; `x'` beats `x` because `x` is outside `S'`
  have h1 : T x x' := hd x hxS x' (hS' hx'S') hx'S
  have h2 : T x' x := hd' x' hx'S' x (hS hxS) hxS'
  exact h.asymm x x' h1 h2

/-- **THE CAP AT EVERY ORDER.**  `(A, S) ↦ A ∪ S` is injective into the `(n+j)`-sets, so every
factorial moment of the dominator count is bounded with no distributional input. -/
theorem factorial_moment_le (h : IsTournament T) (n j : ℕ) :
    ∑ A ∈ (univ : Finset V).powersetCard n, ((Erdos902Mass.domSet T A).card).choose j
      ≤ (Fintype.card V).choose (n + j) := by
  classical
  have hsig : ∑ A ∈ (univ : Finset V).powersetCard n, ((Erdos902Mass.domSet T A).card).choose j
      = (((univ : Finset V).powersetCard n).sigma
          (fun A => (Erdos902Mass.domSet T A).powersetCard j)).card := by
    rw [Finset.card_sigma]
    exact Finset.sum_congr rfl (fun A _ => (Finset.card_powersetCard _ _).symm)
  have hrhs : (Fintype.card V).choose (n + j)
      = ((univ : Finset V).powersetCard (n + j)).card := by
    rw [Finset.card_powersetCard, Finset.card_univ]
  rw [hsig, hrhs]
  -- disjointness of an `n`-set from any set dominating it
  have hdisj : ∀ (A S : Finset V), S ⊆ Erdos902Mass.domSet T A → Disjoint A S := by
    intro A S hsub
    rw [Finset.disjoint_right]
    intro x hxS hxA
    have := hsub hxS
    simp only [Erdos902Mass.domSet, Finset.mem_filter, Erdos902Mass.DominatesAll] at this
    exact h.irrefl x (this.2 x hxA)
  have hdom : ∀ (A S : Finset V), S ⊆ Erdos902Mass.domSet T A → Dominant T (A ∪ S) S := by
    intro A S hsub x hxS a ha haS
    have hxd := hsub hxS
    simp only [Erdos902Mass.domSet, Finset.mem_filter, Erdos902Mass.DominatesAll] at hxd
    exact hxd.2 a ((Finset.mem_union.mp ha).resolve_right haS)
  refine Finset.card_le_card_of_injOn (fun p => p.1 ∪ p.2) ?_ ?_
  · rintro ⟨A, S⟩ hp
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powersetCard] at hp
    obtain ⟨⟨-, hAcard⟩, hSsub, hScard⟩ := hp
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_union_of_disjoint (hdisj A S hSsub), hAcard, hScard]
  · rintro ⟨A, S⟩ hp ⟨A', S'⟩ hq hEq
    have hEq' : A ∪ S = A' ∪ S' := hEq
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powersetCard] at hp hq
    obtain ⟨⟨-, hAcard⟩, hSsub, hScard⟩ := hp
    obtain ⟨⟨-, hAcard'⟩, hSsub', hScard'⟩ := hq
    have hSS : S = S' := by
      refine dominant_unique T h (U := A ∪ S) Finset.subset_union_right ?_ ?_ ?_ ?_
      · rw [hEq']; exact Finset.subset_union_right
      · rw [hScard, hScard']
      · exact hdom A S hSsub
      · rw [hEq']; exact hdom A' S' hSsub'
    subst hSS
    have hAA : A = A' := by
      have h1 : (A ∪ S) \ S = A := Finset.union_sdiff_cancel_right (hdisj A S hSsub)
      have h2 : (A' ∪ S) \ S = A' := Finset.union_sdiff_cancel_right (hdisj A' S hSsub')
      rw [← h1, ← h2, hEq']
    subst hAA
    rfl

/-- The same bound in the `comN` form used by `Erdos902Order.bonferroni_general`: every one of
its terms, odd or even, is at most `C(N, n+j)`. -/
theorem comN_sum_le (h : IsTournament T) (n j : ℕ) :
    ∑ S ∈ (univ : Finset V).powersetCard j, ((Erdos902Bonferroni.comN T S).card).choose n
      ≤ (Fintype.card V).choose (n + j) := by
  rw [← Erdos902Bonferroni.factorial_moment_identity T n j]
  exact factorial_moment_le T h n j

#print axioms dominant_unique
#print axioms factorial_moment_le
#print axioms comN_sum_le

end Erdos902OddBound
