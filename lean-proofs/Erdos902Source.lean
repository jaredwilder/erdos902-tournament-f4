/-
Erdos 902 -- THE SOURCELESS IDENTITY: what the sharp bound was actually counting.

`Erdos902Mass.sum_choose_outdeg_le` proved `sum_x C(d+(x), j) <= C(N, j+1)` by sending the pair
`(x, B)` -- `x` dominating the `j`-set `B` -- to `insert x B`, injectively, because a tournament
has at most one vertex of a set beating all the others.  That was stated as an INEQUALITY, and
the deficit was never named.

An injection has an image.  This file computes it.

⭐ THE IDENTITY (`sourceful_count`).  Call a set SOURCEFUL if one of its own members beats all
the others.  The image of that injection is exactly the sourceful `(j+1)`-sets, so

      sum over x of C(d+(x), j)   =   #{ sourceful (j+1)-sets },

an EQUALITY, with no tournament hypothesis beyond being a tournament.  The bound
`<= C(N,j+1)` was the identity plus the observation that sourceful sets are sets; its slack was
never mysterious, it was the sourceless sets all along.

⭐ THE CONSEQUENCE (`sourceless_le`).  In a tournament with Schutte's property, every `n`-set has
a dominator, so `C(N,n) <= sum_x C(d+(x), n)` -- and by the identity that is a lower bound on the
number of SOURCEFUL `(n+1)`-sets.  Hence

      #{ sourceless (n+1)-sets }   <=   C(N, n+1) - C(N, n).

This is a structural theorem about Schutte tournaments rather than a counting bound on `N`:
domination forces a supply of internal sources.  A tournament with `S_n` cannot be too
thoroughly cyclic at scale `n+1`, and the permitted amount of cyclicity is exactly
`C(N,n+1) - C(N,n)`.

⛔ WHAT IT DOES AND DOES NOT GIVE.  Read as a bound on `N` it degenerates: `#sourceless >= 0`
turns it into `C(N,n) <= C(N,n+1)`, i.e. `N >= 2n+1`, far below `2^(n+1)-1`.  Its content is in
the other direction -- it constrains the STRUCTURE of any extremal example rather than its size,
and it is the first statement in this estate that does so.  Every previous closure bounded a
cardinality; this one bounds a shape.

The `n = 2` case is a cleaner form of a classical fact: `#{sourceless triples}` is the number of
3-cycles, `sum_x C(d+(x),2)` counts the transitive ones, and the identity here is the classical
`#3-cycles = C(N,3) - sum_x C(d+(x),2)` obtained as a special case rather than assumed.
-/
import Mathlib
import Erdos902Mass

open Finset

namespace Erdos902Source

variable {V : Type*} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T]

/-- A set is SOURCEFUL when one of its own members beats all the others. -/
def Sourceful (S : Finset V) : Prop := ∃ x ∈ S, ∀ y ∈ S, y ≠ x → T x y

instance : DecidablePred (Sourceful T) := fun _ => by
  unfold Sourceful; infer_instance

/-! ### The identity -/

/-- **THE SOURCELESS IDENTITY.**  The injection of `Erdos902Mass.sum_choose_outdeg_le` has image
exactly the sourceful `(j+1)`-sets, so its inequality was an equality in disguise. -/
theorem sourceful_count (h : IsTournament T) (j : ℕ) :
    ∑ x : V, ((Erdos902Mass.outN T x).card).choose j
      = (((univ : Finset V).powersetCard (j + 1)).filter (Sourceful T)).card := by
  classical
  have hsig : ∑ x : V, ((Erdos902Mass.outN T x).card).choose j
      = ((univ : Finset V).sigma (fun x => (Erdos902Mass.outN T x).powersetCard j)).card := by
    rw [Finset.card_sigma]
    exact Finset.sum_congr rfl (fun x _ => (Finset.card_powersetCard _ _).symm)
  have hxB : ∀ (x : V) (B : Finset V), B ⊆ Erdos902Mass.outN T x → x ∉ B := by
    intro x B hsub hmem
    have := hsub hmem
    simp only [Erdos902Mass.outN, Finset.mem_filter] at this
    exact h.irrefl x this.2
  have himg : ((univ : Finset V).sigma
        (fun x => (Erdos902Mass.outN T x).powersetCard j)).image (fun p => insert p.1 p.2)
      = ((univ : Finset V).powersetCard (j + 1)).filter (Sourceful T) := by
    ext S
    simp only [Finset.mem_image, Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨x, B⟩, ⟨hsub, hcard⟩, rfl⟩
      have hnot : x ∉ B := hxB x B hsub
      refine ⟨⟨Finset.subset_univ _, ?_⟩, x, Finset.mem_insert_self _ _, ?_⟩
      · rw [Finset.card_insert_of_notMem hnot, hcard]
      · intro y hy hne
        have hyB : y ∈ B := (Finset.mem_insert.mp hy).resolve_left hne
        have := hsub hyB
        simpa [Erdos902Mass.outN] using this
    · rintro ⟨⟨-, hcard⟩, x, hxS, hsrc⟩
      refine ⟨⟨x, S.erase x⟩, ⟨?_, ?_⟩, ?_⟩
      · intro y hy
        have hyS : y ∈ S := Finset.mem_of_mem_erase hy
        have hne : y ≠ x := Finset.ne_of_mem_erase hy
        simpa [Erdos902Mass.outN] using hsrc y hyS hne
      · rw [Finset.card_erase_of_mem hxS, hcard]
        rfl
      · exact Finset.insert_erase hxS
  rw [hsig, ← himg, Finset.card_image_of_injOn]
  rintro ⟨x, B⟩ hp ⟨x', B'⟩ hq hEq
  have hEq' : insert x B = insert x' B' := hEq
  simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powersetCard] at hp hq
  have hdomx : Erdos902Mass.DominatesAll T B x := by
    intro b hb
    have := hp.2.1 hb
    simpa [Erdos902Mass.outN] using this
  have hdomx' : Erdos902Mass.DominatesAll T B' x' := by
    intro b hb
    have := hq.2.1 hb
    simpa [Erdos902Mass.outN] using this
  have hxx : x = x' :=
    Erdos902Mass.source_unique T h hdomx hdomx' (hxB x B hp.2.1) (hxB x' B' hq.2.1) hEq'
  subst hxx
  have hBB : B = B' := by
    have h1 : (insert x B).erase x = (insert x B').erase x := by rw [hEq']
    rwa [Finset.erase_insert (hxB x B hp.2.1), Finset.erase_insert (hxB x B' hq.2.1)] at h1
  subst hBB
  rfl

/-! ### The consequence for Schutte tournaments -/

/-- **DOMINATION FORCES SOURCES.**  If every `n`-set has a dominator then the sourceful
`(n+1)`-sets number at least `C(N,n)`, so the sourceless ones number at most
`C(N,n+1) - C(N,n)`.  A Schutte tournament cannot be too thoroughly cyclic at scale `n+1`. -/
theorem sourceless_le (h : IsTournament T) (n : ℕ)
    (hdom : ∀ A ∈ (univ : Finset V).powersetCard n, 1 ≤ (Erdos902Mass.domSet T A).card) :
    (((univ : Finset V).powersetCard (n + 1)).filter (fun S => ¬ Sourceful T S)).card
      ≤ (Fintype.card V).choose (n + 1) - (Fintype.card V).choose n := by
  have hcov : (Fintype.card V).choose n
      ≤ ∑ x : V, ((Erdos902Mass.outN T x).card).choose n := by
    calc (Fintype.card V).choose n
        = ∑ _A ∈ (univ : Finset V).powersetCard n, 1 := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, smul_eq_mul,
            Nat.mul_one]
      _ ≤ ∑ A ∈ (univ : Finset V).powersetCard n, (Erdos902Mass.domSet T A).card :=
          Finset.sum_le_sum hdom
      _ = _ := Erdos902Mass.total_domination_general T n
  have hsplit : (((univ : Finset V).powersetCard (n + 1)).filter (Sourceful T)).card
      + (((univ : Finset V).powersetCard (n + 1)).filter (fun S => ¬ Sourceful T S)).card
      = (Fintype.card V).choose (n + 1) := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_powersetCard,
      Finset.card_univ]
  rw [← sourceful_count T h n] at hsplit
  omega

#print axioms sourceful_count
#print axioms sourceless_le

end Erdos902Source
