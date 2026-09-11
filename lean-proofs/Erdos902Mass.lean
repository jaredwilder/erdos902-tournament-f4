/-
Erdos 902 -- THE SHARP MASS LAW, for EVERY tournament (no group structure).

`Erdos902Switch.total_domination` conserved domination mass for circulant tournaments, where a
switch is available.  That was a statement about `Z_N`.  This file drops the group entirely and
proves the two facts in their general form, one an identity and one a sharp inequality.

Write `c_T(B)` for the number of vertices dominating every element of `B`, and `d+(x)` for the
out-degree.

⭐ THE IDENTITY (`total_domination_general`).  For every `j`,

      sum over j-sets B of c_T(B)   =   sum over x of C(d+(x), j)

because the `j`-sets dominated by `x` are exactly the `j`-subsets of its out-neighbourhood.

⭐ THE SHARP BOUND (`sum_choose_outdeg_le`).  For every tournament and every `j`,

      sum over x of C(d+(x), j)   <=   C(N, j+1)

with a one-line reason: send the pair `(x, B)` -- `x` dominating the `j`-set `B` -- to the
`(j+1)`-set `insert x B`.  That map is INJECTIVE, because `x` is a vertex of `insert x B`
beating all the others, and A TOURNAMENT HAS AT MOST ONE SUCH VERTEX (two would have to beat
each other).  At `j = 1` this is the identity `sum d+(x) = C(N,2)`; at `j = 2` it is the
classical "the number of 3-cycles is non-negative".  Here it is for all `j` at once.

⭐ THE CONSEQUENCE (`threshold_bound`).  If EVERY `j`-set is dominated `theta` times over then

      theta * (j+1)  <=  N - j.

⛔ AND THE HONEST READING, WHICH IS A NEGATIVE RESULT.  Combined with the `j`-fold
in-neighbourhood law -- in a tournament with `S_n`, the common in-neighbourhood of any `j`-set
carries `S_(n-j)`, so `theta = f(n-j)` is admissible -- this yields the family

      f(n)  >=  (j+1) * f(n-j) + j        for every 1 <= j <= n.

⛔ SCOPE OF THAT LAST CLAIM.  `threshold_bound` below is machine-checked.  The `j`-fold
in-neighbourhood law is proved in this estate only for `j = 1`
(`Erdos902ClosedForm.hasSle_induced`); the general `j` is the same three-line argument with a
set in place of a vertex, but it is NOT formalized here.  So the recursion family below is
STATED, not machine-checked, and only its `j = 1` instance is.

`j = 1` is exactly the recursion `f(n) >= 2 f(n-1) + 1` already in the estate, and EVERY LARGER
`j` IS WEAKER: iterating `j = 1` twice gives `4 f(n-2) + 3`, while `j = 2` gives only
`3 f(n-2) + 2`.  So this entire family bottoms out at `2^(n+1) - 1` and cannot reach the
Szekeres order `n 2^n`.  That is worth knowing precisely: the factor of `n` is not hiding in
higher-order domination counting, and an argument that closes it must leave this family.
-/
import Mathlib
import Erdos902Counting

open Finset

namespace Erdos902Mass

variable {V : Type*} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T]

/-- `x` dominates every element of `B`. -/
def DominatesAll (B : Finset V) (x : V) : Prop := ∀ b ∈ B, T x b

instance (B : Finset V) : DecidablePred (DominatesAll T B) := fun _ => by
  unfold DominatesAll; infer_instance

/-- The vertices dominating all of `B`. -/
def domSet (B : Finset V) : Finset V := univ.filter (DominatesAll T B)

/-- The out-neighbourhood of `x`. -/
def outN (x : V) : Finset V := univ.filter (fun y => T x y)

/-! ### The identity -/

/-- **THE MASS IDENTITY, for every tournament.**  The `j`-sets dominated by `x` are exactly the
`j`-subsets of `x`'s out-neighbourhood. -/
theorem total_domination_general (j : ℕ) :
    ∑ B ∈ (univ : Finset V).powersetCard j, (domSet T B).card
      = ∑ x : V, ((outN T x).card).choose j := by
  have hset : ∀ x : V,
      (((univ : Finset V).powersetCard j).filter (fun B => DominatesAll T B x)).card
        = ((outN T x).card).choose j := by
    intro x
    have hEq : ((univ : Finset V).powersetCard j).filter (fun B => DominatesAll T B x)
        = (outN T x).powersetCard j := by
      ext B
      simp only [Finset.mem_filter, Finset.mem_powersetCard, DominatesAll, outN,
        Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    rw [hEq, Finset.card_powersetCard]
  simp only [domSet, Finset.card_filter]
  rw [Finset.sum_comm]
  have hinner : ∀ x ∈ (univ : Finset V),
      (∑ B ∈ (univ : Finset V).powersetCard j, if DominatesAll T B x then 1 else 0)
        = ((outN T x).card).choose j := by
    intro x _
    rw [← Finset.card_filter]
    exact hset x
  exact Finset.sum_congr rfl hinner

/-! ### The sharp bound -/

/-- **AT MOST ONE DOMINANT VERTEX.**  In a tournament, a set has at most one member beating all
the others -- two such would have to beat each other. -/
theorem source_unique (h : IsTournament T) {B B' : Finset V} {x x' : V}
    (hx : DominatesAll T B x) (hx' : DominatesAll T B' x')
    (hxB : x ∉ B) (hxB' : x' ∉ B') (hEq : insert x B = insert x' B') : x = x' := by
  by_contra hne
  have h1 : x ∈ insert x' B' := by rw [← hEq]; exact Finset.mem_insert_self _ _
  have h2 : x' ∈ insert x B := by rw [hEq]; exact Finset.mem_insert_self _ _
  have hxB'mem : x ∈ B' := (Finset.mem_insert.mp h1).resolve_left hne
  have hx'Bmem : x' ∈ B := (Finset.mem_insert.mp h2).resolve_left (Ne.symm hne)
  exact h.asymm x x' (hx x' hx'Bmem) (hx' x hxB'mem)

/-- **THE SHARP BOUND.**  `(x, B) ↦ insert x B` is injective into the `(j+1)`-sets.

At `j = 1` this is `∑ d⁺(x) = C(N,2)`; at `j = 2` it is "the number of 3-cycles is at least
zero".  Here for all `j`. -/
theorem sum_choose_outdeg_le (h : IsTournament T) (j : ℕ) :
    ∑ x : V, ((outN T x).card).choose j ≤ (Fintype.card V).choose (j + 1) := by
  classical
  have hsig : ∑ x : V, ((outN T x).card).choose j
      = ((univ : Finset V).sigma (fun x => (outN T x).powersetCard j)).card := by
    rw [Finset.card_sigma]
    exact Finset.sum_congr rfl (fun x _ => (Finset.card_powersetCard _ _).symm)
  have hrhs : (Fintype.card V).choose (j + 1)
      = ((univ : Finset V).powersetCard (j + 1)).card := by
    rw [Finset.card_powersetCard, Finset.card_univ]
  rw [hsig, hrhs]
  refine Finset.card_le_card_of_injOn (fun p => insert p.1 p.2) ?_ ?_
  · rintro ⟨x, B⟩ hp
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powersetCard] at hp
    obtain ⟨-, hsub, hcard⟩ := hp
    have hxB : x ∉ B := by
      intro hmem
      have := hsub hmem
      simp only [outN, Finset.mem_filter] at this
      exact h.irrefl x this.2
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by rw [Finset.card_insert_of_notMem hxB, hcard]⟩
  · rintro ⟨x, B⟩ hp ⟨x', B'⟩ hq hEq
    have hEq' : insert x B = insert x' B' := hEq
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powersetCard] at hp hq
    have hdomx : DominatesAll T B x := by
      intro b hb
      have := hp.2.1 hb
      simpa [outN] using this
    have hdomx' : DominatesAll T B' x' := by
      intro b hb
      have := hq.2.1 hb
      simpa [outN] using this
    have hxB : x ∉ B := by
      intro hmem
      have := hp.2.1 hmem
      simp only [outN, Finset.mem_filter] at this
      exact h.irrefl x this.2
    have hxB' : x' ∉ B' := by
      intro hmem
      have := hq.2.1 hmem
      simp only [outN, Finset.mem_filter] at this
      exact h.irrefl x' this.2
    have hxx : x = x' := source_unique T h hdomx hdomx' hxB hxB' hEq'
    subst hxx
    have hBB : B = B' := by
      have h1 : (insert x B).erase x = (insert x B').erase x := by rw [hEq']
      rwa [Finset.erase_insert hxB, Finset.erase_insert hxB'] at h1
    subst hBB
    rfl

/-! ### The consequence -/

/-- If every `j`-set is dominated at least `θ` times, then `θ * C(N,j) ≤ C(N,j+1)`. -/
theorem threshold_le_choose (h : IsTournament T) (j θ : ℕ)
    (hall : ∀ B ∈ (univ : Finset V).powersetCard j, θ ≤ (domSet T B).card) :
    θ * ((Fintype.card V).choose j) ≤ (Fintype.card V).choose (j + 1) := by
  calc θ * ((Fintype.card V).choose j)
      = ∑ _B ∈ (univ : Finset V).powersetCard j, θ := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, smul_eq_mul,
          Nat.mul_comm]
    _ ≤ ∑ B ∈ (univ : Finset V).powersetCard j, (domSet T B).card := Finset.sum_le_sum hall
    _ = ∑ x : V, ((outN T x).card).choose j := total_domination_general T j
    _ ≤ _ := sum_choose_outdeg_le T h j

/-- **THE CLEAN FORM.**  `θ * (j+1) ≤ N - j`.  Robustness of domination is capped linearly by
the vertex count, for every tournament and every `j`. -/
theorem threshold_bound (h : IsTournament T) (j θ : ℕ) (hj : j ≤ Fintype.card V)
    (hall : ∀ B ∈ (univ : Finset V).powersetCard j, θ ≤ (domSet T B).card) :
    θ * (j + 1) ≤ Fintype.card V - j := by
  have hpos : 0 < (Fintype.card V).choose j := Nat.choose_pos hj
  have hkey := threshold_le_choose T h j θ hall
  have hid : (Fintype.card V).choose (j + 1) * (j + 1)
      = (Fintype.card V).choose j * (Fintype.card V - j) := Nat.choose_succ_right_eq _ _
  have hstep : θ * (j + 1) * ((Fintype.card V).choose j)
      ≤ ((Fintype.card V).choose j) * (Fintype.card V - j) := by
    calc θ * (j + 1) * ((Fintype.card V).choose j)
        = (θ * ((Fintype.card V).choose j)) * (j + 1) := by ring
      _ ≤ ((Fintype.card V).choose (j + 1)) * (j + 1) :=
          Nat.mul_le_mul_right _ hkey
      _ = ((Fintype.card V).choose j) * (Fintype.card V - j) := hid
  have := Nat.le_of_mul_le_mul_right (by linarith [hstep] : θ * (j + 1) * ((Fintype.card V).choose j)
      ≤ (Fintype.card V - j) * ((Fintype.card V).choose j)) hpos
  exact this

#print axioms total_domination_general
#print axioms source_unique
#print axioms sum_choose_outdeg_le
#print axioms threshold_le_choose
#print axioms threshold_bound

end Erdos902Mass
