/-
Erdos 902 -- THE OVERLAP INEQUALITY: the first second-moment statement in this estate.

Six closures agreed on one thing.  Whatever the sets counted -- entire, higher-order, covering,
split, straddling -- every bound was a FIRST-MOMENT statement about a single vertex `v`: bound
`|N-(v)|`, then average over `v`.  All six landed on `2^k`.  The instruction the sixth left was
to find a statement about how the neighbourhoods of DIFFERENT vertices overlap.

Here it is.  Write `c(A)` for the number of vertices dominating `A`, and `M` for the largest
value `c` takes on a `k`-set.

⭐ THE POINTWISE LEVER (`pointwise_lever`).  For every integer `c` with `1 <= c <= M`,

      M + c^2  <=  (M+1) * c,

since the difference is `(c-1)(M-c) >= 0`.  It is an equality at BOTH ends, `c = 1` and `c = M`,
which is what makes it lossless: it charges nothing except the spread of `c` itself.

⭐ THE SECOND MOMENT (`second_moment`).  Summing `c(A)^2` over `k`-sets counts ordered pairs of
common dominators, so it is exactly an OVERLAP sum:

      sum over A of c(A)^2  =  sum over x, y of C(|N+(x) cap N+(y)|, k).

⭐ THE OVERLAP INEQUALITY (`overlap_inequality`).  Property `S_k` forces `c(A) >= 1` for every
`A`, so summing the lever over all `k`-sets gives

    M * C(N,k)  +  sum over x,y of C(|N+(x) cap N+(y)|, k)   <=   (M+1) * sum over x of C(d+(x), k).

Two different vertices finally appear in the same inequality, and the correction subtracted from
the first-moment bound is precisely the total pairwise overlap.

⛔ MEASURED, AND IT IS THE SEVENTH CLOSURE -- BUT IT IS THE ONE THAT NAMES THE TARGET.
Splitting off the diagonal `x = y` turns it into `C(N,k) <= S1 - (1/M) * (off-diagonal overlap)`.
In the regular regime the typical overlap is about `N/4`, so `C(N/4,k)` is smaller than
`C(N/2,k)` by a factor `2^k`, and the correction improves `N >= 2^k` only to
`N >= 2^k/(1 - 2^-k)`.  The order is untouched.

BUT THE REASON IS NOW A SINGLE NAMED QUANTITY.  The correction is divided by `M`, and `M` is the
maximum number of dominators of any `k`-set.  If `M` were within a constant of the MEAN number
of dominators, the same inequality would force `mu <= O(1)`, i.e. `N = O(2^k)` would be
contradicted and the true order would follow.  The entire remaining gap is therefore:

      HOW UNEVEN CAN DOMINATION BE?  -- bound max_A c(A) against its mean.

That is the first time in this estate the obstruction is one number rather than a direction, and
it is a statement purely about overlaps of out-neighbourhoods.
-/
import Mathlib
import Erdos902Mass

open Finset

namespace Erdos902Overlap

variable {V : Type*} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T]

/-! ### The pointwise lever -/

/-- **THE LEVER.**  `M + c^2 ≤ (M+1) c` for `1 ≤ c ≤ M`, with equality at both ends -- the
difference is exactly `(c-1)(M-c)`. -/
theorem pointwise_lever {c M : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ M) : M + c ^ 2 ≤ (M + 1) * c := by
  obtain ⟨e, rfl⟩ : ∃ e, c = 1 + e := ⟨c - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, M = (1 + e) + d := ⟨M - (1 + e), by omega⟩
  nlinarith [Nat.zero_le (d * e)]

/-! ### The second moment is an overlap sum -/

/-- **THE SECOND MOMENT.**  `∑ c(A)^2` counts ordered pairs of common dominators, so it is
exactly the total pairwise overlap of out-neighbourhoods. -/
theorem second_moment (k : ℕ) :
    ∑ A ∈ (univ : Finset V).powersetCard k, (Erdos902Mass.domSet T A).card ^ 2
      = ∑ x : V, ∑ y : V,
          (((Erdos902Mass.outN T x) ∩ (Erdos902Mass.outN T y)).card).choose k := by
  have hpt : ∀ A : Finset V, (Erdos902Mass.domSet T A).card ^ 2
      = ∑ x : V, ∑ y : V,
          (if Erdos902Mass.DominatesAll T A x ∧ Erdos902Mass.DominatesAll T A y then 1 else 0) := by
    intro A
    rw [sq, Erdos902Mass.domSet, Finset.card_filter, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    by_cases h1 : Erdos902Mass.DominatesAll T A x <;>
      by_cases h2 : Erdos902Mass.DominatesAll T A y <;> simp [h1, h2]
  have hpair : ∀ x y : V,
      (((univ : Finset V).powersetCard k).filter
          (fun A => Erdos902Mass.DominatesAll T A x ∧ Erdos902Mass.DominatesAll T A y)).card
        = (((Erdos902Mass.outN T x) ∩ (Erdos902Mass.outN T y)).card).choose k := by
    intro x y
    have hEq : ((univ : Finset V).powersetCard k).filter
        (fun A => Erdos902Mass.DominatesAll T A x ∧ Erdos902Mass.DominatesAll T A y)
        = ((Erdos902Mass.outN T x) ∩ (Erdos902Mass.outN T y)).powersetCard k := by
      ext A
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Erdos902Mass.DominatesAll,
        Erdos902Mass.outN, Finset.subset_iff, Finset.mem_inter, Finset.mem_filter,
        Finset.mem_univ, true_and, forall_and]
      tauto
    rw [hEq, Finset.card_powersetCard]
  simp only [hpt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [← Finset.card_filter]
  exact hpair x y

/-! ### The overlap inequality -/

/-- **THE OVERLAP INEQUALITY.**  Two different vertices in one bound at last: the correction to
the first-moment count is exactly the total pairwise overlap, damped by `M`. -/
theorem overlap_inequality (k M : ℕ)
    (hdom : ∀ A ∈ (univ : Finset V).powersetCard k, 1 ≤ (Erdos902Mass.domSet T A).card)
    (hmax : ∀ A ∈ (univ : Finset V).powersetCard k, (Erdos902Mass.domSet T A).card ≤ M) :
    M * ((Fintype.card V).choose k)
        + ∑ x : V, ∑ y : V, (((Erdos902Mass.outN T x) ∩ (Erdos902Mass.outN T y)).card).choose k
      ≤ (M + 1) * ∑ x : V, ((Erdos902Mass.outN T x).card).choose k := by
  have hsum : ∑ A ∈ (univ : Finset V).powersetCard k,
      (M + (Erdos902Mass.domSet T A).card ^ 2)
        ≤ ∑ A ∈ (univ : Finset V).powersetCard k, (M + 1) * (Erdos902Mass.domSet T A).card :=
    Finset.sum_le_sum (fun A hA => pointwise_lever (hdom A hA) (hmax A hA))
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    smul_eq_mul, second_moment T k, ← Finset.mul_sum,
    Erdos902Mass.total_domination_general T k] at hsum
  rw [Nat.mul_comm M ((Fintype.card V).choose k)]
  exact hsum

#print axioms pointwise_lever
#print axioms second_moment
#print axioms overlap_inequality

end Erdos902Overlap
