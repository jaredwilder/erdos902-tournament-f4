/-
Erdos 902 -- THE CODEGREE DISTRIBUTION.  Its second moment is exactly determined too.

`Erdos902OddBound` proved the distribution-free cap and showed it insufficient, leaving a precise
demand: control the DISTRIBUTION of `|comN S|` over `j`-sets `S`, not merely its total.  Its
first moment was already pinned (`sum over j-sets S of |comN S| = sum over a of C(d-(a), j)`).
This file pins the second, by the same pairing one level up.

⭐ THE SECOND MOMENT (`codegree_second_moment`).  With no hypotheses at all:

      sum over j-sets S of |comN S|^2   =   sum over a,b of C(|N-(a) cap N-(b)|, j).

Both sides count triples `(S, a, b)` with every member of `S` beating both `a` and `b`.  The
left is the second moment of the codegree distribution; the right is built from the PAIRWISE
in-codegrees.

⭐ AT THE EXTREMAL OBJECT (`codegree_second_moment_doubly_regular`).  `Erdos902Double` forces
regularity of degree `F` and every pairwise in-codegree equal to `lam`, so the right side
collapses completely:

      sum over j-sets S of |comN S|^2   =   N * C(F,j)  +  N * ((N-1) * C(lam,j)).

So at the extremal object BOTH moments of the codegree distribution are closed-form in
`(N, F, lam, j)` -- exactly the distributional information the fifteenth closure demanded, at
every order `j` at once.

⛔ AND TWO MOMENTS ARE STILL NOT ENOUGH, which is worth stating because it is now the same
obstruction one level down.  Mean and variance give Chebyshev, hence
`#{S : |comN S| >= mu + k*sigma} <= C(N,j)/k^2` -- a POLYNOMIAL tail.  The convexity loss that
`Erdos902OddBound` measured is a factor `(2^n/n)^j j!`, which is super-exponential in `j`, so a
polynomial tail cannot pay for it.  Closing needs EXPONENTIAL concentration of `|comN S|`, and
exponential concentration is not a two-moment statement -- it needs all moments, which for these
tournaments is precisely a character-sum estimate.

SIXTEENTH CLOSURE, and the pattern is now exact and self-similar.  At every level this estate has
climbed -- dominator counts, then codegrees -- the first two moments are exactly computable from
regularity and double regularity, and the first two moments are never enough, because the loss
being paid for is exponential while two moments buy only polynomial control.  That is one
sentence covering all sixteen rounds, and it says the remaining ingredient is not another
identity: it is a concentration inequality.
-/
import Mathlib
import Erdos902Bonferroni
import Erdos902Cover

open Finset

namespace Erdos902Codeg

variable {V : Type*} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T]

/-- `a` is beaten by every member of `S` exactly when `S` sits inside `N⁻(a)`. -/
theorem mem_comN_iff_subset (S : Finset V) (a : V) :
    a ∈ Erdos902Bonferroni.comN T S ↔ S ⊆ Erdos902Cover.inN T a := by
  rw [Erdos902Bonferroni.mem_comN]
  constructor
  · intro h x hx
    simpa [Erdos902Cover.inN] using h x hx
  · intro h x hx
    simpa [Erdos902Cover.inN] using h hx

/-- **THE SECOND MOMENT OF THE CODEGREE DISTRIBUTION.**  Both sides count triples `(S, a, b)`
with every member of `S` beating both `a` and `b`.  No hypotheses. -/
theorem codegree_second_moment (j : ℕ) :
    ∑ S ∈ (univ : Finset V).powersetCard j, ((Erdos902Bonferroni.comN T S).card) ^ 2
      = ∑ a : V, ∑ b : V,
          (((Erdos902Cover.inN T a) ∩ (Erdos902Cover.inN T b)).card).choose j := by
  classical
  have hcard : ∀ S : Finset V, (Erdos902Bonferroni.comN T S).card
      = ∑ a : V, (if S ⊆ Erdos902Cover.inN T a then 1 else 0) := by
    intro S
    rw [← Finset.card_filter]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact mem_comN_iff_subset T S a
  have hsq : ∀ S : Finset V, ((Erdos902Bonferroni.comN T S).card) ^ 2
      = ∑ a : V, ∑ b : V,
          (if S ⊆ Erdos902Cover.inN T a ∧ S ⊆ Erdos902Cover.inN T b then 1 else 0) := by
    intro S
    rw [sq, hcard S, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    by_cases h1 : S ⊆ Erdos902Cover.inN T a <;> by_cases h2 : S ⊆ Erdos902Cover.inN T b <;>
      simp [h1, h2]
  have hpair : ∀ a b : V,
      (((univ : Finset V).powersetCard j).filter
        (fun S => S ⊆ Erdos902Cover.inN T a ∧ S ⊆ Erdos902Cover.inN T b)).card
        = (((Erdos902Cover.inN T a) ∩ (Erdos902Cover.inN T b)).card).choose j := by
    intro a b
    have hEq : ((univ : Finset V).powersetCard j).filter
        (fun S => S ⊆ Erdos902Cover.inN T a ∧ S ⊆ Erdos902Cover.inN T b)
        = ((Erdos902Cover.inN T a) ∩ (Erdos902Cover.inN T b)).powersetCard j := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_inter_iff,
        Finset.subset_univ, true_and]
      tauto
    rw [hEq, Finset.card_powersetCard]
  simp only [hsq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Finset.card_filter]
  exact hpair a b

/-- **AT THE EXTREMAL OBJECT.**  Regularity and double regularity collapse the right-hand side,
so the second moment of the codegree distribution is closed-form at every order `j`. -/
theorem codegree_second_moment_doubly_regular (F lam j : ℕ)
    (hin : ∀ a : V, (Erdos902Cover.inN T a).card = F)
    (hdr : ∀ a : V, ∀ b ∈ univ.erase a,
      ((Erdos902Cover.inN T a) ∩ (Erdos902Cover.inN T b)).card = lam) :
    ∑ S ∈ (univ : Finset V).powersetCard j, ((Erdos902Bonferroni.comN T S).card) ^ 2
      = Fintype.card V * (F.choose j)
        + Fintype.card V * ((Fintype.card V - 1) * (lam.choose j)) := by
  classical
  rw [codegree_second_moment T j]
  have hrow : ∀ a : V,
      ∑ b : V, (((Erdos902Cover.inN T a) ∩ (Erdos902Cover.inN T b)).card).choose j
        = F.choose j + (Fintype.card V - 1) * (lam.choose j) := by
    intro a
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    have hd : (((Erdos902Cover.inN T a) ∩ (Erdos902Cover.inN T a)).card).choose j
        = F.choose j := by
      rw [Finset.inter_self, hin a]
    have hoff : ∑ b ∈ univ.erase a,
        (((Erdos902Cover.inN T a) ∩ (Erdos902Cover.inN T b)).card).choose j
          = (Fintype.card V - 1) * (lam.choose j) := by
      rw [Finset.sum_congr rfl (fun b hb => by rw [hdr a b hb]), Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, smul_eq_mul]
    rw [hd, hoff]
  rw [Finset.sum_congr rfl (fun a _ => hrow a), Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Nat.mul_add]

#print axioms mem_comN_iff_subset
#print axioms codegree_second_moment
#print axioms codegree_second_moment_doubly_regular

end Erdos902Codeg
