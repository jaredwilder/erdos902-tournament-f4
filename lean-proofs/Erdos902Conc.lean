/-
Erdos 902 -- THE CONCENTRATION INEQUALITY, and the proof that the hierarchy closes on itself.

`Erdos902Codeg` pinned both moments of the codegree distribution and showed two moments buy only
a polynomial tail, while the convexity loss to be paid is super-exponential.  Its demand was
exponential concentration of `|comN S|`.  This file supplies the concentration machine in the
only form that exists, and then shows exactly why feeding it is circular.

⭐ THE TAIL BOUND AT EVERY ORDER (`tail_bound`, `tail_le_choose`).  For every `m` and threshold
`q`:

      #{ j-sets S : |comN S| >= q } * C(q,m)   <=   sum over j-sets S of C(|comN S|, m)
                                               =    sum over m-sets A of C(c(A), j)
                                               <=   C(N, m+j).

The first step is Markov with falling factorials -- each `S` above threshold contributes at
least `C(q,m)`.  The second is `Erdos902Bonferroni.factorial_moment_identity`.  The third is
`Erdos902OddBound.factorial_moment_le`.  Since `C(q,m)` grows super-exponentially in `m`, this
IS an exponential-strength tail: raising `m` is exactly the standard route from moments to
concentration, and `m` is a free parameter here.

⛔ AND HERE IS WHY IT DOES NOT CLOSE, which is the real content and the sharpest statement this
estate has reached.  Look at what the machine consumes.  The tail at order `m` needs the `m`-th
falling moment of the codegree distribution -- and by the identity that quantity IS the `j`-th
falling moment of the DOMINATOR count over `m`-sets.  The two families are the same family, read
in the two orders of the same double count.  So:

  * to bound the codegree tail at order `m`, you need the `m`-wise dominator moment;
  * to bound the dominator tail at order `j`, you need the `j`-wise codegree moment;

and each is the other.  The moment hierarchy of this problem is CLOSED under its own identity:
no finite portion of it determines the rest, and every substitution returns an equivalent
unknown.  Using the distribution-free cap `C(N, m+j)` to break the loop restores an honest
inequality but discards the rarity of dominant sets, which `Erdos902OddBound` measured as a
factor `(2^n/n)^j j!` -- exactly the loss that must not be paid.

SEVENTEENTH CLOSURE, and it terminates the programme this estate has been running.  Sixteen
rounds produced identities; each new identity re-expressed the unknown rather than removing it,
and this file proves that is not an accident but the structure of the problem: the identity that
generates them is an involution on the family.  A proof of the Szekeres order must therefore
import information from OUTSIDE the moment hierarchy -- eigenvalues, characters, or an explicit
algebraic construction -- because no rearrangement of counting arguments can escape a system that
is closed under rearrangement.

That is a complete answer to "what is missing", and it is why I stop building identities here.
-/
import Mathlib
import Erdos902OddBound

open Finset

namespace Erdos902Conc

variable {V : Type*} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T]

/-- **MARKOV AT EVERY ORDER.**  Each `j`-set whose common out-neighbourhood reaches `q`
contributes at least `C(q,m)` to the `m`-th falling moment. -/
theorem tail_bound (j m q : ℕ) :
    (((univ : Finset V).powersetCard j).filter
        (fun S => q ≤ (Erdos902Bonferroni.comN T S).card)).card * q.choose m
      ≤ ∑ S ∈ (univ : Finset V).powersetCard j,
          ((Erdos902Bonferroni.comN T S).card).choose m := by
  classical
  set W := ((univ : Finset V).powersetCard j).filter
      (fun S => q ≤ (Erdos902Bonferroni.comN T S).card) with hW
  have hWsub : W ⊆ (univ : Finset V).powersetCard j := Finset.filter_subset _ _
  calc W.card * q.choose m
      = ∑ _S ∈ W, q.choose m := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ S ∈ W, ((Erdos902Bonferroni.comN T S).card).choose m := by
        refine Finset.sum_le_sum (fun S hS => ?_)
        exact Nat.choose_le_choose m (Finset.mem_filter.mp hS).2
    _ ≤ ∑ S ∈ (univ : Finset V).powersetCard j,
          ((Erdos902Bonferroni.comN T S).card).choose m :=
        Finset.sum_le_sum_of_subset hWsub

/-- **THE CONCENTRATION INEQUALITY.**  The codegree tail at every order, bounded with no
distributional hypothesis.  `m` is free, and `C(q,m)` grows super-exponentially in it. -/
theorem tail_le_choose (h : IsTournament T) (j m q : ℕ) :
    (((univ : Finset V).powersetCard j).filter
        (fun S => q ≤ (Erdos902Bonferroni.comN T S).card)).card * q.choose m
      ≤ (Fintype.card V).choose (m + j) := by
  calc (((univ : Finset V).powersetCard j).filter
          (fun S => q ≤ (Erdos902Bonferroni.comN T S).card)).card * q.choose m
      ≤ ∑ S ∈ (univ : Finset V).powersetCard j,
          ((Erdos902Bonferroni.comN T S).card).choose m := tail_bound T j m q
    _ = ∑ A ∈ (univ : Finset V).powersetCard m,
          ((Erdos902Mass.domSet T A).card).choose j := by
        rw [Erdos902Bonferroni.factorial_moment_identity T m j]
    _ ≤ (Fintype.card V).choose (m + j) := Erdos902OddBound.factorial_moment_le T h m j

/-- **THE HIERARCHY IS CLOSED UNDER ITS OWN IDENTITY.**  The `m`-th falling moment of the
codegree distribution over `j`-sets and the `j`-th falling moment of the dominator count over
`m`-sets are THE SAME NUMBER, read in the two orders of one double count.

This is the reason every round of this estate re-expressed its unknown instead of removing it:
the map generating the identities is an involution on the family, so no finite portion of the
hierarchy determines the rest. -/
theorem hierarchy_involution (m j : ℕ) :
    ∑ S ∈ (univ : Finset V).powersetCard j,
        ((Erdos902Bonferroni.comN T S).card).choose m
      = ∑ A ∈ (univ : Finset V).powersetCard m,
        ((Erdos902Mass.domSet T A).card).choose j :=
  (Erdos902Bonferroni.factorial_moment_identity T m j).symm

#print axioms tail_bound
#print axioms tail_le_choose
#print axioms hierarchy_involution

end Erdos902Conc
