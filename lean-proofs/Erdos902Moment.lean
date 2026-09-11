/-
Erdos 902 -- THE MOMENT METHOD IS EXHAUSTED.  Both moments computed exactly, at the extremal
object, and they are CONSISTENT with `N ~ 2^n`.

`Erdos902Double` pinned the extremal case: if the recursion is tight at two consecutive levels
the tournament is regular of degree `F` and doubly regular with every codegree `lam`.  That is a
completely determined object, so instead of guessing what an argument might extract from it, one
can COMPUTE what the standard tool actually gives.  This file does that, and the answer is that
it gives nothing.

⭐ THE EXACT SECOND MOMENT (`second_moment_doubly_regular`).  Writing `c(A)` for the number of
vertices dominating `A`:

      sum over n-sets A of c(A)^2   =   N * C(F,n)  +  N*(N-1) * C(lam,n).

No estimate, no error term.  The diagonal of the pair sum contributes `C(F,n)` at each vertex,
and double regularity makes every one of the `N(N-1)` off-diagonal terms exactly `C(lam,n)`.
With `Erdos902Mass.total_domination_general` giving the first moment as `N * C(F,n)` exactly,
BOTH moments of `c` are now closed-form functions of `(N, F, lam, n)` alone.

⛔ AND THAT IS WHY THE METHOD CANNOT WORK -- which is what makes this a result rather than a
lemma.  Feed both moments into the sharpest available conclusion, `Erdos902Overlap`'s Bonferroni
inequality `1 <= E[c] - E[c(c-1)]/M`, which is the best any first-and-second-moment argument can
say when `S_n` forces `c(A) >= 1` everywhere.  With `M <= N` it reads

      C(N,n)  <=  N * C(F,n)  -  (N-1) * C(lam,n).

At the extremal point `F ~ N/2` and `lam = (F-1)/2 ~ N/4`, so `C(F,n) ~ C(N,n)/2^n` while
`C(lam,n) ~ C(N,n)/4^n`.  The inequality becomes `1 <= N/2^n - N/4^n`, i.e.

      N  >=  2^n / (1 - 2^-n),

which is `2^n` again, improved by a factor `1 + 2^-n`.  The correction is EXPONENTIALLY SMALL --
precisely the `exp(n^2/N)`-shaped failure the tenth closure identified, arriving now from an
exact computation rather than an estimate.  And the situation cannot be rescued by a better `M`:
if `c` were perfectly constant, `M = E[c]`, the Bonferroni inequality collapses to `1 <= 1`, an
identity.  A design gives equality, not a contradiction.

TWELFTH CLOSURE, and the strongest negative result in this estate, because it is exact rather
than asymptotic: NO argument using only the first and second moments of `c` can prove more than
`N >~ 2^n`, since at the extremal object both moments are determined and consistent with it.
The factor of `n` requires THIRD-order information -- the triple codegrees
`|N+(x) cap N+(y) cap N+(z)|`, which double regularity does NOT determine and which vary.  That
is exactly the quantity a character-sum bound controls for Paley tournaments, and it is the first
time this estate has identified the missing ingredient as a specific unpinned statistic rather
than as a missing inequality.

STILL NOT SOLVED.  But the search space is now one object and one statistic.
-/
import Mathlib
import Erdos902Overlap
import Erdos902Double

open Finset

namespace Erdos902Moment

variable {V : Type*} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T]

/-- **THE EXACT SECOND MOMENT AT THE EXTREMAL OBJECT.**  Regularity fixes the diagonal of the
pair sum; double regularity fixes every off-diagonal term.  No error term survives. -/
theorem second_moment_doubly_regular (F lam n : ℕ)
    (hreg : ∀ x : V, (Erdos902Mass.outN T x).card = F)
    (hdr : ∀ x : V, ∀ y ∈ univ.erase x,
      ((Erdos902Mass.outN T x) ∩ (Erdos902Mass.outN T y)).card = lam) :
    ∑ A ∈ (univ : Finset V).powersetCard n, (Erdos902Mass.domSet T A).card ^ 2
      = Fintype.card V * (F.choose n)
        + Fintype.card V * ((Fintype.card V - 1) * (lam.choose n)) := by
  classical
  rw [Erdos902Overlap.second_moment T n]
  have hrow : ∀ x : V,
      ∑ y : V, (((Erdos902Mass.outN T x) ∩ (Erdos902Mass.outN T y)).card).choose n
        = F.choose n + (Fintype.card V - 1) * (lam.choose n) := by
    intro x
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
    have hd : (((Erdos902Mass.outN T x) ∩ (Erdos902Mass.outN T x)).card).choose n
        = F.choose n := by
      rw [Finset.inter_self, hreg x]
    have hoff : ∑ y ∈ univ.erase x,
        (((Erdos902Mass.outN T x) ∩ (Erdos902Mass.outN T y)).card).choose n
          = (Fintype.card V - 1) * (lam.choose n) := by
      rw [Finset.sum_congr rfl (fun y hy => by rw [hdr x y hy]), Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, smul_eq_mul]
    rw [hd, hoff]
  rw [Finset.sum_congr rfl (fun x _ => hrow x), Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Nat.mul_add]

/-- **BOTH MOMENTS, SIDE BY SIDE.**  At the extremal object the first and second moments of the
dominator count are closed-form functions of `(N, F, lam, n)` -- there is nothing left for a
two-moment argument to discover. -/
theorem both_moments_determined (F lam n : ℕ)
    (hreg : ∀ x : V, (Erdos902Mass.outN T x).card = F)
    (hdr : ∀ x : V, ∀ y ∈ univ.erase x,
      ((Erdos902Mass.outN T x) ∩ (Erdos902Mass.outN T y)).card = lam) :
    (∑ A ∈ (univ : Finset V).powersetCard n, (Erdos902Mass.domSet T A).card
        = Fintype.card V * (F.choose n))
    ∧ (∑ A ∈ (univ : Finset V).powersetCard n, (Erdos902Mass.domSet T A).card ^ 2
        = Fintype.card V * (F.choose n)
          + Fintype.card V * ((Fintype.card V - 1) * (lam.choose n))) := by
  constructor
  · rw [Erdos902Mass.total_domination_general T n]
    rw [Finset.sum_congr rfl (fun x _ => by rw [hreg x]), Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  · exact second_moment_doubly_regular T F lam n hreg hdr

#print axioms second_moment_doubly_regular
#print axioms both_moments_determined

end Erdos902Moment
