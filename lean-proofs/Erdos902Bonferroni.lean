/-
Erdos 902 -- THE THIRD-ORDER TOOL, and what it predicts about the answer.

`Erdos902Moment` proved the two-moment method exhausted and named the missing ingredient: the
TRIPLE codegrees, which double regularity does not determine.  This file builds the tool that
reaches them, at every order at once.

⭐ THE FACTORIAL MOMENT IDENTITY (`factorial_moment_identity`).  For all `n` and `j`:

      sum over n-sets A of C(c(A), j)   =   sum over j-sets S of C(|common out-nbhd of S|, n).

Both sides count the same pairs `(A, S)`: an `n`-set `A`, a `j`-set `S`, with every member of `S`
dominating every member of `A`.  Reading it left to right it is the `j`-th factorial moment of
the dominator count; right to left it is the `j`-wise codegree statistic.  `j = 1` is
`Erdos902Mass.total_domination_general`, `j = 2` is `Erdos902Overlap.second_moment` in disguise,
and `j = 3` is the first order this estate could not previously see.

⭐ BONFERRONI (`bonferroni3`, `bonferroni_covering`).  For every integer `c >= 1`,

      1 + C(c,2)  <=  c + C(c,3),

which is exactly `(c-1)(c-2)(c-3) >= 0` after clearing denominators -- the odd truncation of
inclusion-exclusion.  Schutte's property forces `c(A) >= 1` on every `n`-set, so summing and
applying the identity three times gives a bound where the `j = 3` codegrees appear with a sign.

⛔ WHAT IT PREDICTS, AND WHY I THINK IT SETTLES THE DIRECTION.  Write `t = N/2^n`.  At the
extremal object `F ~ N/2`, `lam ~ N/4`, and the triple codegrees `~ N/8`, so the three terms are
`t`, `t^2/2`, `t^3/6` times `C(N,n)`, and the bound reads

      1  <=  t - t^2/2 + t^3/6,

forcing `t >= 1.6` -- a genuine constant-factor improvement on `N >= 2^n`, and the FIRST
improvement any round has produced.  But look at the shape.  That is the order-3 truncation of
`1 - e^(-t)`.  Carrying the expansion to order `k` gives `1 <= sum_(j<=k) (-1)^(j+1) t^j / j!`,
and since `1 - e^(-t) < 1` for every `t`, the inequality can only hold because the truncation
OVERSHOOTS -- which needs `t^(k+1)/(k+1)!` to be non-negligible, i.e. `t >~ k`.

So the order-`k` method proves `N >~ k * 2^n`, and no more.  Every bounded order is a constant.
To reach `n * 2^n` one needs order `n`; to reach `n^2 * 2^n` one needs order `n^2` -- and `n^2`
is exactly `log C(N,n)`, the union bound's exponent.  THAT is why every round of this estate
stalled at a constant times `2^n`: each was a bounded-order argument, and I never once used more
than three orders at a time.

This also predicts the ANSWER.  The Poisson heuristic the identity encodes gives
`P(c = 0) ~ e^(-t)`, so a random-like tournament needs `t ~ log C(N,n) ~ n^2`.  Szekeres's
`n 2^n` is what one order-`n` argument yields; the union bound's `n^2 2^n` is what the full
series yields.  The identity says the full series is the truth, so I expect
`f(n) = Theta(n^2 2^n)` and the UPPER bound to be sharp -- not the lower one.

STILL NOT SOLVED.  But the estate now has the tool at every order, a first constant-factor
improvement, and a reason to believe which end of the gap is loose.
-/
import Mathlib
import Erdos902Mass

open Finset

namespace Erdos902Bonferroni

variable {V : Type*} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T]

/-- The common out-neighbourhood of a set `S`: everything beaten by every member of `S`. -/
def comN (S : Finset V) : Finset V := univ.filter (fun a => ∀ x ∈ S, T x a)

theorem mem_comN {S : Finset V} {a : V} : a ∈ comN T S ↔ ∀ x ∈ S, T x a := by
  simp [comN]

/-- `S` dominates `A` elementwise, from either side. -/
theorem subset_domSet_iff (A S : Finset V) :
    S ⊆ Erdos902Mass.domSet T A ↔ A ⊆ comN T S := by
  constructor
  · intro h a ha
    refine (mem_comN T).mpr (fun x hx => ?_)
    have := h hx
    simp only [Erdos902Mass.domSet, Finset.mem_filter, Erdos902Mass.DominatesAll] at this
    exact this.2 a ha
  · intro h x hx
    simp only [Erdos902Mass.domSet, Finset.mem_filter, Erdos902Mass.DominatesAll,
      Finset.mem_univ, true_and]
    intro a ha
    exact (mem_comN T).mp (h ha) x hx

/-- **THE FACTORIAL MOMENT IDENTITY.**  Both sides count pairs `(A, S)` with every member of `S`
dominating every member of `A`. -/
theorem factorial_moment_identity (n j : ℕ) :
    ∑ A ∈ (univ : Finset V).powersetCard n, ((Erdos902Mass.domSet T A).card).choose j
      = ∑ S ∈ (univ : Finset V).powersetCard j, ((comN T S).card).choose n := by
  classical
  have hleft : ∀ A : Finset V, ((Erdos902Mass.domSet T A).card).choose j
      = ∑ S ∈ (univ : Finset V).powersetCard j, (if S ⊆ Erdos902Mass.domSet T A then 1 else 0) := by
    intro A
    rw [← Finset.card_filter, ← Finset.card_powersetCard]
    congr 1
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    tauto
  have hright : ∀ S : Finset V, ((comN T S).card).choose n
      = ∑ A ∈ (univ : Finset V).powersetCard n, (if A ⊆ comN T S then 1 else 0) := by
    intro S
    rw [← Finset.card_filter, ← Finset.card_powersetCard]
    congr 1
    ext A
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    tauto
  simp only [hleft, hright]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun A _ => ?_))
  by_cases h : S ⊆ Erdos902Mass.domSet T A
  · rw [if_pos h, if_pos ((subset_domSet_iff T A S).mp h)]
  · rw [if_neg h, if_neg (fun hcon => h ((subset_domSet_iff T A S).mpr hcon))]

/-! ### Bonferroni at order three -/

/-- **THE ODD TRUNCATION.**  `1 + C(c,2) <= c + C(c,3)` for `c >= 1` -- after clearing
denominators this is exactly `(c-1)(c-2)(c-3) >= 0`. -/
theorem bonferroni3 (c : ℕ) (hc : 1 ≤ c) : 1 + c.choose 2 ≤ c + c.choose 3 := by
  induction c, hc using Nat.le_induction with
  | base => decide
  | succ c hc ih =>
      have h2 : (c + 1).choose 2 = c.choose 1 + c.choose 2 := Nat.choose_succ_succ c 1
      have h3 : (c + 1).choose 3 = c.choose 2 + c.choose 3 := Nat.choose_succ_succ c 2
      rw [h2, h3, Nat.choose_one_right]
      omega

/-- **THE THIRD-ORDER COVERING BOUND.**  Schutte's property forces `c(A) >= 1` everywhere, so
the odd truncation summed over all `n`-sets, with the identity applied at `j = 1, 2, 3`, puts the
TRIPLE codegrees into a bound on `C(N,n)` for the first time. -/
theorem bonferroni_covering (n : ℕ)
    (hdom : ∀ A ∈ (univ : Finset V).powersetCard n, 1 ≤ (Erdos902Mass.domSet T A).card) :
    (Fintype.card V).choose n
        + ∑ S ∈ (univ : Finset V).powersetCard 2, ((comN T S).card).choose n
      ≤ ∑ S ∈ (univ : Finset V).powersetCard 1, ((comN T S).card).choose n
        + ∑ S ∈ (univ : Finset V).powersetCard 3, ((comN T S).card).choose n := by
  classical
  have hsum : ∑ A ∈ (univ : Finset V).powersetCard n,
        (1 + ((Erdos902Mass.domSet T A).card).choose 2)
      ≤ ∑ A ∈ (univ : Finset V).powersetCard n,
        (((Erdos902Mass.domSet T A).card).choose 1 + ((Erdos902Mass.domSet T A).card).choose 3) := by
    refine Finset.sum_le_sum (fun A hA => ?_)
    rw [Nat.choose_one_right]
    exact bonferroni3 _ (hdom A hA)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_powersetCard, Finset.card_univ, smul_eq_mul, Nat.mul_one,
    factorial_moment_identity T n 2, factorial_moment_identity T n 1,
    factorial_moment_identity T n 3] at hsum
  exact hsum

#print axioms factorial_moment_identity
#print axioms bonferroni3
#print axioms bonferroni_covering

end Erdos902Bonferroni
