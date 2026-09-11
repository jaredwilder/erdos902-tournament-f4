/-
Erdos 902 -- THE TOOL AT EVERY ORDER.  Bonferroni is an exact identity, and the remainder is
the thing worth naming.

`Erdos902Bonferroni` proved the order-3 case and showed the pattern: an order-`k` argument yields
`N >~ k * 2^n`.  So the Szekeres order needs order `n`, and the union bound's order needs `n^2`.
This file supplies the tool at every order, which is the only way any of those is reachable.

⭐ THE ALTERNATING IDENTITY (`alt_choose_odd`).  For `c >= 1` and every `r`:

      sum_(i<=r) C(c, 2i+1)   =   1  +  sum_(i<r) C(c, 2i+2)  +  C(c-1, 2r+1).

This is `sum_(j<=k) (-1)^j C(c,j) = (-1)^k C(c-1,k)` at odd `k = 2r+1`, rearranged so that no
subtraction survives.  It is an EQUALITY: Bonferroni's inequality is what remains after throwing
away the final term, and that term -- `C(c-1, 2r+1)` -- is exactly the slack a truncated
inclusion-exclusion discards.

⭐ THE COVERING BOUND AT EVERY ODD ORDER (`bonferroni_general`).  Schutte's property gives
`c(A) >= 1` on every `n`-set, so summing the identity over all `n`-sets and applying
`Erdos902Bonferroni.factorial_moment_identity` at each `j` gives, for every `r`:

      C(N,n)  +  sum over even j <= 2r+1 of T_j   <=   sum over odd j <= 2r+1 of T_j,

where `T_j = sum over j-sets S of C(|common out-nbhd of S|, n)`.  Order 3 was
`Erdos902Bonferroni.bonferroni_covering`; this is every order at once, and `r` is now a free
parameter that an argument may choose as a function of `n`.

⛔ WHAT REMAINS, STATED EXACTLY.  Taking `r ~ n/2` is what would deliver `N >~ n 2^n`.  The
obstruction is no longer the tool -- it is that `T_j` for `3 <= j <= 2r+1` needs UPPER bounds on
the odd terms, and the estate has exact values only at `j = 1` and `j = 2` (regularity and
double regularity).  For `j >= 3` only the TOTAL is pinned:
`sum over j-sets S of |comN S| = N * C(F,j)`, while the distribution is free, and an upper bound
on `sum_S C(|comN S|, n)` needs the distribution because `C(-, n)` is convex.

So the honest state after fourteen rounds is a single sentence: EVERY ingredient of the
order-`n` argument is now proved except upper bounds on the odd-order codegree sums, and that
missing piece is precisely what a character-sum estimate supplies for Paley tournaments.  The
gap between this estate and the Szekeres order is one family of inequalities, named.
-/
import Mathlib
import Erdos902Bonferroni

open Finset

namespace Erdos902Order

variable {V : Type*} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T]

/-! ### The alternating identity -/

/-- **THE ALTERNATING IDENTITY.**  `sum_(j<=k) (-1)^j C(c,j) = (-1)^k C(c-1,k)` at odd `k`,
written without subtraction.  The final term is the slack Bonferroni discards. -/
theorem alt_choose_odd (c : ℕ) (hc : 1 ≤ c) (r : ℕ) :
    ∑ i ∈ Finset.range (r + 1), c.choose (2 * i + 1)
      = 1 + (∑ i ∈ Finset.range r, c.choose (2 * i + 2)) + (c - 1).choose (2 * r + 1) := by
  induction r with
  | zero =>
      simp only [Finset.range_one, Finset.sum_singleton, Finset.range_zero, Finset.sum_empty,
        Nat.mul_zero, Nat.zero_add]
      rw [Nat.choose_one_right, Nat.choose_one_right]
      omega
  | succ r ih =>
      obtain ⟨d, hd⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
      subst hd
      simp only [Nat.add_sub_cancel] at ih ⊢
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      -- normalise the new index to `2*r+3` so Pascal applies directly
      have hi1 : 2 * (r + 1) + 1 = 2 * r + 3 := by ring
      rw [hi1]
      have hc1 : (d + 1).choose (2 * r + 3)
          = d.choose (2 * r + 2) + d.choose (2 * r + 3) := by
        have hj : 2 * r + 3 = 2 * r + 2 + 1 := by ring
        rw [hj]; exact Nat.choose_succ_succ d (2 * r + 2)
      have hc2 : (d + 1).choose (2 * r + 2)
          = d.choose (2 * r + 1) + d.choose (2 * r + 2) := by
        have hj : 2 * r + 2 = 2 * r + 1 + 1 := by ring
        rw [hj]; exact Nat.choose_succ_succ d (2 * r + 1)
      rw [hc1, hc2]
      ring

/-- Bonferroni at odd order, as an inequality: drop the remainder. -/
theorem bonferroni_odd (c : ℕ) (hc : 1 ≤ c) (r : ℕ) :
    1 + (∑ i ∈ Finset.range r, c.choose (2 * i + 2))
      ≤ ∑ i ∈ Finset.range (r + 1), c.choose (2 * i + 1) := by
  rw [alt_choose_odd c hc r]
  omega

/-! ### The covering bound at every odd order -/

/-- **THE COVERING BOUND AT EVERY ODD ORDER.**  `r` is a free parameter; order 3 is `r = 1`.
Reaching the Szekeres order needs `r ~ n/2`, which this makes expressible for the first time. -/
theorem bonferroni_general (n r : ℕ)
    (hdom : ∀ A ∈ (univ : Finset V).powersetCard n, 1 ≤ (Erdos902Mass.domSet T A).card) :
    (Fintype.card V).choose n
        + ∑ i ∈ Finset.range r,
            (∑ S ∈ (univ : Finset V).powersetCard (2 * i + 2),
              ((Erdos902Bonferroni.comN T S).card).choose n)
      ≤ ∑ i ∈ Finset.range (r + 1),
            (∑ S ∈ (univ : Finset V).powersetCard (2 * i + 1),
              ((Erdos902Bonferroni.comN T S).card).choose n) := by
  classical
  have hsum : ∑ A ∈ (univ : Finset V).powersetCard n,
        (1 + ∑ i ∈ Finset.range r, ((Erdos902Mass.domSet T A).card).choose (2 * i + 2))
      ≤ ∑ A ∈ (univ : Finset V).powersetCard n,
        (∑ i ∈ Finset.range (r + 1), ((Erdos902Mass.domSet T A).card).choose (2 * i + 1)) := by
    refine Finset.sum_le_sum (fun A hA => bonferroni_odd _ (hdom A hA) r)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    smul_eq_mul, Nat.mul_one, Finset.sum_comm, Finset.sum_comm
      (s := (univ : Finset V).powersetCard n) (t := Finset.range (r + 1))] at hsum
  rw [Finset.sum_congr rfl
        (fun i _ => Erdos902Bonferroni.factorial_moment_identity T n (2 * i + 2)),
      Finset.sum_congr rfl
        (fun i _ => Erdos902Bonferroni.factorial_moment_identity T n (2 * i + 1))] at hsum
  exact hsum

#print axioms alt_choose_odd
#print axioms bonferroni_odd
#print axioms bonferroni_general

end Erdos902Order
