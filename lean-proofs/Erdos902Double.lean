/-
Erdos 902 -- DOUBLE RIGIDITY.  Tightness at two consecutive levels forces DOUBLE REGULARITY.

`Erdos902Rigid` showed that if the recursion `f(n) >= 2 f(n-1) + 1` is tight then the tournament
is regular and every in-neighbourhood is extremal.  That is rigidity at ONE level.  This file
pushes it to two, and the escalation is the first mechanism in this estate that is STRUCTURAL
rather than an `exp(n^2/N)` correction -- which is exactly what the tenth closure said was
needed.

⭐ THE CODEGREE IDENTITY (`codegree_sum`).  Summing the common in-neighbourhood over ALL ordered
pairs is a pure double count, taken at the vertex doing the beating:

      sum over x,y of |N-(x) cap N-(y)|   =   sum over z of d+(z)^2.

⭐ DOUBLE RIGIDITY (`double_rigidity`).  Let the recursion be tight at level `n`, so the
tournament is regular with every degree `F` (`Erdos902Rigid.regular_at_bound`).  Let `F2` bound
the common in-neighbourhoods below -- in a Schutte tournament `F2 = f(n-2)`, since the common
in-neighbourhood of any two vertices carries `S_(n-2)`.  The identity forces

      sum over distinct x,y of |N-(x) cap N-(y)|   =   N * F * (F-1)

across `N * (N-1) = N * 2F` ordered pairs, so the AVERAGE codegree is exactly `(F-1)/2`.  Hence
if `F = 2*F2 + 1` -- the recursion tight at level `n-1` TOO -- every codegree equals `F2`
EXACTLY, because integers at least `F2` averaging `F2` are constant.  The tournament is DOUBLY
REGULAR.

⭐ WHY THAT MATTERS.  Doubly regular tournaments are not a soft class.  They exist only on
`N = 4t+3` vertices, they are equivalent to skew-Hadamard matrices of order `N+1`, and combined
with `Erdos902Rigid.reach_eq_internal_indeg` every in-neighbourhood is then a REGULAR tournament
on `F` vertices which must itself be an extremal `S_(n-1)` example.  At `n = 3` this is the whole
content of `f(3) = 19 > 15`: a 15-vertex example would have to be doubly regular with all fifteen
in-neighbourhoods isomorphic to the Paley tournament on 7 points.

⛔ WHAT IS PROVED AND WHAT IS NOT.  `codegree_sum` and `double_rigidity` are proved.  The step
from "doubly regular with extremal in-neighbourhoods" to "no such tournament exists" is NOT
proved, and I could not find it.  Divisibility does not close it: `N = 2F+1` with `F = 2*F2+1`
gives `N = 4*F2+3`, which is exactly the residue doubly regular tournaments require, so the
arithmetic is CONSISTENT rather than contradictory -- the extremal configuration passes every
counting and congruence test this estate can apply.

ELEVENTH CLOSURE, and the first that changes the KIND of obstruction.  Ten rounds produced
inequalities whose corrections vanished at `N ~ 2^n`.  This produces a structural classification
instead: the extremal case is not merely regular, it is skew-Hadamard.  A proof of the Szekeres
order can now be attempted against a named finite family rather than an arbitrary tournament --
a different problem, and a better-posed one.
-/
import Mathlib
import Erdos902Rigid

open Finset

namespace Erdos902Double

variable {V : Type*} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T]

abbrev inN (v : V) : Finset V := Erdos902Cover.inN T v
abbrev outN (v : V) : Finset V := Erdos902Mass.outN T v

/-! ### The codegree identity -/

/-- The common in-neighbourhood of `x` and `y` is the set of vertices beating both. -/
theorem inter_inN_eq (x y : V) :
    (inN T x) ∩ (inN T y) = univ.filter (fun z => T z x ∧ T z y) := by
  ext z
  simp [Erdos902Cover.inN, Finset.mem_inter]

theorem card_outN (z : V) : (outN T z).card = ∑ x : V, (if T z x then 1 else 0) := by
  simp only [Erdos902Mass.outN]
  rw [Finset.card_filter]

/-- **THE CODEGREE IDENTITY.**  Summed over all ordered pairs, common in-neighbourhoods count
each vertex once per ordered pair of vertices it beats. -/
theorem codegree_sum :
    ∑ x : V, ∑ y : V, ((inN T x) ∩ (inN T y)).card = ∑ z : V, ((outN T z).card) ^ 2 := by
  have hpt : ∀ x y : V, ((inN T x) ∩ (inN T y)).card
      = ∑ z : V, (if T z x ∧ T z y then 1 else 0) := by
    intro x y
    rw [inter_inN_eq, Finset.card_filter]
  have hsq : ∀ z : V, ((outN T z).card) ^ 2
      = ∑ x : V, ∑ y : V, (if T z x ∧ T z y then 1 else 0) := by
    intro z
    rw [sq, card_outN T z, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    by_cases h1 : T z x <;> by_cases h2 : T z y <;> simp [h1, h2]
  simp only [hpt, hsq]
  rw [show (∑ x : V, ∑ y : V, ∑ z : V, (if T z x ∧ T z y then 1 else 0))
        = (∑ x : V, ∑ z : V, ∑ y : V, (if T z x ∧ T z y then 1 else 0)) from
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)]
  exact Finset.sum_comm

/-! ### Double rigidity -/

/-- **DOUBLE RIGIDITY.**  With the tournament regular of degree `F`, if every codegree of a
distinct pair is at least `F2` and `F = 2*F2 + 1`, then every such codegree is EXACTLY `F2`:
the tournament is doubly regular.

The average codegree over distinct pairs is forced to `(F-1)/2 = F2`, and a family of integers
each at least `F2` whose average is `F2` is constant. -/
theorem double_rigidity (F F2 : ℕ) (hN : Fintype.card V = 2 * F + 1)
    (hreg : ∀ z : V, (outN T z).card = F)
    (hin : ∀ z : V, (inN T z).card = F)
    (hcod : ∀ x : V, ∀ y ∈ univ.erase x, F2 ≤ ((inN T x) ∩ (inN T y)).card)
    (htight : F = 2 * F2 + 1) :
    ∀ x : V, ∀ y ∈ univ.erase x, ((inN T x) ∩ (inN T y)).card = F2 := by
  classical
  have hdiag : ∀ x : V, ((inN T x) ∩ (inN T x)).card = F := by
    intro x; rw [Finset.inter_self]; exact hin x
  have hsplit : ∀ x : V, ∑ y : V, ((inN T x) ∩ (inN T y)).card
      = F + ∑ y ∈ univ.erase x, ((inN T x) ∩ (inN T y)).card := by
    intro x
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), hdiag x]
  -- total over ordered pairs, with the diagonal separated out
  have htotal : Fintype.card V * F
      + ∑ x : V, ∑ y ∈ univ.erase x, ((inN T x) ∩ (inN T y)).card
      = Fintype.card V * (F * F) := by
    have h1 : ∑ x : V, ∑ y : V, ((inN T x) ∩ (inN T y)).card
        = Fintype.card V * F + ∑ x : V, ∑ y ∈ univ.erase x, ((inN T x) ∩ (inN T y)).card := by
      simp only [hsplit]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    have h2 : ∑ z : V, ((outN T z).card) ^ 2 = Fintype.card V * (F * F) := by
      have : ∀ z : V, ((outN T z).card) ^ 2 = F * F := by
        intro z; rw [hreg z, sq]
      rw [Finset.sum_congr rfl (fun z _ => this z), Finset.sum_const, Finset.card_univ,
        smul_eq_mul]
    have h3 := codegree_sum T
    omega
  have hcount : ∀ x : V, (univ.erase x).card = 2 * F := by
    intro x
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hN]
    omega
  -- the off-diagonal total is exactly the minimum permitted by `hcod`
  have hleft : ∑ x : V, ∑ _y ∈ univ.erase x, F2 = Fintype.card V * (2 * F * F2) := by
    have hrow : ∀ x : V, ∑ _y ∈ univ.erase x, F2 = 2 * F * F2 := by
      intro x
      rw [Finset.sum_const, hcount x, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun x _ => hrow x), Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  have hexpand : Fintype.card V * (F * F)
      = Fintype.card V * (2 * F * F2) + Fintype.card V * F := by
    have hFF : F * F = 2 * F * F2 + F := by rw [htight]; ring
    rw [hFF, Nat.mul_add]
  have hlow : ∑ x : V, ∑ _y ∈ univ.erase x, F2
      = ∑ x : V, ∑ y ∈ univ.erase x, ((inN T x) ∩ (inN T y)).card := by
    rw [hleft]; omega
  -- integers at least `F2` whose total is the minimum are all equal to `F2`
  have hrow := (Finset.sum_eq_sum_iff_of_le
    (fun x (_ : x ∈ (univ : Finset V)) =>
      Finset.sum_le_sum (fun i hi => hcod x i hi))).mp hlow
  intro x y hy
  have hxrow := hrow x (Finset.mem_univ x)
  exact ((Finset.sum_eq_sum_iff_of_le (fun i hi => hcod x i hi)).mp hxrow y hy).symm

#print axioms codegree_sum
#print axioms double_rigidity

end Erdos902Double
