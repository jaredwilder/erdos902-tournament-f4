/-
Erdos 902 -- THE COVERING LAW: what the tail actually demands of an in-neighbourhood.

Three closures so far said where the factor of `n` is NOT.  Destruction multiplicity is forced
(`Erdos902Switch`), the mean is not a potential's to move (`mass_conservation`), and
higher-order domination counting bottoms out at `2^(n+1)-1` (`Erdos902Mass`).  What is left is
the tail: not how many dominators a typical `k`-set has, but what the WORST one is forced to have.

⭐ THE COVERING LAW (`inNbhd_covers`).  The estate already knows that in a tournament with
`S_(k+1)` the in-neighbourhood `N-(v)` carries `S_k` -- a statement about the `k`-sets INSIDE
`N-(v)`.  That is far from all of it.  The truth is:

    N-(v) dominates EVERY k-set of the whole tournament that avoids v.

Proof in one line: dominate `A + {v}`; the dominator beats `v`, so it lies in `N-(v)`, and it
beats `A`.  Nothing about `A` being inside `N-(v)` was ever used.

So `N-(v)` is not merely a smaller Schutte tournament sitting inside.  It is a COVERING DESIGN
for the `k`-subsets of `V \ {v}`, using its own out-neighbourhoods as blocks.  That is a
genuinely stronger demand, and it is a demand on the TAIL: every single `k`-set must be hit,
not most of them.

⭐ THE COUNT (`cover_count`).  Each `w` in `N-(v)` covers at most `C(d+(w), k)` of the
`C(N-1, k)` sets that must be covered, so

    C(N-1, k)  <=  sum over w in N-(v) of C(d+(w), k)   <=  |N-(v)| * C(d_max, k).

⛔ AND HERE IS THE HONEST MEASUREMENT OF IT.  With `d_max <= (N-1)/2` this gives

    |N-(v)|  >=  C(N-1,k) / C((N-1)/2, k)  ~  2^k,

so the covering law, USED AS A COUNT, yields `N >~ 2^(k+1)` -- the same barrier as the
recursion, not better.  The ratio is `2^k * prod (1 + i/(N-1))`, and at `N ~ k 2^k` that
correction factor is `exp(k^2/2N) = exp(k/2^(k+1))`, which tends to 1.  The factor of `k` is
NOT in this count either.

That is the fourth closure, and it is the sharpest one, because it says where the factor must
be: `N-(v)` has to be simultaneously (a) a Schutte tournament on `S_k` and (b) a covering design
for everything outside.  Counting (a) gives `2^k`.  Counting (b) gives `2^k`.  Neither counts
the INTERACTION -- an extremal `S_k` tournament is a tight object, and the claim that it can
ALSO spend its out-neighbourhoods covering the whole complement is what should fail.  Any proof
of the Szekeres order must exploit that conflict structurally; no first-moment count of either
property alone can reach it.
-/
import Mathlib
import Erdos902ClosedForm
import Erdos902Mass

open Finset

namespace Erdos902Cover

variable {V : Type*} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T]

/-- The in-neighbourhood of `v`. -/
def inN (v : V) : Finset V := univ.filter (fun u => T u v)

/-! ### The covering law -/

/-- **THE COVERING LAW.**  In a tournament with `S_(k+1)`, the in-neighbourhood of `v` dominates
every `k`-set avoiding `v` -- not merely the `k`-sets inside it.

The dominator of `A ∪ {v}` beats `v`, hence lies in `N⁻(v)`; that `A` was anywhere at all in the
tournament is never used. -/
theorem inNbhd_covers (k : ℕ) (h : HasSle T (k + 1)) (v : V) (A : Finset V) (hA : A.card ≤ k) :
    ∃ w ∈ inN T v, ∀ a ∈ A, T w a := by
  have hcard : (insert v A).card ≤ k + 1 := by
    calc (insert v A).card ≤ A.card + 1 := Finset.card_insert_le _ _
      _ ≤ k + 1 := by omega
  obtain ⟨w, -, hwbeat⟩ := h (insert v A) hcard
  refine ⟨w, ?_, fun a ha => hwbeat a (Finset.mem_insert_of_mem ha)⟩
  simp only [inN, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hwbeat v (Finset.mem_insert_self _ _)

/-! ### The count it forces -/

/-- **THE COVERING COUNT.**  `N⁻(v)` must cover all `C(N-1, k)` of the `k`-sets avoiding `v`,
using out-neighbourhoods as blocks. -/
theorem cover_count (k : ℕ) (h : HasSle T (k + 1)) (v : V) :
    (Fintype.card V - 1).choose k
      ≤ ∑ w ∈ inN T v, ((Erdos902Mass.outN T w).card).choose k := by
  have hsub : (((univ : Finset V).erase v).powersetCard k)
      ⊆ (inN T v).biUnion (fun w => (Erdos902Mass.outN T w).powersetCard k) := by
    intro A hA
    rw [Finset.mem_powersetCard] at hA
    obtain ⟨-, hcard⟩ := hA
    obtain ⟨w, hw, hbeat⟩ := inNbhd_covers T k h v A (le_of_eq hcard)
    refine Finset.mem_biUnion.mpr ⟨w, hw, ?_⟩
    rw [Finset.mem_powersetCard]
    refine ⟨fun a ha => ?_, hcard⟩
    simp only [Erdos902Mass.outN, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hbeat a ha
  calc (Fintype.card V - 1).choose k
      = ((((univ : Finset V).erase v).powersetCard k)).card := by
        rw [Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ v),
          Finset.card_univ]
    _ ≤ ∑ w ∈ inN T v, ((Erdos902Mass.outN T w).powersetCard k).card :=
        le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    _ = ∑ w ∈ inN T v, ((Erdos902Mass.outN T w).card).choose k :=
        Finset.sum_congr rfl (fun w _ => Finset.card_powersetCard _ _)

/-- **THE IN-DEGREE BOUND.**  If no vertex beats more than `d` others, every in-neighbourhood
has at least `C(N-1,k) / C(d,k)` vertices.  With `d ≈ (N-1)/2` this is `≈ 2^k`. -/
theorem indeg_lower (k : ℕ) (h : HasSle T (k + 1)) (v : V) (d : ℕ)
    (hd : ∀ w : V, (Erdos902Mass.outN T w).card ≤ d) :
    (Fintype.card V - 1).choose k ≤ (inN T v).card * (d.choose k) := by
  calc (Fintype.card V - 1).choose k
      ≤ ∑ w ∈ inN T v, ((Erdos902Mass.outN T w).card).choose k := cover_count T k h v
    _ ≤ ∑ _w ∈ inN T v, d.choose k :=
        Finset.sum_le_sum (fun w _ => Nat.choose_le_choose k (hd w))
    _ = (inN T v).card * (d.choose k) := by rw [Finset.sum_const, smul_eq_mul]

/-- The covering law is strictly more than "the in-neighbourhood carries `S_k`": specialised to
`A` inside `N⁻(v)` it gives exactly that, so the estate's `hasSle_induced` is the shadow of this
statement on the sets it happens to look at. -/
theorem covers_generalises_induced (k : ℕ) (h : HasSle T (k + 1)) (v : V) (A : Finset V)
    (hA : A.card ≤ k) (_hsub : A ⊆ inN T v) :
    ∃ w ∈ inN T v, ∀ a ∈ A, T w a :=
  inNbhd_covers T k h v A hA

#print axioms inNbhd_covers
#print axioms cover_count
#print axioms indeg_lower
#print axioms covers_generalises_induced

end Erdos902Cover
