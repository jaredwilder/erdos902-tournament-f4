/-
Erdos 902 -- THE SZEKERES-SZEKERES LOWER BOUND.  f(n) >= (n+2) * 2^(n-1) - 1.

The last classical piece.  The estate's formalized lower bound was the Erdos 1963 value
`2^(n+1) - 1`; the literature's stronger lower bound is Szekeres-Szekeres [SzSz65], of order
`n * 2^n`.  This file closes it, with a self-contained proof whose value matches the [SzSz65]
formula exactly -- including TIGHTNESS at both known exact points:

      n = 2 :  (2+2) * 2^1 - 1 =  7  =  f(2)
      n = 3 :  (3+2) * 2^2 - 1 = 19  =  f(3)

so in particular `f(3) >= 19` is now kernel-checked (the estate previously had only `>= 15`).

⭐ THE MECHANISM: MULTIPLICITY AMPLIFICATION (`amplification`).  Let `HasSleM k m` mean every
set of at most `k` vertices has at least `m` dominators.  Then

      HasSleM (k+1) m   ⟹   HasSleM k (k + 1 + m).

Proof.  Let `S` have at most `k` vertices, `D` its dominator set, `c = |D|`, and suppose
`c <= k + m`.  Drop `m - 1` elements of `D` to get `E ⊆ D` with `|E| = c - m + 1 <= k + 1`.
`E` has a dominator `w`.  The set `S ∪ {w}` has at most `k + 1` vertices, so it has at least
`m` dominators; every one of them beats all of `S` (hence lies in `D`) and beats `w` (hence
lies OUTSIDE `E`, since `w` beats all of `E`).  But `|D \ E| = m - 1 < m`.  Contradiction.

The domination property amplifies itself: asking for ONE dominator of every `(k+1)`-set forces
`k + 2` dominators of every `k`-set.  This is the factor the plain doubling recursion never
sees.

⭐ THE MULTIPLICITY-PRESERVING DESCENT (`hasSleM_induced`, `card_ge_of_hasSleM`).  All `m`
dominators of `S ∪ {v}` beat `v`, so the in-neighbourhood of every vertex inherits
`HasSleM k m` with the SAME `m`, and the estate's counting step (`card_ge_two_mul_succ`) turns
a minimum in-degree bound into a vertex bound.  By induction:

      HasSleM k m  (1 <= m)   ⟹   N >= (m+1) * 2^k - 1.

At `m = 1` this is the estate's classical `2^(k+1) - 1` again; the gain is that `m` rides along.

⭐ THE CHAIN (`card_ge_szekeres`).  Amplify ONCE at the top, then descend:

      S_n  =  HasSleM n 1  ⟹  HasSleM (n-1) (n+1)  ⟹  N >= (n+2) * 2^(n-1) - 1.

(Amplifying more than once trades a doubling for a linear gain and is strictly worse; once is
optimal in this family, which is why the formula is what it is.)

⛔ SCOPE.  The BOUND is Szekeres-Szekeres [SzSz65]; this proof is the estate's own and
self-contained -- no claim is made that it is the original argument.  The upper half of
`f(3) = 19` (existence of a 19-vertex S_3 tournament) is NOT formalized here; `f(3) >= 19` is.
With `Erdos902Existence.f_le_explicit` this file completes the classical sandwich, both sides
unconditional:

      (n+2) * 2^(n-1) - 1   <=   f(n)   <=   n + 3 n^2 2^n.
-/
import Mathlib
import Erdos902Existence
import Erdos902Mass

open Finset

namespace Erdos902Szekeres

universe u

variable {V : Type*} [Fintype V] [DecidableEq V] (T : V → V → Prop) [DecidableRel T]

/-- `m`-fold Schutte property: every set of at most `k` vertices has at least `m` dominators. -/
def HasSleM (k m : ℕ) : Prop :=
  ∀ S : Finset V, S.card ≤ k → m ≤ (Erdos902Mass.domSet T S).card

/-- The plain property is the `m = 1` case. -/
theorem hasSleM_one_of_hasSle {n : ℕ} (H : HasSle T n) : HasSleM T n 1 := by
  intro S hS
  obtain ⟨w, -, hbeats⟩ := H S hS
  have hw : w ∈ Erdos902Mass.domSet T S := by
    simp only [Erdos902Mass.domSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Erdos902Mass.DominatesAll]
    exact hbeats
  exact Finset.card_pos.mpr ⟨w, hw⟩

/-! ### The amplification -/

/-- **MULTIPLICITY AMPLIFICATION.**  One dominator for every `(k+1)`-set forces `k + 1 + m`
dominators for every `k`-set, given `m`-fold domination of `(k+1)`-sets.  The domination
property amplifies itself on the way down. -/
theorem amplification (hT : IsTournament T) (k m : ℕ) (hm : 1 ≤ m)
    (H : HasSleM T (k + 1) m) : HasSleM T k (k + 1 + m) := by
  intro S hS
  by_contra hlt
  push_neg at hlt
  set D := Erdos902Mass.domSet T S with hD
  have hcm : m ≤ D.card := H S (le_trans hS (Nat.le_succ k))
  -- drop `m - 1` elements of `D`
  have hchoose : D.card - m + 1 ≤ D.card := by omega
  obtain ⟨E, hED, hEcard⟩ := Finset.exists_subset_card_eq hchoose
  have hEle : E.card ≤ k + 1 := by omega
  have hEpos : 0 < E.card := by omega
  -- a dominator of `E`
  have hEdom : m ≤ (Erdos902Mass.domSet T E).card := H E hEle
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (lt_of_lt_of_le hm hEdom)
  have hwbeats : ∀ e ∈ E, T w e := by
    simpa [Erdos902Mass.domSet, Erdos902Mass.DominatesAll] using hw
  -- `w` is not in `S`: an element of `E ⊆ D` would beat it and be beaten by it
  obtain ⟨e0, he0⟩ := Finset.card_pos.mp hEpos
  have he0D : e0 ∈ D := hED he0
  have he0beats : ∀ s ∈ S, T e0 s := by
    simpa [hD, Erdos902Mass.domSet, Erdos902Mass.DominatesAll] using he0D
  have hwS : w ∉ S := by
    intro hwS
    exact hT.asymm e0 w (he0beats w hwS) (hwbeats e0 he0)
  -- `S ∪ {w}` has at most `k + 1` vertices, so at least `m` dominators
  have hins : (insert w S).card ≤ k + 1 := by
    calc (insert w S).card ≤ S.card + 1 := Finset.card_insert_le _ _
      _ ≤ k + 1 := by omega
  have hm2 : m ≤ (Erdos902Mass.domSet T (insert w S)).card := H _ hins
  -- but its dominators all lie in `D \ E`, which has only `m - 1` elements
  have hsub : Erdos902Mass.domSet T (insert w S) ⊆ D \ E := by
    intro d hd
    have hdall : ∀ b ∈ insert w S, T d b := by
      simpa [Erdos902Mass.domSet, Erdos902Mass.DominatesAll] using hd
    have hdD : d ∈ D := by
      simp only [hD, Erdos902Mass.domSet, Finset.mem_filter, Finset.mem_univ, true_and,
        Erdos902Mass.DominatesAll]
      exact fun s hs => hdall s (Finset.mem_insert_of_mem hs)
    have hdw : T d w := hdall w (Finset.mem_insert_self _ _)
    have hdE : d ∉ E := fun hdE => hT.asymm d w hdw (hwbeats d hdE)
    exact Finset.mem_sdiff.mpr ⟨hdD, hdE⟩
  have hcardDE : (D \ E).card = m - 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hED]
    omega
  have := le_trans hm2 (Finset.card_le_card hsub)
  omega

/-! ### The multiplicity-preserving descent -/

/-- All `m` dominators of `S ∪ {v}` beat `v`, so every in-neighbourhood inherits the property
with the SAME multiplicity. -/
theorem hasSleM_induced (hT : IsTournament T) (k m : ℕ)
    (H : HasSleM T (k + 1) m) (v : V) : HasSleM (induced T v) k m := by
  intro S hS
  have hcard : (insert v (S.image Subtype.val)).card ≤ k + 1 := by
    calc (insert v (S.image Subtype.val)).card
        ≤ (S.image Subtype.val).card + 1 := Finset.card_insert_le _ _
      _ ≤ S.card + 1 := Nat.add_le_add_right Finset.card_image_le 1
      _ ≤ k + 1 := by omega
  have hm' := H _ hcard
  have hsub : Erdos902Mass.domSet T (insert v (S.image Subtype.val))
      ⊆ (Erdos902Mass.domSet (induced T v) S).image Subtype.val := by
    intro d hd
    have hdall : ∀ b ∈ insert v (S.image Subtype.val), T d b := by
      simpa [Erdos902Mass.domSet, Erdos902Mass.DominatesAll] using hd
    have hdv : T d v := hdall v (Finset.mem_insert_self _ _)
    refine Finset.mem_image.mpr ⟨⟨d, hdv⟩, ?_, rfl⟩
    simp only [Erdos902Mass.domSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Erdos902Mass.DominatesAll]
    intro a ha
    exact hdall a.val (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ha))
  calc m ≤ (Erdos902Mass.domSet T (insert v (S.image Subtype.val))).card := hm'
    _ ≤ ((Erdos902Mass.domSet (induced T v) S).image Subtype.val).card :=
        Finset.card_le_card hsub
    _ = (Erdos902Mass.domSet (induced T v) S).card :=
        Finset.card_image_of_injective _ Subtype.val_injective

/-- **THE COUNT WITH MULTIPLICITY.**  `HasSleM k m` forces `(m+1) * 2^k - 1` vertices: the
estate's doubling recursion, with the multiplicity riding along. -/
theorem card_ge_of_hasSleM :
    ∀ (k m : ℕ), 1 ≤ m → ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (T : V → V → Prop) [DecidableRel T],
      IsTournament T → HasSleM T k m → (m + 1) * 2 ^ k - 1 ≤ Fintype.card V := by
  intro k
  induction k with
  | zero =>
      intro m hm V _ _ T _ hT H
      have h0 : m ≤ (Erdos902Mass.domSet T (∅ : Finset V)).card := H ∅ (by simp)
      have h1 : (Erdos902Mass.domSet T (∅ : Finset V)).card ≤ Fintype.card V := by
        rw [← Finset.card_univ]
        exact Finset.card_le_card (Finset.subset_univ _)
      simp only [pow_zero, Nat.mul_one]
      omega
  | succ k ih =>
      intro m hm V _ _ T _ hT H
      have hne : Nonempty V := by
        have h0 : m ≤ (Erdos902Mass.domSet T (∅ : Finset V)).card := H ∅ (by simp)
        obtain ⟨x, -⟩ := Finset.card_pos.mp (lt_of_lt_of_le hm h0)
        exact ⟨x⟩
      have hk : ∀ v : V, (m + 1) * 2 ^ k - 1 ≤ indeg T v := by
        intro v
        have := ih m hm (induced T v) (induced_isTournament T hT v)
          (hasSleM_induced T hT k m H v)
        rwa [card_inNbhd] at this
      have hmain := card_ge_two_mul_succ T hT ((m + 1) * 2 ^ k - 1) hk hne
      have hpos : 1 ≤ (m + 1) * 2 ^ k :=
        Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hexp : (m + 1) * 2 ^ (k + 1) = 2 * ((m + 1) * 2 ^ k) := by ring
      omega

/-! ### The Szekeres-Szekeres bound -/

/-- **THE SZEKERES-SZEKERES LOWER BOUND.**  Any tournament with Schutte's property `S_n` has at
least `(n+2) * 2^(n-1) - 1` vertices.  Amplify once, then descend. -/
theorem card_ge_szekeres (hT : IsTournament T) (n : ℕ) (hn : 1 ≤ n)
    (H : HasSle T n) : (n + 2) * 2 ^ (n - 1) - 1 ≤ Fintype.card V := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have h1 : HasSleM T (j + 1) 1 := hasSleM_one_of_hasSle T H
  have h2 : HasSleM T j (j + 1 + 1) := amplification T hT j 1 (le_refl 1) h1
  have h3 := card_ge_of_hasSleM j (j + 2) (by omega) T hT (by
    have : j + 1 + 1 = j + 2 := by omega
    rwa [this] at h2)
  have hidx : j + 1 - 1 = j := by omega
  rw [hidx]
  have harith : (j + 1 + 2) = (j + 2 + 1) := by omega
  rw [harith]
  exact h3

/-- The bound at the level of admissible vertex counts. -/
theorem szekeres_card_bound (n m : ℕ) (hn : 1 ≤ n) (h : SchutteAt n m) :
    (n + 2) * 2 ^ (n - 1) - 1 ≤ m := by
  obtain ⟨T, inst, hT, hS⟩ := h
  letI := inst
  have := card_ge_szekeres T hT n hn hS
  simpa using this

/-- **f(3) >= 19.**  The Szekeres value, kernel-checked; the estate previously had only 15. -/
theorem f_three_ge_19 (m : ℕ) (h : SchutteAt 3 m) : 19 ≤ m := by
  have := szekeres_card_bound 3 m (by norm_num) h
  norm_num at this
  exact this

/-- **THE SZEKERES-SZEKERES BOUND FOR f, UNCONDITIONAL.** -/
theorem szekeres_f_ge (n : ℕ) (hn : 1 ≤ n) : (n + 2) * 2 ^ (n - 1) - 1 ≤ f n := by
  obtain ⟨M, hM⟩ := Erdos902Existence.erdos_existence n hn
  have hmem : f n ∈ {m | SchutteAt n m} := Nat.sInf_mem ⟨M, hM⟩
  exact szekeres_card_bound n (f n) hn hmem

/-- **THE COMPLETE CLASSICAL SANDWICH**, both sides unconditional:
`(n+2) * 2^(n-1) - 1  <=  f(n)  <=  n + 3 n^2 2^n`. -/
theorem classical_sandwich (n : ℕ) (hn : 1 ≤ n) :
    (n + 2) * 2 ^ (n - 1) - 1 ≤ f n ∧ f n ≤ n + 3 * n ^ 2 * 2 ^ n :=
  ⟨szekeres_f_ge n hn, Erdos902Existence.f_le_explicit n hn⟩

#print axioms amplification
#print axioms card_ge_of_hasSleM
#print axioms card_ge_szekeres
#print axioms szekeres_card_bound
#print axioms f_three_ge_19
#print axioms szekeres_f_ge
#print axioms classical_sandwich

end Erdos902Szekeres
