/-
Erdos 902 -- THE ERDOS EXISTENCE BOUND [Er63c], formalized.

This is the half `Erdos902ClosedForm.f_ge` cited rather than proved: for every `n` there IS a
tournament with Schutte's property `S_n`.  Without it the lower bound is a statement about a
possibly-empty set.

METHOD: the probabilistic method, done as COUNTING (no measure theory).  A random tournament on
`Fin M` is encoded by `c : Fin M x Fin M -> Bool`, read at the coordinate `blockCoord a b`
(the pair sorted, so both directions of an arc read the SAME bit and the relation is a
tournament by construction).

The count is done with an INJECTION, never an equivalence.  For a fixed `S`, a `c` for which no
vertex dominates `S` is sent to
  (a) for each `v` outside `S`, the row of bits from `v` to `S` -- which is NOT the all-dominating
      pattern, so it lives in a set of size `2^n - 1`; and
  (b) every bit outside those rows, untouched.
The rows are disjoint because the pairs {v,s} are distinct, and the map is injective because
(a) and (b) together mention every coordinate.  That gives

    #{c : S undominated}  <=  (2^n - 1)^(M-n) * 2^(M*M - (M-n)*n)

with no complement bookkeeping and no ordering case-split beyond a single left inverse.
Union bound over the `C(M,n)` sets, `Erdos902Arith.exists_good_M` to pick `M`, done.
-/
import Mathlib
import Erdos902ClosedForm
import Erdos902Arith

open Finset

namespace Erdos902Existence

abbrev Coord (m : ℕ) := Fin m × Fin m
abbrev Space (m : ℕ) := Coord m → Bool

variable {m : ℕ}

/-- The single bit carrying the arc between `a` and `b`: the pair, sorted. -/
def blockCoord (a b : Fin m) : Coord m := if a < b then (a, b) else (b, a)

/-- The value of that bit which means "a beats b". -/
def pat (a b : Fin m) : Bool := decide (a < b)

/-- The tournament read off from `c`.  Total and asymmetric BY CONSTRUCTION: the two directions
of an arc consult the same bit and compare it against opposite values. -/
def beatsOf (c : Space m) (a b : Fin m) : Prop :=
  if a < b then c (a, b) = true else if b < a then c (b, a) = false else False

instance (c : Space m) : DecidableRel (beatsOf c) := fun a b => by
  unfold beatsOf; infer_instance

theorem beats_lt (c : Space m) {a b : Fin m} (h : a < b) :
    beatsOf c a b ↔ c (a, b) = true := by simp [beatsOf, h]

theorem beats_gt (c : Space m) {a b : Fin m} (h : a < b) :
    beatsOf c b a ↔ c (a, b) = false := by simp [beatsOf, lt_asymm h, h]

theorem beatsOf_isTournament (c : Space m) : IsTournament (beatsOf c) where
  irrefl a := by simp [beatsOf]
  total a b hab := by
    rcases lt_trichotomy a b with h | h | h
    · cases hc : c (a, b)
      · exact Or.inr ((beats_gt c h).mpr hc)
      · exact Or.inl ((beats_lt c h).mpr hc)
    · exact absurd h hab
    · cases hc : c (b, a)
      · exact Or.inl ((beats_gt c h).mpr hc)
      · exact Or.inr ((beats_lt c h).mpr hc)
  asymm a b hab hba := by
    rcases lt_trichotomy a b with h | h | h
    · rw [beats_lt c h] at hab; rw [beats_gt c h] at hba; simp [hab] at hba
    · subst h; simp [beatsOf] at hab
    · rw [beats_gt c h] at hab; rw [beats_lt c h] at hba; simp [hba] at hab

/-- Domination, in the coordinate form the counting uses. -/
theorem beats_iff_coord (c : Space m) {a b : Fin m} (hab : a ≠ b) :
    beatsOf c a b ↔ c (blockCoord a b) = pat a b := by
  rcases lt_trichotomy a b with h | h | h
  · simp [blockCoord, pat, h, beats_lt c h]
  · exact absurd h hab
  · simp [blockCoord, pat, lt_asymm h, beats_gt c h]

/-! ### The count for one set `S` -/

/-- `S` is undominated by `c`. -/
def Bad (S : Finset (Fin m)) (c : Space m) : Prop :=
  ∀ v ∈ Sᶜ, ∃ s ∈ S, c (blockCoord v s) ≠ pat v s

instance (S : Finset (Fin m)) (c : Space m) : Decidable (Bad S c) := by
  unfold Bad; infer_instance

/-- Left inverse of `blockCoord` given that exactly one endpoint lies in `S`.  This is what
makes injectivity a one-liner instead of a four-way case split. -/
def unblk (S : Finset (Fin m)) (x : Coord m) : Fin m × Fin m :=
  if x.1 ∈ S then (x.2, x.1) else (x.1, x.2)

theorem unblk_blockCoord {S : Finset (Fin m)} {v s : Fin m} (hv : v ∉ S) (hs : s ∈ S) :
    unblk S (blockCoord v s) = (v, s) := by
  by_cases h : v < s <;> simp [unblk, blockCoord, h, hv, hs]

/-- The coordinates read by the rows of `S`. -/
def Blk (S : Finset (Fin m)) : Finset (Coord m) :=
  (Sᶜ ×ˢ S).image (fun p => blockCoord p.1 p.2)

theorem blk_injOn (S : Finset (Fin m)) :
    Set.InjOn (fun p : Fin m × Fin m => blockCoord p.1 p.2) ↑(Sᶜ ×ˢ S) := by
  rintro ⟨v, s⟩ hp ⟨v', s'⟩ hq hEq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_compl] at hp hq
  have hcong := congrArg (unblk S) hEq
  rwa [unblk_blockCoord hp.1 hp.2, unblk_blockCoord hq.1 hq.2] at hcong

theorem blk_card (S : Finset (Fin m)) : (Blk S).card = (m - S.card) * S.card := by
  rw [Blk, Finset.card_image_of_injOn (blk_injOn S), Finset.card_product, Finset.card_compl,
    Fintype.card_fin]

/-- The pattern of bits that would make `v` dominate `S`. -/
def patRow (S : Finset (Fin m)) (v : Fin m) : {s // s ∈ S} → Bool := fun s => pat v s.1

/-- Target of the injection: one non-dominating row per outside vertex, plus every other bit. -/
abbrev Tgt (S : Finset (Fin m)) : Type :=
  ((v : {x // x ∈ Sᶜ}) → {g : {s // s ∈ S} → Bool // g ≠ patRow S v.1}) ×
    ({x : Coord m // x ∉ Blk S} → Bool)

def enc (S : Finset (Fin m)) (c : {c : Space m // Bad S c}) : Tgt S :=
  (fun v => ⟨fun s => c.1 (blockCoord v.1 s.1), by
      obtain ⟨s, hs, hne⟩ := c.2 v.1 v.2
      intro hEq
      exact hne (congrFun hEq ⟨s, hs⟩)⟩,
    fun x => c.1 x.1)

theorem enc_injective (S : Finset (Fin m)) : Function.Injective (enc S) := by
  intro c c' h
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ Blk S
  · obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_product] at hp
    have h1 := congrFun (congrArg Prod.fst h) ⟨p.1, hp.1⟩
    have h2 := congrFun (congrArg Subtype.val h1) ⟨p.2, hp.2⟩
    simpa [enc, hpx] using h2
  · exact congrFun (congrArg Prod.snd h) ⟨x, hx⟩

theorem card_row (S : Finset (Fin m)) (v : Fin m) :
    Fintype.card {g : {s // s ∈ S} → Bool // g ≠ patRow S v} = 2 ^ S.card - 1 := by
  have h1 : Fintype.card ({s // s ∈ S} → Bool) = 2 ^ S.card := by
    simp [Fintype.card_fun, Fintype.card_coe]
  have h2 := Fintype.card_subtype_compl (fun g : {s // s ∈ S} → Bool => g = patRow S v)
  simpa [h1, Fintype.card_subtype_eq, Ne] using h2

theorem card_tgt (S : Finset (Fin m)) :
    Fintype.card (Tgt S)
      = (2 ^ S.card - 1) ^ (m - S.card) * 2 ^ (m * m - (m - S.card) * S.card) := by
  have hcompl : Fintype.card {x : Coord m // x ∉ Blk S} = m * m - (m - S.card) * S.card := by
    rw [Fintype.card_subtype_compl]
    simp [Fintype.card_coe, blk_card]
  rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_fun, hcompl]
  simp [card_row, Finset.prod_const, Fintype.card_coe, Finset.card_compl]

/-- **THE COUNT.**  At most `(2^n - 1)^(M-n) * 2^(rest)` matrices leave `S` undominated. -/
theorem card_bad_le (S : Finset (Fin m)) :
    (univ.filter (Bad S)).card
      ≤ (2 ^ S.card - 1) ^ (m - S.card) * 2 ^ (m * m - (m - S.card) * S.card) := by
  have h := Fintype.card_le_of_injective (enc S) (enc_injective S)
  rw [Fintype.card_subtype, card_tgt] at h
  exact h

/-! ### Union bound -/

theorem exists_dominating (n : ℕ)
    (hlt : (Nat.choose m n) * ((2 ^ n - 1) ^ (m - n) * 2 ^ (m * m - (m - n) * n)) < 2 ^ (m * m)) :
    ∃ c : Space m, ∀ S : Finset (Fin m), S.card = n → ∃ v, v ∉ S ∧ ∀ s ∈ S, beatsOf c v s := by
  classical
  by_contra hcon
  push_neg at hcon
  have hcover : (univ : Finset (Space m)) ⊆
      ((univ : Finset (Fin m)).powersetCard n).biUnion (fun S => univ.filter (Bad S)) := by
    intro c _
    obtain ⟨S, hS, hbad⟩ := hcon c
    refine Finset.mem_biUnion.mpr ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro v hv
    have hvS : v ∉ S := Finset.mem_compl.mp hv
    obtain ⟨s, hs, hns⟩ := hbad v hvS
    refine ⟨s, hs, ?_⟩
    intro hEq
    have hne : v ≠ s := by rintro rfl; exact hvS hs
    exact hns ((beats_iff_coord c hne).mpr hEq)
  have h1 : (2 : ℕ) ^ (m * m) ≤
      ∑ S ∈ (univ : Finset (Fin m)).powersetCard n, (univ.filter (Bad S)).card := by
    have hcard : (univ : Finset (Space m)).card = 2 ^ (m * m) := by
      simp [Finset.card_univ, Fintype.card_fun, Fintype.card_prod]
    calc (2 : ℕ) ^ (m * m) = (univ : Finset (Space m)).card := hcard.symm
      _ ≤ _ := le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
  have h2 : ∑ S ∈ (univ : Finset (Fin m)).powersetCard n, (univ.filter (Bad S)).card
      ≤ (Nat.choose m n) * ((2 ^ n - 1) ^ (m - n) * 2 ^ (m * m - (m - n) * n)) := by
    calc ∑ S ∈ (univ : Finset (Fin m)).powersetCard n, (univ.filter (Bad S)).card
        ≤ ∑ _S ∈ (univ : Finset (Fin m)).powersetCard n,
            ((2 ^ n - 1) ^ (m - n) * 2 ^ (m * m - (m - n) * n)) := by
          refine Finset.sum_le_sum ?_
          intro S hSmem
          have hSc : S.card = n := (Finset.mem_powersetCard.mp hSmem).2
          simpa [hSc] using card_bad_le S
      _ = _ := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
  omega

/-! ### Assembly -/

/-- **THE ERDOS EXISTENCE BOUND at any `M` the arithmetic admits.**  Stated at an arbitrary `M`
so the witness stays visible: nothing here is hidden behind an `∃`. -/
theorem schutteAt_of_arith (M n : ℕ) (hnM : n ≤ M)
    (harith : (Nat.choose M n) * (2 ^ n - 1) ^ (M - n) < (2 ^ n) ^ (M - n)) :
    SchutteAt n M := by
  have hMM : (M - n) * n ≤ M * M := Nat.mul_le_mul (Nat.sub_le _ _) hnM
  have hsplit : (2 : ℕ) ^ (M * M) = 2 ^ ((M - n) * n) * 2 ^ (M * M - (M - n) * n) := by
    rw [← pow_add, Nat.add_sub_cancel' hMM]
  have hpos : 0 < (2 : ℕ) ^ (M * M - (M - n) * n) := pow_pos (by norm_num) _
  have hlt : (Nat.choose M n) * ((2 ^ n - 1) ^ (M - n) * 2 ^ (M * M - (M - n) * n))
      < 2 ^ (M * M) := by
    rw [hsplit, ← Nat.mul_assoc]
    refine mul_lt_mul_of_pos_right ?_ hpos
    calc (Nat.choose M n) * (2 ^ n - 1) ^ (M - n) < (2 ^ n) ^ (M - n) := harith
      _ = 2 ^ ((M - n) * n) := by rw [← pow_mul, Nat.mul_comm]
  obtain ⟨c, hc⟩ := exists_dominating (m := M) n hlt
  refine ⟨beatsOf c, inferInstance, beatsOf_isTournament c, ?_⟩
  refine hasSle_of_hasS (beatsOf c) n (by simpa using hnM) ?_
  intro L hlen hnd
  obtain ⟨v, hv, hbeats⟩ := hc L.toFinset (by rw [List.toFinset_card_of_nodup hnd, hlen])
  exact ⟨v, fun hmem => hv (List.mem_toFinset.mpr hmem),
    fun s hs => hbeats s (List.mem_toFinset.mpr hs)⟩

/-- **THE EXPLICIT WITNESS.**  A tournament with Schutte's property `S_n` exists on
`n + 3 n^2 2^n` vertices. -/
theorem schutteAt_M0 (n : ℕ) (hn : 1 ≤ n) : SchutteAt n (Erdos902Arith.M0 n) :=
  schutteAt_of_arith _ n (by simp [Erdos902Arith.M0]) (Erdos902Arith.good_M0 n hn)

/-- **THE ERDOS EXISTENCE BOUND.**  For every `n` there is a tournament with property `S_n`. -/
theorem erdos_existence (n : ℕ) (hn : 1 ≤ n) : ∃ M : ℕ, SchutteAt n M :=
  ⟨Erdos902Arith.M0 n, schutteAt_M0 n hn⟩

/-- **f(n) >= 2^(n+1) - 1, UNCONDITIONALLY.**  The nonemptiness hypothesis of
`Erdos902ClosedForm.f_ge` is now discharged rather than cited. -/
theorem f_ge_unconditional (n : ℕ) (hn : 1 ≤ n) : 2 ^ (n + 1) - 1 ≤ f n := by
  obtain ⟨M, hM⟩ := erdos_existence n hn
  exact f_ge n ⟨M, hM⟩

/-- **THE ERDOS UPPER BOUND [Er63c], EXPLICIT: `f n ≤ n + 3 n^2 2^n`.**

This is the `O(n^2 2^n)` half of Erdos's 1963 estimate, with an explicit constant and no
asymptotic notation.  It is NOT the conjectured `O(n 2^n)`: the factor of `n` between this and
the Szekeres-Szekeres lower bound is exactly the open part of the problem. -/
theorem f_le_explicit (n : ℕ) (hn : 1 ≤ n) : f n ≤ n + 3 * n ^ 2 * 2 ^ n := by
  have hmem : Erdos902Arith.M0 n ∈ {m | SchutteAt n m} := schutteAt_M0 n hn
  have h : f n ≤ Erdos902Arith.M0 n := Nat.sInf_le hmem
  simpa [Erdos902Arith.M0] using h

/-- **BOTH SIDES OF ERDOS [Er63c], IN ONE STATEMENT.**
`2^(n+1) - 1  ≤  f n  ≤  n + 3 n^2 2^n`. -/
theorem erdos902_sandwich (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (n + 1) - 1 ≤ f n ∧ f n ≤ n + 3 * n ^ 2 * 2 ^ n :=
  ⟨f_ge_unconditional n hn, f_le_explicit n hn⟩

#print axioms card_bad_le
#print axioms exists_dominating
#print axioms schutteAt_M0
#print axioms erdos_existence
#print axioms f_ge_unconditional
#print axioms f_le_explicit
#print axioms erdos902_sandwich

end Erdos902Existence
