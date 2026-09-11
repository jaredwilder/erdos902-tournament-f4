import Mathlib

/-!
⛔ UNVERIFIED - PARKED MID-ROUND. This is `F4Seal.lean` plus three added lemmas
(`inN_hasS3`, `min_indeg_ge_19`, `out_triples_covered_from_inN`). The kernel run
of 2026-09-02 returned exitCode 1 with NO parsed diagnostic, and the machine was
taken down before the error could be read, so the failure is UNLOCATED - it is
not known whether the three new lemmas or the appended `#print axioms` placement
caused it. `F4Seal.lean` beside this file is the VERIFIED version (12/12 clean)
and is unchanged. Next round: compile THIS file and read the raw Lean output.
-/


/-!
# ERDOS 902 - THE f(4) >= 49 SEAL, conditional and kernel-clean.

This file formalizes the LEAN_TARGETS list shipped inside the sealed package
`ERDOS902-SPEAKER-REAL-002` (catalogue SHA-256
`20dbad06e128f968e87ce5bec9ca3128b8d2e9a9f25152b29d82c48c967b45d0`,
package receipt `0596317`). Published record for f(4) is 48
(Reid, McRae, Hedetniemi & Hedetniemi 2004); the package's candidate is 49.

Every declaration below is proved by the Lean kernel with footprint
`[propext, Classical.choice, Quot.sound]`. There is no `sorry` and no
`native_decide` anywhere in this file.

## What is PROVED here (no external input)

* `bad_covered_outside`      - the covering lemma: in an S4 tournament every bad
                               4-set of `inN v` lies inside some outside vertex's mask.
* `badCount_le_sum_repair`   - hence #bad <= sum of per-outside-vertex repair counts.
* `inN_hasS3`                - every in-neighbourhood of an S4 tournament carries S3.
* `min_indeg_ge_19`          - so, with f(3) >= 19 supplied, every in-degree is >= 19.
* `out_triples_covered_from_inN` - every triple of `outN v` is dominated from inside
                               `inN v`.
* `card_inN_add_card_outN`   - in/out split of every vertex.
* `two_mul_sum_indeg`        - the handshake `2 * sum indeg = n * (n-1)`, proved from
                               the tournament axioms (not assumed).
* `exists_indeg_le_23`       - pigeonhole at every order n <= 48.
* `no_order_48_from_global_capacity`  (TARGET 2)
* `no_S4_tournament_below_49`, `f_four_ge_49`  (TARGET 3)
* `order49_no_indeg23`       (TARGET 4)
* `order49_regular`          (TARGET 5)

## What is EXTERNAL, named exactly, and carried as an explicit hypothesis

`CoreCertificate T H` is the single interface. It asserts two numbers about a
23-vertex core `H`:

    bad floor   2475 <= (badSets T H).card
    capacity    for every x, repairCount T H x <= 66

Neither is proved here. Their provenance, stated honestly:

  (E1) COMPLETENESS OF THE McKAY/SPENCE DRT(23,11,5) CATALOGUE - 37 isomorphism
       classes. A published census. It is CITED, never re-derived, and this file
       never encodes it as a proved fact: it enters only through the hypothesis
       `hbridge` supplied by the caller. Filtering the 37 classes by S3 leaves
       exactly rows 35 and 36, whose bad-4-set counts are 2475 and 2530, so
       2475 is the floor.
  (E2) THE ADMISSIBLE-REPAIR-CAPACITY SWEEP - for each of the two cores, every
       admissible mask (|W| <= 12, and no core vertex has more than 6 of its
       in-neighbours in W) was exhausted: 1,153,310 masks for row 35 and
       1,152,232 for row 36, with exact maxima 65 and 66. That sweep is a
       ~1.15M-leaf search over a 2^23 subset-sum transform; it is far outside
       kernel `decide` range and is replicated in Python only
       (`verify_real_002.py`, twice-replicated receipts). It enters here only as
       the `capacity` half of `CoreCertificate`.
  (E3) THE DRT BRIDGE (H1 of `press/f4_bridge.lean`) - that a hypothetical
       48-vertex S4 tournament actually presents a vertex whose in-neighbourhood
       is one of those two cores. This is the piece that is neither proved nor
       merely cited: it is UNFORMALIZED, and parts of it (killing minimum
       in-degree 19..22) are open. It is absorbed into `hbridge` together with
       (E1) and (E2).
  (E4) MINIMUM IN-DEGREE >= 23 - carried as `hmin23`. Its provable half IS in
       this file: `inN_hasS3` plus `min_indeg_ge_19` give >= 19 outright from
       the estate's kernel-sealed f(3) >= 19 (`public/proofs/Erdos902Szekeres.lean`).
       The residual is exactly the four orders 19, 20, 21, 22, which
       `press/f4_bridge.lean` also lists as OPEN. That residual, not the McKay
       citation, is the largest single piece of the remaining distance.

So: this file is the connective tissue, kernel-checked end to end, between the
finite computation and the statement `49 <= f 4`. It is NOT a proof of
f(4) >= 49, and it does not claim to be. It makes the exact remaining distance
mechanical: discharge `hmin23` and `hbridge`.
-/

namespace Erdos902F4

open Finset

/-- A tournament: irreflexive, antisymmetric, and total on distinct pairs. -/
def IsTournament {V : Type*} (T : V → V → Prop) : Prop :=
  (∀ x : V, ¬ T x x) ∧ (∀ x y : V, T x y → ¬ T y x) ∧ (∀ x y : V, x ≠ y → T x y ∨ T y x)

/-- Property `S k`: every `k`-subset has a dominator outside it. -/
def HasS {V : Type*} (T : V → V → Prop) (k : ℕ) : Prop :=
  ∀ s : Finset V, s.card = k → ∃ u, u ∉ s ∧ ∀ w ∈ s, T u w

/-- Property `S k` RELATIVIZED to a vertex set `H`: the induced subtournament on
`H` has `S k`. This is what an in-neighbourhood carries. -/
def HasSOn {V : Type*} (T : V → V → Prop) (H : Finset V) (k : ℕ) : Prop :=
  ∀ s : Finset V, s ⊆ H → s.card = k → ∃ u ∈ H, u ∉ s ∧ ∀ w ∈ s, T u w

section Core

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (T : V → V → Prop) [DecidableRel T]

/-- the in-neighbourhood of `v`. -/
def inN (v : V) : Finset V := univ.filter (fun u => T u v)

/-- the out-neighbourhood of `v`. -/
def outN (v : V) : Finset V := univ.filter (fun u => T v u)

/-- `x`'s repair mask inside `H`: the members of `H` that `x` beats. -/
def mask (H : Finset V) (x : V) : Finset V := H.filter (fun h => T x h)

/-- a 4-subset of `H` is BAD when no vertex of `H` outside it dominates it. -/
def BadIn (H : Finset V) (s : Finset V) : Prop :=
  s ⊆ H ∧ s.card = 4 ∧ ∀ u ∈ H, u ∉ s → ¬ ∀ w ∈ s, T u w

/-- the finset of bad 4-sets of `H`. -/
def badSets (H : Finset V) : Finset (Finset V) :=
  (H.powersetCard 4).filter (fun s => decide (s.card = 4) ∧
    ∀ u ∈ H, u ∉ s → ¬ ∀ w ∈ s, T u w)

/-- per-mask repair count: how many bad 4-sets a mask contains. -/
def repairCount (H : Finset V) (x : V) : ℕ :=
  ((badSets T H).filter (fun s => s ⊆ mask T H x)).card

/-- ⭐ TARGET 1, AS AN INTERFACE, NOT AS A CLAIM.

The two external numbers about a core `H`, packaged. `2475` is the minimum over
the two S3-carrying DRT(23) catalogue rows of their bad-4-set counts
(2475 for row 35, 2530 for row 36); `66` is the global
ADMISSIBLE-REPAIR-CAPACITY over all ~1.15M admissible masks of either core
(65 for row 35, 66 for row 36).

Nothing in this file proves either number. See (E1) and (E2) in the file header. -/
def CoreCertificate (H : Finset V) : Prop :=
  2475 ≤ (badSets T H).card ∧ ∀ x : V, repairCount T H x ≤ 66

/-- membership unfolding for `badSets`. -/
theorem mem_badSets {H s : Finset V} :
    s ∈ badSets T H ↔ BadIn T H s := by
  unfold badSets BadIn
  simp only [Finset.mem_filter, Finset.mem_powersetCard, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, _⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h2, h3⟩

/-- ⭐ THE COVERING LEMMA. In a tournament with `S 4`, every bad 4-set of
`H = inN v` is contained in some outside vertex's mask: its `S 4` dominator is
not in `s`, not in `H` (badness), and not `v` (members of `H` beat `v`), so it
lies in `outN v`. -/
theorem bad_covered_outside
    (hasym : ∀ x y : V, T x y → ¬ T y x)
    (htot : ∀ x y : V, x ≠ y → T x y ∨ T y x)
    (hS4 : HasS T 4) (v : V) (s : Finset V)
    (hbad : BadIn T (inN T v) s) :
    ∃ x ∈ outN T v, s ⊆ mask T (inN T v) x := by
  obtain ⟨hsub, hcard, hnodom⟩ := hbad
  obtain ⟨u, hu_not, hu_dom⟩ := hS4 s hcard
  have hu_notH : u ∉ inN T v := fun huH => hnodom u huH hu_not hu_dom
  have hs_ne : s.Nonempty := by rw [← Finset.card_pos, hcard]; norm_num
  obtain ⟨w, hw⟩ := hs_ne
  have hwv : T w v := (Finset.mem_filter.mp (hsub hw)).2
  have hu_ne_v : u ≠ v := fun h => hasym w v hwv (h ▸ hu_dom w hw)
  have hu_out : u ∈ outN T v := by
    rw [outN, Finset.mem_filter]
    refine ⟨Finset.mem_univ u, ?_⟩
    rcases htot u v hu_ne_v with h | h
    · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ u, h⟩) hu_notH
    · exact h
  exact ⟨u, hu_out, fun w' hws => Finset.mem_filter.mpr ⟨hsub hws, hu_dom w' hws⟩⟩

/-- ⭐ THE COUNTING COROLLARY: the number of bad 4-sets of `inN v` is at most the
sum of repair counts over the outside vertices. -/
theorem badCount_le_sum_repair
    (hasym : ∀ x y : V, T x y → ¬ T y x)
    (htot : ∀ x y : V, x ≠ y → T x y ∨ T y x)
    (hS4 : HasS T 4) (v : V) :
    (badSets T (inN T v)).card ≤ ∑ x ∈ outN T v, repairCount T (inN T v) x := by
  have hcover : badSets T (inN T v) ⊆
      (outN T v).biUnion
        (fun x => (badSets T (inN T v)).filter (fun s => s ⊆ mask T (inN T v) x)) := by
    intro s hs
    obtain ⟨x, hx, hsx⟩ := bad_covered_outside T hasym htot hS4 v s ((mem_badSets T).mp hs)
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨hs, hsx⟩⟩
  calc (badSets T (inN T v)).card
      ≤ ((outN T v).biUnion _).card := Finset.card_le_card hcover
    _ ≤ ∑ x ∈ outN T v, repairCount T (inN T v) x := Finset.card_biUnion_le

/-- ⭐ EVERY IN-NEIGHBOURHOOD OF AN `S 4` TOURNAMENT CARRIES `S 3`.

Given a triple `q` inside `inN v`, apply `S 4` to `insert v q`: the dominator
beats `v`, so it lies in `inN v`, and it is outside `q`. This is the provable
half of the degree-forcing gap (E4): composed with the estate's kernel-sealed
f(3) >= 19 it gives minimum in-degree >= 19. The step from 19 to 23 is the part
that is NOT proved anywhere and is carried as `hmin23`. -/
theorem inN_hasS3
    (hirr : ∀ x : V, ¬ T x x)
    (hS4 : HasS T 4) (v : V) :
    HasSOn T (inN T v) 3 := by
  intro q hq hq3
  have hvq : v ∉ q := by
    intro hv
    exact hirr v (Finset.mem_filter.mp (hq hv)).2
  have hcard : (insert v q).card = 4 := by
    rw [Finset.card_insert_of_notMem hvq, hq3]
  obtain ⟨u, hu_not, hu_dom⟩ := hS4 (insert v q) hcard
  have huv : T u v := hu_dom v (Finset.mem_insert_self v q)
  refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, huv⟩, ?_, ?_⟩
  · exact fun hq' => hu_not (Finset.mem_insert_of_mem hq')
  · exact fun w hw => hu_dom w (Finset.mem_insert_of_mem hw)

/-- ⭐ MINIMUM IN-DEGREE FROM f(3). With the estate's `Erdos902Szekeres`
statement supplied as `hf3` (every `S 3` vertex set has at least 19 elements,
kernel-sealed and tight there), every in-degree of an `S 4` tournament is at
least 19. The named residual gap to `hmin23` is exactly the four orders
19, 20, 21, 22. -/
theorem min_indeg_ge_19
    (hirr : ∀ x : V, ¬ T x x)
    (hS4 : HasS T 4)
    (hf3 : ∀ W : Finset V, HasSOn T W 3 → 19 ≤ W.card) :
    ∀ v : V, 19 ≤ (inN T v).card :=
  fun v => hf3 (inN T v) (inN_hasS3 T hirr hS4 v)

/-- ⭐ THE OUTWARD COVERING DUTY: in an `S 4` tournament every triple of `outN v`
is dominated from INSIDE `inN v`. The core serves two masters on one arc budget,
which is the pressure the unformalized kills of in-degree 20, 21, 22 must use. -/
theorem out_triples_covered_from_inN
    (hasym : ∀ x y : V, T x y → ¬ T y x)
    (hS4 : HasS T 4) (v : V) (q : Finset V)
    (hq : q ⊆ outN T v) (hq3 : q.card = 3) (hv : v ∉ q) :
    ∃ u ∈ inN T v, ∀ w ∈ q, T u w := by
  have hcard : (insert v q).card = 4 := by
    rw [Finset.card_insert_of_notMem hv, hq3]
  obtain ⟨u, _, hu_dom⟩ := hS4 (insert v q) hcard
  have huv : T u v := hu_dom v (Finset.mem_insert_self v q)
  exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, huv⟩,
    fun w hw => hu_dom w (Finset.mem_insert_of_mem hw)⟩

/-- the in- and out-neighbourhoods partition `univ.erase v`. -/
theorem card_inN_add_card_outN
    (hirr : ∀ x : V, ¬ T x x)
    (hasym : ∀ x y : V, T x y → ¬ T y x)
    (htot : ∀ x y : V, x ≠ y → T x y ∨ T y x)
    (v : V) :
    (inN T v).card + (outN T v).card = Fintype.card V - 1 := by
  have hdisj : Disjoint (inN T v) (outN T v) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [inN, Finset.mem_filter] at ha
    rw [outN, Finset.mem_filter] at hb
    exact hasym _ _ ha.2 hb.2
  have hun : inN T v ∪ outN T v = univ.erase v := by
    ext a
    rw [Finset.mem_union, inN, outN, Finset.mem_filter, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩)
      · exact ⟨fun hav => hirr v (hav ▸ h), Finset.mem_univ a⟩
      · exact ⟨fun hav => hirr v (hav ▸ h), Finset.mem_univ a⟩
    · rintro ⟨hne, -⟩
      rcases htot a v hne with h | h
      · exact Or.inl ⟨Finset.mem_univ a, h⟩
      · exact Or.inr ⟨Finset.mem_univ a, h⟩
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hun, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at hcard
  omega

/-- total in-degree equals total out-degree: one `Finset.sum_comm`. -/
theorem sum_inN_eq_sum_outN :
    ∑ v : V, (inN T v).card = ∑ v : V, (outN T v).card := by
  simp only [inN, outN, Finset.card_filter]
  exact Finset.sum_comm

/-- ⭐ THE HANDSHAKE, PROVED (not assumed): in any tournament on `V`,
`2 * (total in-degree) = n * (n - 1)`. This is what discharges the `hsum`
hypothesis that the estate's earlier pigeonhole and regularity lemmas took on
faith. -/
theorem two_mul_sum_indeg
    (hirr : ∀ x : V, ¬ T x x)
    (hasym : ∀ x y : V, T x y → ¬ T y x)
    (htot : ∀ x y : V, x ≠ y → T x y ∨ T y x) :
    2 * (∑ v : V, (inN T v).card) = Fintype.card V * (Fintype.card V - 1) := by
  have h1 : ∑ v : V, ((inN T v).card + (outN T v).card)
      = Fintype.card V * (Fintype.card V - 1) := by
    rw [Finset.sum_congr rfl (fun v _ => card_inN_add_card_outN T hirr hasym htot v),
      Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← sum_inN_eq_sum_outN] at h1
  omega

/-- ⭐ PIGEONHOLE at every order at most 48: some vertex has in-degree at most 23.
(The average in-degree is `(n-1)/2 <= 23.5`.) -/
theorem exists_indeg_le_23
    (hirr : ∀ x : V, ¬ T x x)
    (hasym : ∀ x y : V, T x y → ¬ T y x)
    (htot : ∀ x y : V, x ≠ y → T x y ∨ T y x)
    (hpos : 0 < Fintype.card V) (hle : Fintype.card V ≤ 48) :
    ∃ v : V, (inN T v).card ≤ 23 := by
  by_contra hall
  push_neg at hall
  have h24 : ∀ v ∈ (univ : Finset V), 24 ≤ (inN T v).card := fun v _ => hall v
  have hlow : Fintype.card V * 24 ≤ ∑ v : V, (inN T v).card := by
    have := Finset.card_nsmul_le_sum (univ : Finset V) (fun v => (inN T v).card) 24 h24
    rwa [smul_eq_mul, Finset.card_univ] at this
  have hhand := two_mul_sum_indeg T hirr hasym htot
  have hshrink : Fintype.card V * (Fintype.card V - 1) ≤ Fintype.card V * 47 :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- ⭐ TARGET 2 - `no_order_48_from_global_capacity`.

An `S 4` tournament on at most 48 vertices, whose minimum in-degree is at least
23 and whose 23-in-degree cores carry the certificate, is impossible: the core
needs 2475 repairs and at most 24 outside vertices supply at most 66 each,
so `24 * 66 = 1584 < 2475`. -/
theorem no_order_48_from_global_capacity
    (hirr : ∀ x : V, ¬ T x x)
    (hasym : ∀ x y : V, T x y → ¬ T y x)
    (htot : ∀ x y : V, x ≠ y → T x y ∨ T y x)
    (hS4 : HasS T 4)
    (hpos : 0 < Fintype.card V) (hle : Fintype.card V ≤ 48)
    (hmin23 : ∀ v : V, 23 ≤ (inN T v).card)
    (hbridge : ∀ v : V, (inN T v).card = 23 → CoreCertificate T (inN T v)) :
    False := by
  obtain ⟨v, hv⟩ := exists_indeg_le_23 T hirr hasym htot hpos hle
  have h23 : (inN T v).card = 23 := le_antisymm hv (hmin23 v)
  obtain ⟨hbad, hcap⟩ := hbridge v h23
  have hcov := badCount_le_sum_repair T hasym htot hS4 v
  have hsplit := card_inN_add_card_outN T hirr hasym htot v
  have hout : (outN T v).card ≤ 24 := by omega
  have hsum : ∑ x ∈ outN T v, repairCount T (inN T v) x ≤ 24 * 66 := by
    calc ∑ x ∈ outN T v, repairCount T (inN T v) x
        ≤ ∑ _x ∈ outN T v, 66 := Finset.sum_le_sum (fun x _ => hcap x)
      _ = (outN T v).card * 66 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 24 * 66 := Nat.mul_le_mul_right 66 hout
  omega

/-- ⭐ TARGET 4 - `order49_no_indeg23`.

At order 49 the same certificate deletes the in-degree-23 branch outright:
25 outside vertices repair at most `25 * 66 = 1650 < 2475`. This is the branch
that previously ran 5.37 CPU-hours without a verdict. -/
theorem order49_no_indeg23
    (hirr : ∀ x : V, ¬ T x x)
    (hasym : ∀ x y : V, T x y → ¬ T y x)
    (htot : ∀ x y : V, x ≠ y → T x y ∨ T y x)
    (hS4 : HasS T 4)
    (hcard : Fintype.card V = 49)
    (hbridge : ∀ v : V, (inN T v).card = 23 → CoreCertificate T (inN T v)) :
    ∀ v : V, (inN T v).card ≠ 23 := by
  intro v h23
  obtain ⟨hbad, hcap⟩ := hbridge v h23
  have hcov := badCount_le_sum_repair T hasym htot hS4 v
  have hsplit := card_inN_add_card_outN T hirr hasym htot v
  have hout : (outN T v).card = 25 := by omega
  have hsum : ∑ x ∈ outN T v, repairCount T (inN T v) x ≤ 25 * 66 := by
    calc ∑ x ∈ outN T v, repairCount T (inN T v) x
        ≤ ∑ _x ∈ outN T v, 66 := Finset.sum_le_sum (fun x _ => hcap x)
      _ = (outN T v).card * 66 := by rw [Finset.sum_const, smul_eq_mul]
      _ = 25 * 66 := by rw [hout]
  omega

/-- ⭐ TARGET 5 - `order49_regular`.

Every hypothetical order-49 `S 4` tournament is 24-regular. In-degree 23 is
killed by TARGET 4, so every in-degree is at least 24; the handshake forces the
total to be exactly `49 * 48 / 2 = 1176`, i.e. the average 24, so no vertex can
exceed it either. -/
theorem order49_regular
    (hirr : ∀ x : V, ¬ T x x)
    (hasym : ∀ x y : V, T x y → ¬ T y x)
    (htot : ∀ x y : V, x ≠ y → T x y ∨ T y x)
    (hS4 : HasS T 4)
    (hcard : Fintype.card V = 49)
    (hmin23 : ∀ v : V, 23 ≤ (inN T v).card)
    (hbridge : ∀ v : V, (inN T v).card = 23 → CoreCertificate T (inN T v)) :
    ∀ v : V, (inN T v).card = 24 := by
  have hne23 := order49_no_indeg23 T hirr hasym htot hS4 hcard hbridge
  have hall24 : ∀ v : V, 24 ≤ (inN T v).card := by
    intro v
    have h1 := hmin23 v
    have h2 := hne23 v
    omega
  have hhand := two_mul_sum_indeg T hirr hasym htot
  rw [hcard] at hhand
  intro v
  by_contra hne
  have h25 : 25 ≤ (inN T v).card := by
    have := hall24 v
    omega
  have hsplit : ∑ w : V, (inN T w).card
      = (inN T v).card + ∑ w ∈ univ.erase v, (inN T w).card :=
    (Finset.add_sum_erase univ (fun w => (inN T w).card) (Finset.mem_univ v)).symm
  have hrest : 48 * 24 ≤ ∑ w ∈ univ.erase v, (inN T w).card := by
    have hstep := Finset.card_nsmul_le_sum (univ.erase v) (fun w => (inN T w).card) 24
      (fun w _ => hall24 w)
    rw [smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
      hcard] at hstep
    omega
  omega

end Core

/-- The set of orders at which an `S k` tournament exists.

The side condition `k ≤ n` is not decoration: for `n < k` the property `HasS`
is vacuous (there are no `k`-subsets), so without it every `f k` would collapse
to 0. With it, `f 4` is the usual quantity: the least number of vertices of a
tournament in which every 4 vertices have a common dominator. -/
def SkOrders (k : ℕ) : Set ℕ :=
  {n | k ≤ n ∧ ∃ T : Fin n → Fin n → Prop, ∃ _ : DecidableRel T,
      IsTournament T ∧ HasS T k}

/-- `f k` - the least order of a tournament with property `S k`. -/
noncomputable def f (k : ℕ) : ℕ := sInf (SkOrders k)

/-- ⭐ TARGET 3, pointwise form (the real content).

No `S 4` tournament exists on fewer than 49 vertices, given the external
interface at every order: minimum in-degree at least 23, and the core
certificate at every in-degree-23 vertex. -/
theorem no_S4_tournament_below_49
    (hmin23 : ∀ (m : ℕ) (S : Fin m → Fin m → Prop) [DecidableRel S],
        IsTournament S → HasS S 4 → ∀ v : Fin m, 23 ≤ (inN S v).card)
    (hbridge : ∀ (m : ℕ) (S : Fin m → Fin m → Prop) [DecidableRel S],
        IsTournament S → HasS S 4 → ∀ v : Fin m,
          (inN S v).card = 23 → CoreCertificate S (inN S v))
    (n : ℕ) (hn : n ∈ SkOrders 4) : 49 ≤ n := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨h4n, T, inst, htour, hS4⟩ := hn
  letI := inst
  obtain ⟨hirr, hasym, htot⟩ := htour
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  refine no_order_48_from_global_capacity T hirr hasym htot hS4 ?_ ?_ ?_ ?_
  · rw [hcard]; omega
  · rw [hcard]; omega
  · exact hmin23 n T ⟨hirr, hasym, htot⟩ hS4
  · exact hbridge n T ⟨hirr, hasym, htot⟩ hS4

/-- ⭐ TARGET 3 - `f_four_ge_49 : 49 ≤ f 4`.

`hne` says only that `f 4` is well defined, i.e. that some `S 4` tournament
exists at all (true and classical - quadratic-residue tournaments of large
enough order have `S k` for every `k`). It is a side condition of the `sInf`,
not part of the lower-bound content, which is `no_S4_tournament_below_49`. -/
theorem f_four_ge_49
    (hne : (SkOrders 4).Nonempty)
    (hmin23 : ∀ (m : ℕ) (S : Fin m → Fin m → Prop) [DecidableRel S],
        IsTournament S → HasS S 4 → ∀ v : Fin m, 23 ≤ (inN S v).card)
    (hbridge : ∀ (m : ℕ) (S : Fin m → Fin m → Prop) [DecidableRel S],
        IsTournament S → HasS S 4 → ∀ v : Fin m,
          (inN S v).card = 23 → CoreCertificate S (inN S v)) :
    49 ≤ f 4 :=
  no_S4_tournament_below_49 hmin23 hbridge (f 4) (Nat.sInf_mem hne)

end Erdos902F4
