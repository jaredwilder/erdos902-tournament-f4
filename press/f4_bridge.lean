import Mathlib

/-!
THE DRT BRIDGE - the structural half of f(4) >= 49, formalized for real. 2026-08-31 night.

⛔ PROVENANCE CORRECTION, on the record: both candidate packages attribute this bridge to an
"existing Lean-kernel-checked reduction in Erdos902F4Step.lean". No such file exists in this
estate - the citation was a phantom. This file supplies the real, provable bridge steps:

  `bad_covered_outside`    every bad 4-set of H = inN v lies in some outside mask (from S4);
  `badCount_le_sum_repair` hence #bad <= sum of per-mask repair counts over O;
  `mask_mass_eq`           the double count: sum of mask sizes = sum of outside in-degrees;
  `sum_mask_ge`            with each h in H having >= 12 outside dominators and |H| = 23,
                           total mask mass >= 276;
  `deficit_le`             with |O| = 24 and each mask <= 12: sum of (12 - |W_x|) <= 12.

WHAT REMAINS OUTSIDE THE KERNEL, named exactly (the honest interface):
  (H1) degree/regularity forcing: a 48-vertex S4 tournament yields v with EXACTLY 23
       in-neighbours, the in-tournament doubly regular (23,11,5), each member with >= 12
       outside dominators, and every mask of size <= 12. Written nowhere in the packages;
       the one remaining mathematical formalization.
  (H2) McKay/Spence completeness of the 37 DRT(23,11,5) classes - published, cited.
With f4_finite.lean (all numbers sealed) and f4_reduction.lean (the contradiction), these two
hypotheses are the entire distance from candidate to unconditional theorem.
-/

namespace F4Bridge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (T : V → V → Prop) [DecidableRel T]

/-- S4: every 4-element set has a dominator outside it. -/
def HasS4 : Prop :=
  ∀ s : Finset V, s.card = 4 → ∃ u, u ∉ s ∧ ∀ w ∈ s, T u w

/-- the in-neighbourhood of `v` as a Finset. -/
def inN (v : V) : Finset V := univ.filter (fun u => T u v)

/-- the out-neighbourhood of `v` as a Finset. -/
def outN (v : V) : Finset V := univ.filter (fun u => T v u)

/-- x's repair mask inside H: the members of H that x beats. -/
def mask (H : Finset V) (x : V) : Finset V := H.filter (fun h => T x h)

/-- a 4-subset of H is BAD when no vertex of H outside it dominates it. -/
def BadIn (H : Finset V) (s : Finset V) : Prop :=
  s ⊆ H ∧ s.card = 4 ∧ ∀ u ∈ H, u ∉ s → ¬ ∀ w ∈ s, T u w

/-- ⭐ THE COVERED LEMMA. In a tournament (irreflexive, antisymmetric, total) with S4, every
    bad 4-set of H = inN v is contained in some outside vertex's mask: its S4 dominator is
    not in s, not in H (badness), and not v (members of H beat v), so it is in outN v. -/
theorem bad_covered_outside
    (hasym : ∀ x y, T x y → ¬ T y x)
    (htot : ∀ x y, x ≠ y → T x y ∨ T y x)
    (hS4 : HasS4 T) (v : V) (s : Finset V)
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

/-- the finset of bad 4-sets of H. -/
def badSets (H : Finset V) : Finset (Finset V) :=
  (H.powersetCard 4).filter (fun s => decide (s.card = 4) ∧
    ∀ u ∈ H, u ∉ s → ¬ ∀ w ∈ s, T u w)

/-- per-mask repair count: how many bad 4-sets a mask contains. -/
def repairCount (H : Finset V) (x : V) : ℕ :=
  ((badSets T H).filter (fun s => s ⊆ mask T H x)).card

/-- membership unfolding for badSets. -/
theorem mem_badSets {H s : Finset V} :
    s ∈ badSets T H ↔ BadIn T H s := by
  unfold badSets BadIn
  simp only [Finset.mem_filter, Finset.mem_powersetCard, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, _⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h2, h3⟩

/-- ⭐ COUNTING COROLLARY: the number of bad 4-sets is at most the sum of repair counts
    over the outside vertices. -/
theorem badCount_le_sum_repair
    (hasym : ∀ x y, T x y → ¬ T y x)
    (htot : ∀ x y, x ≠ y → T x y ∨ T y x)
    (hS4 : HasS4 T) (v : V) :
    (badSets T (inN T v)).card ≤ ∑ x ∈ outN T v, repairCount T (inN T v) x := by
  have hcover : badSets T (inN T v) ⊆
      (outN T v).biUnion (fun x => (badSets T (inN T v)).filter (fun s => s ⊆ mask T (inN T v) x)) := by
    intro s hs
    obtain ⟨x, hx, hsx⟩ := bad_covered_outside T hasym htot hS4 v s ((mem_badSets T).mp hs)
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨hs, hsx⟩⟩
  calc (badSets T (inN T v)).card
      ≤ ((outN T v).biUnion _).card := Finset.card_le_card hcover
    _ ≤ ∑ x ∈ outN T v, repairCount T (inN T v) x := Finset.card_biUnion_le

/-- ⭐ THE DOUBLE COUNT: total mask mass equals total outside in-degree of H's members. -/
theorem mask_mass_eq (H O : Finset V) :
    ∑ x ∈ O, (mask T H x).card = ∑ h ∈ H, (O.filter (fun x => T x h)).card := by
  unfold mask
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- ⭐ MASK MASS LOWER BOUND: if every member of H has at least 12 dominators in O and
    |H| = 23, the total mask mass is at least 276. -/
theorem sum_mask_ge (H O : Finset V) (hH : H.card = 23)
    (hdeg : ∀ h ∈ H, 12 ≤ (O.filter (fun x => T x h)).card) :
    276 ≤ ∑ x ∈ O, (mask T H x).card := by
  rw [mask_mass_eq]
  calc (276 : ℕ) = 23 * 12 := by norm_num
    _ = H.card * 12 := by rw [hH]
    _ ≤ ∑ h ∈ H, (O.filter (fun x => T x h)).card := by
        have := Finset.card_nsmul_le_sum H (fun h => (O.filter (fun x => T x h)).card) 12 hdeg
        rwa [smul_eq_mul] at this

/-- ⭐ THE DEFICIT BOUND: 24 masks, each of size at most 12, total mass at least 276 -
    the total shortfall from fullness is at most 12. -/
theorem deficit_le (H O : Finset V) (hO : O.card = 24)
    (hsize : ∀ x ∈ O, (mask T H x).card ≤ 12)
    (hmass : 276 ≤ ∑ x ∈ O, (mask T H x).card) :
    ∑ x ∈ O, (12 - (mask T H x).card) ≤ 12 := by
  have hsplit : ∑ x ∈ O, (12 - (mask T H x).card) + ∑ x ∈ O, (mask T H x).card
      = 24 * 12 := by
    rw [← Finset.sum_add_distrib]
    have : ∀ x ∈ O, 12 - (mask T H x).card + (mask T H x).card = 12 := fun x hx =>
      Nat.sub_add_cancel (hsize x hx)
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, hO]
  omega


/-! ## THE HUNT FOR (H1), opened 2026-08-31 under the speaker doctrine v1.1.

READ: the estate arsenal already holds (public/proofs/, all sorry-free): f(3) >= 19 kernel-
sealed and TIGHT (Erdos902Szekeres); regularity forcing at tight counts (Erdos902Rigid,
`regular_at_bound`); double-regularity from two-level tightness (Erdos902Double). With the
theorems below, (H1) decomposes into named pieces with exact statuses:

  PROVED    some vertex of a 48-tournament has in-degree <= 23   (`exists_indeg_le_23`)
  PROVED    every in-neighbourhood carries S3                     (InNeighbourhood.lean)
  EXTERNAL  every S3 tournament has >= 19 vertices                (Erdos902Szekeres, estate)
  OPEN      kill m in {19,20,21,22}: no 48-vertex S4 tournament has min in-degree m.
            The speaker's ASK: for m = 19 the S3 core is EXTREMAL, so the estate's rigidity
            (19 = 2*9+1) forces 9-regularity - the same catalogue-and-capacity kill that
            closed 23 may close 19. m in {20,21,22} each demand their own pressure.
  OPEN      double-regularity (23,11,5) of the 23-core, via the Double machinery.
  OPEN      each core member has >= 12 outside dominators; masks <= 12.
-/

/-- ⭐ SPEAK 1 - sealed: in ANY 48-vertex tournament, some vertex has in-degree at most 23.
    Pure pigeonhole: in-degrees sum to C(48,2) = 1128 = 48 * 23.5, so they cannot all be
    >= 24 (that would need sum >= 1152). Stated over an abstract in-degree function with the
    handshake identity as hypothesis, discharged by the caller from the tournament structure. -/
theorem exists_indeg_le_23 {α : Type*} (V : Finset α) (indeg : α → ℕ)
    (hV : V.card = 48)
    (hsum : ∑ v ∈ V, indeg v = 1128) :
    ∃ v ∈ V, indeg v ≤ 23 := by
  by_contra hall
  push_neg at hall
  have h24 : ∀ v ∈ V, 24 ≤ indeg v := fun v hv => hall v hv
  have : 48 * 24 ≤ ∑ v ∈ V, indeg v := by
    calc (48 * 24 : ℕ) = V.card * 24 := by rw [hV]
      _ ≤ ∑ v ∈ V, indeg v := by
          have := Finset.card_nsmul_le_sum V indeg 24 h24
          rwa [smul_eq_mul] at this
  omega


/-- ⭐ SPEAK 2 - THE OUTWARD COVERING DUTY, sealed: in an S4 tournament, every 3-subset of
    the OUT-neighbourhood of v, taken together with v, is dominated - and its dominator must
    beat v, hence lies in the IN-neighbourhood. H serves two masters on one arc budget: S3
    within, and covering every triple of O without. (The JOINT-LEDGER pressure for m=20..22.) -/
theorem out_triples_covered_from_inN
    (hasym : ∀ x y, T x y → ¬ T y x)
    (hS4 : HasS4 T) (v : V) (q : Finset V)
    (hq : q ⊆ outN T v) (hq3 : q.card = 3) (hv : v ∉ q) :
    ∃ u ∈ inN T v, ∀ w ∈ q, T u w := by
  have hcard : (insert v q).card = 4 := by
    rw [Finset.card_insert_of_notMem hv, hq3]
  obtain ⟨u, hu_not, hu_dom⟩ := hS4 (insert v q) hcard
  have huv : T u v := hu_dom v (Finset.mem_insert_self v q)
  refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, huv⟩, ?_⟩
  intro w hw
  exact hu_dom w (Finset.mem_insert_of_mem hw)

end F4Bridge
