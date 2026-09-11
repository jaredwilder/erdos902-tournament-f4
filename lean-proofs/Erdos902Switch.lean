/-
Erdos 902 -- THE EXACT SWITCH IDENTITY, and what it says about the switching potential.

Not `eight_k_sharpening`. One level beneath it: the exact change under a single sign-pair
switch, with no inequality anywhere, and then the true incidence operator read off from it.

SETTING (the drop's own).  `G` an abelian group, `D` a skew subset (for every `x != 0` exactly
one of `x`, `-x` lies in `D`), tournament `u -> v` iff `v - u` in `D`.  A vertex `x` DOMINATES a
`k`-set `A` iff `a - x` is in `D` for every `a` in `A`.  A switch at `z` in `D` replaces `z` by
`-z`.  A DEFECT of `x` is an `a` in `A` with `a - x` not in `D`; `x` dominates iff it has none.

⭐ THE IDENTITY (`mem_defects_switch`).  After switching `z`, the defects of `x` are EXACTLY

    (the old defects, minus `x - z`)  union  ({x + z} if it lies in A)

so a switch repairs at most the single element `x - z` and breaks at most the single
element `x + z`.  Exact, pointwise, no inequality, no skewness needed beyond `-z != z`.

⭐ THE INCIDENCE OPERATOR (`destroyers_eq`).  Fix a dominator `x`.  The set of switches that
destroy it is `{z in D : x + z in A}` -- and that set is EXACTLY the translate `A - x`, which
lies in `D` *precisely because x dominates A*.  Hence

    #(switches destroying x)  =  |A|  =  k,  EXACTLY, for every dominator, always.

⛔ THIS IS WHAT KILLS THE PROPOSED SHARPENING.  The drop needed to charge each destroyed
witness ONCE ("every destroyed low-reservoir witness is then charged exactly once"), turning
`k * c_D(A)` into `c_D(A)`.  The identity says the multiplicity `k` is not an artifact of loose
accounting that a cleverer charge can remove: THE VERY CONDITION THAT MAKES `x` A DOMINATOR --
that all `k` differences lie in `D` -- IS the condition that exposes it to all `k` switches.
`charge_once_undercounts` states this as a strict inequality: for `k >= 2` and any dominator at
all, charging once is strictly less than the true total.

⛔ AND THE ASYMMETRY IS EXACT, NOT ESTIMATED.  Destruction has multiplicity exactly `k` per
dominator (`destroy_mult`); repair has multiplicity AT MOST ONE per non-dominator
(`repair_unique`) -- because a vertex with a defect can only be fixed by the one switch that
inserts that defect's difference.  `k : 1`.  That ratio is the whole obstruction.

OUTCOME: this is result (2) of the three -- the destruction is genuine, so this potential's
switch accounting cannot collapse `k^2` to `O(k)`.  To drive the potential down one still needs
repair mass beating `k * c_D(A)`, i.e. of order `k * theta = O(k^2)`, which is exactly the
`N >~ k^2 2^k` classical loss the drop was trying to escape.  The escape route is closed; a
different potential or a restricted switch family (outcome 3) is not.
-/
import Mathlib

open Finset

namespace Erdos902Switch

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

/-- `x` dominates `A`: every element of `A` is beaten by `x`. -/
def Dominates (D A : Finset G) (x : G) : Prop := ∀ a ∈ A, a - x ∈ D

instance (D A : Finset G) (x : G) : Decidable (Dominates D A x) := by
  unfold Dominates; infer_instance

/-- Switching the sign-pair `{z, -z}`: `z` leaves `D`, `-z` enters. -/
def switch (D : Finset G) (z : G) : Finset G := insert (-z) (D.erase z)

/-- The dominators of `A`. -/
def Dom (D A : Finset G) : Finset G := univ.filter (fun x => Dominates D A x)

theorem mem_Dom {D A : Finset G} {x : G} : x ∈ Dom D A ↔ Dominates D A x := by
  simp [Dom]

/-! ### The exact identity -/

/-- **THE EXACT SWITCH IDENTITY, pointwise.**  After switching `z`, the element `a` is a defect
of `x` iff it was a defect and is not `x - z`, or it is `x + z`.

No inequality, no counting, no skewness beyond `-z ∉ D` (which skewness supplies for `z ∈ D`). -/
theorem mem_defects_switch (D : Finset G) {z : G} (hzD : z ∈ D) (hnz : -z ∉ D) (x a : G) :
    (a - x ∉ switch D z) ↔ ((a - x ∉ D ∧ a ≠ x - z) ∨ a = x + z) := by
  have hne : (-z : G) ≠ z := by
    intro h; apply hnz; rw [h]; exact hzD
  have hA : (a - x = -z) ↔ (a = x - z) := by
    constructor
    · intro h; rw [sub_eq_iff_eq_add.mp h]; abel
    · intro h; rw [h]; abel
  have hB : (a - x = z) ↔ (a = x + z) := by
    constructor
    · intro h; rw [sub_eq_iff_eq_add.mp h]; abel
    · intro h; rw [h]; abel
  -- `a = x + z` already forces `a ≠ x - z`, since `z = -z` is excluded
  have hxz : a = x + z → a ≠ x - z := by
    intro h hc
    apply hne
    have h1 : x + z = x - z := by rw [← h, hc]
    have h2 : x + z = x + (-z) := by rw [sub_eq_add_neg] at h1; exact h1
    exact (add_left_cancel h2).symm
  constructor
  · intro h
    simp only [switch, Finset.mem_insert, Finset.mem_erase, not_or, not_and] at h
    obtain ⟨h1, h2⟩ := h
    by_cases hc : a - x = z
    · exact Or.inr (hB.mp hc)
    · exact Or.inl ⟨h2 hc, fun hcon => h1 (hA.mpr hcon)⟩
  · intro h
    simp only [switch, Finset.mem_insert, Finset.mem_erase, not_or, not_and]
    rcases h with ⟨h1, h2⟩ | h
    · exact ⟨fun hcon => h2 (hA.mp hcon), fun _ => h1⟩
    · exact ⟨fun hcon => (hxz h) (hA.mp hcon), fun hcon => absurd (hB.mpr h) hcon⟩

/-! ### The destruction side: multiplicity exactly `k` -/

/-- **THE INCIDENCE OPERATOR.**  For a dominator `x`, the switches that destroy it are exactly
the translate `A - x` -- and that translate lies inside `D` *because* `x` dominates. -/
theorem destroyers_eq (D A : Finset G) (x : G) (h : Dominates D A x) :
    D.filter (fun z => x + z ∈ A) = A.image (fun a => a - x) := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨-, hxz⟩
    exact ⟨x + z, hxz, by abel⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨h a ha, ?_⟩
    have hxa : x + (a - x) = a := by abel
    rw [hxa]; exact ha

/-- **DESTRUCTION MULTIPLICITY IS EXACTLY `k`.**  Every dominator of a `k`-set is destroyed by
exactly `k` of the switches.  This is an identity, not a bound. -/
theorem destroy_mult (D A : Finset G) (x : G) (h : Dominates D A x) :
    (D.filter (fun z => x + z ∈ A)).card = A.card := by
  rw [destroyers_eq D A x h]
  exact Finset.card_image_of_injective A (fun u v huv => by
    have := congrArg (· + x) huv
    simpa using this)

/-- The same fact summed over all switches: the total destruction is exactly `k * c_D(A)`. -/
theorem total_destruction (D A : Finset G) :
    ∑ z ∈ D, ((Dom D A).filter (fun x => x + z ∈ A)).card = (Dom D A).card * A.card := by
  have hinner : ∀ x ∈ Dom D A, (∑ z ∈ D, if x + z ∈ A then 1 else 0) = A.card := by
    intro x hx
    have hdom : Dominates D A x := mem_Dom.mp hx
    have := destroy_mult D A x hdom
    rwa [Finset.card_filter] at this
  simp only [Finset.card_filter]
  rw [Finset.sum_comm, Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]

/-- **THE KILL.**  Charging each destroyed dominator ONCE -- the step the drop needs to turn
`8k^2` into `8k` -- strictly undercounts the true destruction whenever `k >= 2` and a dominator
exists.  The factor `k` is forced by the domination condition itself. -/
theorem charge_once_undercounts (D A : Finset G) (hk : 2 ≤ A.card) (hpos : 0 < (Dom D A).card) :
    (Dom D A).card < ∑ z ∈ D, ((Dom D A).filter (fun x => x + z ∈ A)).card := by
  rw [total_destruction]
  nlinarith [hk, hpos]

/-! ### The repair side: multiplicity at most one -/

/-- **REPAIR MULTIPLICITY IS AT MOST ONE.**  A vertex that does not already dominate `A` can be
made a dominator by at most ONE switch: a defect `a` can only be repaired by the switch that
inserts `a - x`, and that switch is determined by `a`. -/
theorem repair_unique (D A : Finset G) (x : G) (hx : ¬ Dominates D A x) {z₁ z₂ : G}
    (h1 : Dominates (switch D z₁) A x) (h2 : Dominates (switch D z₂) A x) : z₁ = z₂ := by
  rw [Dominates] at hx
  push_neg at hx
  obtain ⟨a, ha, hna⟩ := hx
  have key : ∀ z : G, Dominates (switch D z) A x → a - x = -z := by
    intro z hz
    have hmem := hz a ha
    simp only [switch, Finset.mem_insert, Finset.mem_erase] at hmem
    rcases hmem with hmem | hmem
    · exact hmem
    · exact absurd hmem.2 hna
  have e1 := key z₁ h1
  have e2 := key z₂ h2
  have : -z₁ = -z₂ := by rw [← e1, ← e2]
  simpa using this

/-- **THE ASYMMETRY, IN ONE STATEMENT.**  Destruction has multiplicity exactly `k` per
dominator; repair has multiplicity at most `1` per non-dominator.  `k : 1`. -/
theorem switch_asymmetry (D A : Finset G) (x y : G)
    (hx : Dominates D A x) (hy : ¬ Dominates D A y) :
    (D.filter (fun z => x + z ∈ A)).card = A.card ∧
      ∀ {z₁ z₂ : G}, Dominates (switch D z₁) A y → Dominates (switch D z₂) A y → z₁ = z₂ :=
  ⟨destroy_mult D A x hx, fun h1 h2 => repair_unique D A y hy h1 h2⟩

/-! ### OUTCOME 3: the conserved quantity underneath every switch

The destruction multiplicity `k` is forced (above), so a potential cannot dodge it by cleverer
charging.  The remaining question is what a switch can do AT ALL.  Answer: it moves domination
mass around, and never creates any.

`total_domination` is an exact double count: summing `c_D(A)` over every `k`-set gives
`N * C(|D|, k)`, which depends on `D` ONLY through its cardinality.  A switch preserves
cardinality.  Hence:

⭐ **EVERY SWITCH IS A TRANSPORT.**  `Sum_A c_D(A)` is invariant under every switch, exactly.

Two consequences, both sharp:

* The drop's section 2 computes the MEAN number of dominators and finds it `> 32k`.  That
  quantity is invariant under every switch, so it can never be evidence that switching makes
  progress.  It is a feasibility check, not a step.
* `threshold_le_mean`: if a tournament has every `k`-set dominated `theta` times over, then
  `theta * C(N,k) <= N * C(|D|,k)`.  No switching argument, no potential, and no charge
  accounting can beat this -- it is a conservation law, not an estimate.  Any successful
  potential must act on the TAIL of the distribution of `c`, because the mean is not its to move.
-/

/-- **THE CONSERVED QUANTITY.**  Total domination mass, by double counting: for each `x` the
`k`-sets dominated by `x` are exactly the `k`-subsets of the translate `D + x`. -/
theorem total_domination (D : Finset G) (k : ℕ) :
    ∑ A ∈ (univ : Finset G).powersetCard k, (Dom D A).card
      = Fintype.card G * (D.card).choose k := by
  have hset : ∀ x : G, (((univ : Finset G).powersetCard k).filter (fun A => Dominates D A x)).card
      = (D.card).choose k := by
    intro x
    have himg : ((univ : Finset G).powersetCard k).filter (fun A => Dominates D A x)
        = (D.image (fun d => d + x)).powersetCard k := by
      ext A
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨-, hcard⟩, hdom⟩
        refine ⟨fun {a} ha => ?_, hcard⟩
        exact Finset.mem_image.mpr ⟨a - x, hdom a ha, by abel⟩
      · rintro ⟨hsub, hcard⟩
        refine ⟨⟨Finset.subset_univ _, hcard⟩, fun a ha => ?_⟩
        obtain ⟨d, hd, hdx⟩ := Finset.mem_image.mp (hsub ha)
        have hax : a - x = d := by rw [← hdx]; abel
        rw [hax]; exact hd
    rw [himg, Finset.card_powersetCard,
      Finset.card_image_of_injective _ (add_left_injective x)]
  simp only [Dom, Finset.card_filter]
  rw [Finset.sum_comm]
  have hinner : ∀ x ∈ (univ : Finset G), (∑ A ∈ (univ : Finset G).powersetCard k,
      if Dominates D A x then 1 else 0) = (D.card).choose k := by
    intro x _
    rw [← Finset.card_filter]
    exact hset x
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- A switch preserves `|D|`: `z` leaves, `-z` enters. -/
theorem switch_card (D : Finset G) {z : G} (hz : z ∈ D) (hnz : -z ∉ D) :
    (switch D z).card = D.card := by
  have hpos : 1 ≤ D.card := Finset.card_pos.mpr ⟨z, hz⟩
  have hnotmem : -z ∉ D.erase z := fun h => hnz (Finset.mem_of_mem_erase h)
  rw [switch, Finset.card_insert_of_notMem hnotmem, Finset.card_erase_of_mem hz]
  omega

/-- **MASS CONSERVATION.**  The total domination mass is invariant under every switch. -/
theorem mass_conservation (D : Finset G) {z : G} (hz : z ∈ D) (hnz : -z ∉ D) (k : ℕ) :
    ∑ A ∈ (univ : Finset G).powersetCard k, (Dom (switch D z) A).card
      = ∑ A ∈ (univ : Finset G).powersetCard k, (Dom D A).card := by
  rw [total_domination, total_domination, switch_card D hz hnz]

/-- **THE FEASIBILITY LAW.**  If every `k`-set is dominated at least `theta` times, then
`theta * C(N,k) <= N * C(|D|,k)`.  A conservation law, so no potential, charge, or switch
family can evade it. -/
theorem threshold_le_mean (D : Finset G) (k θ : ℕ)
    (h : ∀ A ∈ (univ : Finset G).powersetCard k, θ ≤ (Dom D A).card) :
    θ * ((Fintype.card G).choose k) ≤ Fintype.card G * (D.card).choose k := by
  calc θ * ((Fintype.card G).choose k)
      = ∑ _A ∈ (univ : Finset G).powersetCard k, θ := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, smul_eq_mul,
          Nat.mul_comm]
    _ ≤ ∑ A ∈ (univ : Finset G).powersetCard k, (Dom D A).card := Finset.sum_le_sum h
    _ = _ := total_domination D k

/-- Specialised to Schutte's property itself (`theta = 1`): a necessary condition on any such
tournament, obtained with no probabilistic argument at all. -/
theorem schutte_necessary (D : Finset G) (k : ℕ)
    (h : ∀ A ∈ (univ : Finset G).powersetCard k, 0 < (Dom D A).card) :
    (Fintype.card G).choose k ≤ Fintype.card G * (D.card).choose k := by
  have := threshold_le_mean D k 1 (fun A hA => h A hA)
  simpa using this

#print axioms mem_defects_switch
#print axioms destroyers_eq
#print axioms destroy_mult
#print axioms total_destruction
#print axioms charge_once_undercounts
#print axioms repair_unique
#print axioms switch_asymmetry
#print axioms total_domination
#print axioms mass_conservation
#print axioms threshold_le_mean
#print axioms schutte_necessary

end Erdos902Switch
