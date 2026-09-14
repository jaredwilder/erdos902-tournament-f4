import Mathlib

/-!
JOB 1 - THE STRUCTURAL BRIDGE for f(4) >= 49, formalized.

Reid-McRae-Hedetniemi-Hedetniemi, AJC 29 (2004) 157-172, Proposition 14, generalized to an
ARBITRARY triple (the paper's proof uses no ordering on {a,b,c}; the (v,x,h) application needs
that generality, with x outside I(v)).

  5 <= |I a cap I b cap I c|   ->   11 <= |I a cap I b|   ->   23 <= |I a|
-/

namespace F4

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (T : V → V → Prop) [DecidableRel T]

structure IsTournament : Prop where
  irr : ∀ x, ¬ T x x
  asy : ∀ x y, T x y → ¬ T y x
  tot : ∀ x y, x ≠ y → T x y ∨ T y x

def Dominating (D : Finset V) : Prop := ∀ v, v ∉ D → ∃ d ∈ D, T d v

/-- ⭐ THE KEY EQUIVALENCE behind Prop 14: a set has NO dominator exactly when it IS
    a dominating set. This is what turns 'no x dominates S' into '|S| >= gamma'. -/
theorem dominating_iff (ht : IsTournament T) (S : Finset V) :
    Dominating T S ↔ ¬ ∃ u, u ∉ S ∧ ∀ s ∈ S, T u s := by
  constructor
  · rintro hD ⟨u, huS, hu⟩
    obtain ⟨d, hd, hdu⟩ := hD u huS
    exact ht.asy u d (hu d hd) hdu
  · intro h v hv
    by_contra hc
    push_neg at hc
    refine h ⟨v, hv, fun s hs => ?_⟩
    rcases ht.tot v s (by rintro rfl; exact hv hs) with h1 | h1
    · exact h1
    · exact absurd h1 (hc s hs)

def dom1 (a : V) : Finset V := univ.filter (fun u => T u a)
def dom2 (a b : V) : Finset V := univ.filter (fun u => T u a ∧ T u b)
def dom3 (a b c : V) : Finset V := univ.filter (fun u => T u a ∧ T u b ∧ T u c)

@[simp] theorem mem_dom1 {a u : V} : u ∈ dom1 T a ↔ T u a := by simp [dom1]
@[simp] theorem mem_dom2 {a b u : V} : u ∈ dom2 T a b ↔ T u a ∧ T u b := by simp [dom2]
@[simp] theorem mem_dom3 {a b c u : V} : u ∈ dom3 T a b c ↔ T u a ∧ T u b ∧ T u c := by simp [dom3]

/-- ⭐ PROPOSITION 14 (core), for an ARBITRARY triple. -/
theorem triple_ge_five (ht : IsTournament T)
    (hS4 : ∀ D : Finset V, D.card ≤ 4 → ¬ Dominating T D) (a b c : V) :
    5 ≤ (dom3 T a b c).card := by
  by_contra hlt
  push_neg at hlt
  by_cases h : ∃ u, u ∉ dom3 T a b c ∧ ∀ s ∈ dom3 T a b c, T u s
  · obtain ⟨x, hxn, hxd⟩ := h
    have h4 : (({a, b, c, x} : Finset V)).card ≤ 4 := by
      have h1 := Finset.card_insert_le a ({b, c, x} : Finset V)
      have h2 := Finset.card_insert_le b ({c, x} : Finset V)
      have h3 := Finset.card_insert_le c ({x} : Finset V)
      have h4 : ({x} : Finset V).card = 1 := Finset.card_singleton x
      omega
    refine hS4 _ h4 ?_
    intro w hw
    simp only [mem_insert, mem_singleton, not_or] at hw
    obtain ⟨hwa, hwb, hwc, hwx⟩ := hw
    by_cases hwS : w ∈ dom3 T a b c
    · exact ⟨x, by simp, hxd w hwS⟩
    · rw [mem_dom3] at hwS
      rcases not_and_or.mp hwS with h1 | h1
      · exact ⟨a, by simp, (ht.tot w a hwa).resolve_left h1⟩
      · rcases not_and_or.mp h1 with h2 | h2
        · exact ⟨b, by simp, (ht.tot w b hwb).resolve_left h2⟩
        · exact ⟨c, by simp, (ht.tot w c hwc).resolve_left h2⟩
  · exact hS4 _ (by omega) ((dominating_iff T ht _).mpr h)

/-- in a tournament, P minus c splits into c's in- and out-neighbours inside P. -/
theorem card_split (ht : IsTournament T) (P : Finset V) (c : V) (hc : c ∈ P) :
    (P.filter (fun u => T u c)).card + (P.filter (fun u => T c u)).card + 1 = P.card := by
  have hpos : 0 < P.card := Finset.card_pos.mpr ⟨c, hc⟩
  have hdisj : Disjoint (P.filter (fun u => T u c)) (P.filter (fun u => T c u)) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    simp only [mem_filter] at hu hu'
    exact ht.asy u c hu.2 hu'.2
  have hunion : (P.filter (fun u => T u c)) ∪ (P.filter (fun u => T c u)) = P.erase c := by
    ext u
    simp only [mem_union, mem_filter, mem_erase]
    constructor
    · rintro (⟨hu, h⟩ | ⟨hu, h⟩)
      · refine ⟨?_, hu⟩; rintro rfl; exact ht.irr u h
      · refine ⟨?_, hu⟩; rintro rfl; exact ht.irr u h
    · rintro ⟨hne, hu⟩
      rcases ht.tot u c hne with h | h
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr ⟨hu, h⟩
  have hcu := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_erase_of_mem hc] at hcu
  omega

theorem sum_in_eq_sum_out (P : Finset V) :
    ∑ c ∈ P, (P.filter (fun u => T u c)).card = ∑ c ∈ P, (P.filter (fun u => T c u)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- min in-degree m inside P  =>  |P| >= 2m+1. -/
theorem card_ge_of_min_indeg (ht : IsTournament T) (P : Finset V) (m : ℕ)
    (hne : P.Nonempty) (hmin : ∀ c ∈ P, m ≤ (P.filter (fun u => T u c)).card) :
    2 * m + 1 ≤ P.card := by
  have hpos : 0 < P.card := Finset.card_pos.mpr hne
  have hsplit : (∑ c ∈ P, (P.filter (fun u => T u c)).card)
      + (∑ c ∈ P, (P.filter (fun u => T c u)).card) + P.card = P.card * P.card := by
    have h : ∑ c ∈ P, ((P.filter (fun u => T u c)).card
        + (P.filter (fun u => T c u)).card + 1) = ∑ _c ∈ P, P.card :=
      Finset.sum_congr rfl (fun c hc => card_split T ht P c hc)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
        smul_eq_mul, smul_eq_mul, mul_one] at h
    exact h
  have heq := sum_in_eq_sum_out T P
  have hlow : P.card * m ≤ ∑ c ∈ P, (P.filter (fun u => T u c)).card := by
    have := Finset.card_nsmul_le_sum P (fun c => (P.filter (fun u => T u c)).card) m hmin
    rwa [smul_eq_mul] at this
  have key : P.card * (2 * m + 1) ≤ P.card * P.card := by
    have h2 : 2 * (P.card * m) + P.card ≤ P.card * P.card := by linarith
    calc P.card * (2 * m + 1) = 2 * (P.card * m) + P.card := by ring
      _ ≤ P.card * P.card := h2
  exact Nat.le_of_mul_le_mul_left key hpos



/-! ## THE CHAIN  5 -> 11 -> 23 -/

theorem dom2_filter (a b c : V) :
    (dom2 T a b).filter (fun u => T u c) = dom3 T a b c := by
  ext u; simp only [Finset.mem_filter, mem_dom2, mem_dom3]; try tauto

theorem dom1_filter (a b : V) :
    (dom1 T a).filter (fun u => T u b) = dom2 T a b := by
  ext u; simp only [Finset.mem_filter, mem_dom1, mem_dom2]; try tauto

theorem pair_ge_eleven (ht : IsTournament T)
    (hS4 : ∀ D : Finset V, D.card ≤ 4 → ¬ Dominating T D) (a b : V) :
    11 ≤ (dom2 T a b).card := by
  have hsub : dom3 T a b a ⊆ dom2 T a b := by
    intro u hu; rw [mem_dom3] at hu; rw [mem_dom2]; exact ⟨hu.1, hu.2.1⟩
  have hne : (dom2 T a b).Nonempty := by
    have h5 := triple_ge_five T ht hS4 a b a
    have h0 : 0 < (dom2 T a b).card :=
      lt_of_lt_of_le (by omega) (Finset.card_le_card hsub)
    exact Finset.card_pos.mp h0
  have := card_ge_of_min_indeg T ht (dom2 T a b) 5 hne (fun c _ => by
    rw [dom2_filter]; exact triple_ge_five T ht hS4 a b c)
  omega

theorem vertex_ge_23 (ht : IsTournament T)
    (hS4 : ∀ D : Finset V, D.card ≤ 4 → ¬ Dominating T D) (a : V) :
    23 ≤ (dom1 T a).card := by
  have hsub : dom2 T a a ⊆ dom1 T a := by
    intro u hu; rw [mem_dom2] at hu; rw [mem_dom1]; exact hu.1
  have hne : (dom1 T a).Nonempty := by
    have h11 := pair_ge_eleven T ht hS4 a a
    have h0 : 0 < (dom1 T a).card :=
      lt_of_lt_of_le (by omega) (Finset.card_le_card hsub)
    exact Finset.card_pos.mp h0
  have := card_ge_of_min_indeg T ht (dom1 T a) 11 hne (fun b _ => by
    rw [dom1_filter]; exact pair_ge_eleven T ht hS4 a b)
  omega

/-! ## SATURATION AT ORDER 48 -/

theorem sum_indeg (ht : IsTournament T) (P : Finset V) :
    2 * (∑ c ∈ P, (P.filter (fun u => T u c)).card) + P.card = P.card * P.card := by
  have h : ∑ c ∈ P, ((P.filter (fun u => T u c)).card
      + (P.filter (fun u => T c u)).card + 1) = ∑ _c ∈ P, P.card :=
    Finset.sum_congr rfl (fun c hc => card_split T ht P c hc)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
      smul_eq_mul, smul_eq_mul, mul_one] at h
  have heq := sum_in_eq_sum_out T P
  omega

theorem all_eq_of_sum (P : Finset V) (f : V → ℕ) (m : ℕ)
    (hmin : ∀ c ∈ P, m ≤ f c) (hsum : ∑ c ∈ P, f c = P.card * m) : ∀ c ∈ P, f c = m := by
  have h : ∑ _c ∈ P, m = ∑ c ∈ P, f c := by
    rw [Finset.sum_const, smul_eq_mul, hsum]
  intro c hc
  exact ((Finset.sum_eq_sum_iff_of_le hmin).mp h c hc).symm



/-! ## ORDER 48 : some vertex has in-degree EXACTLY 23 -/

theorem exists_indeg_23 (ht : IsTournament T)
    (hS4 : ∀ D : Finset V, D.card ≤ 4 → ¬ Dominating T D) (hV : Fintype.card V = 48) :
    ∃ v : V, (dom1 T v).card = 23 := by
  by_contra hcon
  push_neg at hcon
  have h24 : ∀ v : V, 24 ≤ (dom1 T v).card := by
    intro v; have h1 := vertex_ge_23 T ht hS4 v; have h2 := hcon v; omega
  have hs := sum_indeg T ht Finset.univ
  rw [Finset.card_univ, hV] at hs
  have hlow : (Finset.univ : Finset V).card * 24
      ≤ ∑ c ∈ (Finset.univ : Finset V), ((Finset.univ : Finset V).filter (fun u => T u c)).card := by
    have := Finset.card_nsmul_le_sum (Finset.univ : Finset V)
      (fun c => ((Finset.univ : Finset V).filter (fun u => T u c)).card) 24 (fun c _ => h24 c)
    rwa [smul_eq_mul] at this
  rw [Finset.card_univ, hV] at hlow
  omega

/-! ## SATURATION : the core is a DRT(23,11,5) -/

theorem core_regular (ht : IsTournament T)
    (hS4 : ∀ D : Finset V, D.card ≤ 4 → ¬ Dominating T D) (v : V)
    (hv : (dom1 T v).card = 23) :
    ∀ h ∈ dom1 T v, ((dom1 T v).filter (fun u => T u h)).card = 11 := by
  refine all_eq_of_sum (dom1 T v) (fun h => ((dom1 T v).filter (fun u => T u h)).card) 11
    (fun c _ => by rw [dom1_filter]; exact pair_ge_eleven T ht hS4 v c) ?_
  have hs := sum_indeg T ht (dom1 T v)
  rw [hv] at hs ⊢
  omega

theorem dom3_swap (a b c : V) : dom3 T a b c = dom3 T a c b := by
  ext u; simp only [mem_dom3]; tauto

theorem core_doubly (ht : IsTournament T)
    (hS4 : ∀ D : Finset V, D.card ≤ 4 → ¬ Dominating T D) (v : V)
    (hv : (dom1 T v).card = 23) (h : V) (hh : h ∈ dom1 T v) :
    ∀ c ∈ (dom1 T v).filter (fun u => T u h), (dom3 T v h c).card = 5 := by
  have hK : (dom1 T v).filter (fun u => T u h) = dom2 T v h := dom1_filter T v h
  have h11 : (dom2 T v h).card = 11 := by rw [← hK]; exact core_regular T ht hS4 v hv h hh
  rw [hK]
  refine all_eq_of_sum (dom2 T v h) (fun c => (dom3 T v h c).card) 5
    (fun c _ => triple_ge_five T ht hS4 v h c) ?_
  have hs := sum_indeg T ht (dom2 T v h)
  rw [h11] at hs ⊢
  have hcongr : ∑ c ∈ dom2 T v h, ((dom2 T v h).filter (fun u => T u c)).card
      = ∑ c ∈ dom2 T v h, (dom3 T v h c).card :=
    Finset.sum_congr rfl (fun c _ => by rw [dom2_filter])
  omega

/-! ## THE CORE HAS S3 -/

theorem core_hasS3 (ht : IsTournament T)
    (hasS4 : ∀ s : Finset V, s.card = 4 → ∃ u, u ∉ s ∧ ∀ w ∈ s, T u w) (v : V) :
    ∀ s : Finset V, s ⊆ dom1 T v → s.card = 3 → ∃ u ∈ dom1 T v, u ∉ s ∧ ∀ w ∈ s, T u w := by
  intro s hsub hcard
  have hvs : v ∉ s := fun hv => ht.irr v (by have := hsub hv; rwa [mem_dom1] at this)
  have hc4 : (insert v s).card = 4 := by rw [Finset.card_insert_of_notMem hvs, hcard]
  obtain ⟨u, hu, hud⟩ := hasS4 (insert v s) hc4
  refine ⟨u, ?_, fun hus => hu (Finset.mem_insert_of_mem hus),
    fun w hw => hud w (Finset.mem_insert_of_mem hw)⟩
  rw [mem_dom1]; exact hud v (Finset.mem_insert_self v s)

/-! ## THE OUTSIDE MASKS ARE ADMISSIBLE -/

def outside (v : V) : Finset V := Finset.univ.filter (fun x => T v x)

theorem mask_admissible (ht : IsTournament T)
    (hS4 : ∀ D : Finset V, D.card ≤ 4 → ¬ Dominating T D) (v : V)
    (hv : (dom1 T v).card = 23) (x : V) (hx : x ∈ outside T v) (h : V) (hh : h ∈ dom1 T v) :
    (((dom1 T v).filter (fun u => T u h)).filter (fun u => T x u)).card ≤ 6 := by
  have hxv : T v x := by rw [outside, Finset.mem_filter] at hx; exact hx.2
  have h11 : ((dom1 T v).filter (fun u => T u h)).card = 11 := core_regular T ht hS4 v hv h hh
  set K := (dom1 T v).filter (fun u => T u h) with hKdef
  have hneg : K.filter (fun u => ¬ T x u) = dom3 T v x h := by
    ext u
    simp only [hKdef, Finset.mem_filter, mem_dom1, mem_dom3]
    constructor
    · rintro ⟨⟨huv, huh⟩, hnx⟩
      have hux : u ≠ x := by rintro rfl; exact ht.asy u v huv hxv
      exact ⟨huv, (ht.tot u x hux).resolve_right hnx, huh⟩
    · rintro ⟨huv, hux, huh⟩
      exact ⟨⟨huv, huh⟩, ht.asy u x hux⟩
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := K) (p := fun u => T x u)
  rw [hneg, h11] at hsplit
  have h5 := triple_ge_five T ht hS4 v x h
  omega

/-! ## THE COVER : every bad 4-set of the core lies in an outside mask -/

def badSets (H : Finset V) : Finset (Finset V) :=
  (H.powersetCard 4).filter (fun s => ∀ u ∈ H, u ∉ s → ¬ ∀ w ∈ s, T u w)

def maskOf (H : Finset V) (x : V) : Finset V := H.filter (fun h => T x h)

def repairCount (H : Finset V) (x : V) : ℕ :=
  ((badSets T H).filter (fun s => s ⊆ maskOf T H x)).card

theorem bad_covered (ht : IsTournament T)
    (hasS4 : ∀ s : Finset V, s.card = 4 → ∃ u, u ∉ s ∧ ∀ w ∈ s, T u w) (v : V)
    (s : Finset V) (hs : s ∈ badSets T (dom1 T v)) :
    ∃ x ∈ outside T v, s ⊆ maskOf T (dom1 T v) x := by
  rw [badSets, Finset.mem_filter, Finset.mem_powersetCard] at hs
  obtain ⟨⟨hsub, hcard⟩, hnodom⟩ := hs
  obtain ⟨u, hu_not, hu_dom⟩ := hasS4 s hcard
  have hu_notH : u ∉ dom1 T v := fun huH => hnodom u huH hu_not hu_dom
  have hs_ne : s.Nonempty := by rw [← Finset.card_pos, hcard]; norm_num
  obtain ⟨w, hw⟩ := hs_ne
  have hwv : T w v := by have := hsub hw; rwa [mem_dom1] at this
  have hu_ne_v : u ≠ v := by rintro rfl; exact ht.asy w u hwv (hu_dom w hw)
  have hu_out : u ∈ outside T v := by
    rw [outside, Finset.mem_filter]
    refine ⟨Finset.mem_univ u, ?_⟩
    rcases ht.tot u v hu_ne_v with h1 | h1
    · exact absurd (by rw [mem_dom1]; exact h1) hu_notH
    · exact h1
  exact ⟨u, hu_out, fun w2 hw2 => Finset.mem_filter.mpr ⟨hsub hw2, hu_dom w2 hw2⟩⟩

theorem badCount_le_sum (ht : IsTournament T)
    (hasS4 : ∀ s : Finset V, s.card = 4 → ∃ u, u ∉ s ∧ ∀ w ∈ s, T u w) (v : V) :
    (badSets T (dom1 T v)).card ≤ ∑ x ∈ outside T v, repairCount T (dom1 T v) x := by
  have hcover : badSets T (dom1 T v) ⊆ (outside T v).biUnion
      (fun x => (badSets T (dom1 T v)).filter (fun s => s ⊆ maskOf T (dom1 T v) x)) := by
    intro s hs
    obtain ⟨x, hx, hsx⟩ := bad_covered T ht hasS4 v s hs
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨hs, hsx⟩⟩
  calc (badSets T (dom1 T v)).card ≤ _ := Finset.card_le_card hcover
    _ ≤ ∑ x ∈ outside T v, repairCount T (dom1 T v) x := Finset.card_biUnion_le

theorem outside_card (ht : IsTournament T) (hV : Fintype.card V = 48) (v : V)
    (hv : (dom1 T v).card = 23) : (outside T v).card = 24 := by
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset V)) (p := fun u => T u v)
  have hneg : (Finset.univ : Finset V).filter (fun u => ¬ T u v) = insert v (outside T v) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, outside]
    constructor
    · intro hnu
      by_cases he : u = v
      · exact Or.inl he
      · exact Or.inr ((ht.tot u v he).resolve_left hnu)
    · rintro (rfl | hu)
      · exact ht.irr u
      · exact ht.asy v u hu
  have hvout : v ∉ outside T v := by
    rw [outside, Finset.mem_filter]; rintro ⟨-, h⟩; exact ht.irr v h
  rw [hneg, Finset.card_insert_of_notMem hvout, Finset.card_univ, hV] at hsplit
  have : (Finset.univ : Finset V).filter (fun u => T u v) = dom1 T v := rfl
  rw [this, hv] at hsplit
  omega



/-! ## S4 (dominator form) implies no small dominating set -/

theorem no_dom_le_four (ht : IsTournament T) (hV4 : 4 ≤ Fintype.card V)
    (hasS4 : ∀ s : Finset V, s.card = 4 → ∃ u, u ∉ s ∧ ∀ w ∈ s, T u w) :
    ∀ D : Finset V, D.card ≤ 4 → ¬ Dominating T D := by
  intro D hD hdom
  obtain ⟨E, hDE, hE⟩ := Finset.exists_superset_card_eq hD hV4
  have hEdom : Dominating T E := by
    intro w hw
    obtain ⟨d, hd, hdw⟩ := hdom w (fun h => hw (hDE h))
    exact ⟨d, hDE hd, hdw⟩
  obtain ⟨u, hu, hud⟩ := hasS4 E hE
  exact ((dominating_iff T ht E).mp hEdom) ⟨u, hu, hud⟩

/-! ## order <= 48 : some vertex has in-degree exactly 23 (kills 47 AND 48) -/

theorem exists_indeg_23_le (ht : IsTournament T)
    (hS4 : ∀ D : Finset V, D.card ≤ 4 → ¬ Dominating T D)
    (hpos : 0 < Fintype.card V) (hle : Fintype.card V ≤ 49) :
    ∃ v : V, (dom1 T v).card = 23 := by
  by_contra hcon
  push_neg at hcon
  have h24 : ∀ v : V, 24 ≤ (dom1 T v).card := by
    intro v; have h1 := vertex_ge_23 T ht hS4 v; have h2 := hcon v; omega
  have hs := sum_indeg T ht Finset.univ
  rw [Finset.card_univ] at hs
  have hlow : (Finset.univ : Finset V).card * 24
      ≤ ∑ c ∈ (Finset.univ : Finset V), ((Finset.univ : Finset V).filter (fun u => T u c)).card := by
    have := Finset.card_nsmul_le_sum (Finset.univ : Finset V)
      (fun c => ((Finset.univ : Finset V).filter (fun u => T u c)).card) 24 (fun c _ => h24 c)
    rwa [smul_eq_mul] at this
  rw [Finset.card_univ] at hlow
  have h49 : Fintype.card V * 49 ≤ Fintype.card V * Fintype.card V := by nlinarith [hs, hlow]
  have := Nat.le_of_mul_le_mul_left h49 hpos
  omega

theorem outside_card_eq (ht : IsTournament T) (v : V) (hv : (dom1 T v).card = 23) :
    (outside T v).card + 24 = Fintype.card V := by
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset V)) (p := fun u => T u v)
  have hneg : (Finset.univ : Finset V).filter (fun u => ¬ T u v) = insert v (outside T v) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, outside]
    constructor
    · intro hnu
      by_cases he : u = v
      · exact Or.inl he
      · exact Or.inr ((ht.tot u v he).resolve_left hnu)
    · rintro (rfl | hu)
      · exact ht.irr u
      · exact ht.asy v u hu
  have hvout : v ∉ outside T v := by
    rw [outside, Finset.mem_filter]; rintro ⟨-, h⟩; exact ht.irr v h
  rw [hneg, Finset.card_insert_of_notMem hvout, Finset.card_univ] at hsplit
  have hd : (Finset.univ : Finset V).filter (fun u => T u v) = dom1 T v := rfl
  rw [hd, hv] at hsplit
  omega

/-! ## ⭐⭐ THE TOP-LEVEL CIRCUIT

`hExt` is the ONLY external input: for a core that is a DRT(23,11,5) with S3 -- which by the
published completeness of the 37 DRT(23,11,5) classes (McKay/Spence) plus isomorphism
transport must be catalogue row 35 or 36 -- the bad-4-set count is at least 2475 and every
admissible outside mask repairs at most 66. Both numbers are the finite layer
(f4_finite.lean, `native_decide`; independently Python-replicated).

EVERYTHING ELSE IS PROVED HERE. -/

theorem no_S4_of_card_le_48 (ht : IsTournament T)
    (hasS4 : ∀ s : Finset V, s.card = 4 → ∃ u, u ∉ s ∧ ∀ w ∈ s, T u w)
    (h4 : 4 ≤ Fintype.card V) (hle : Fintype.card V ≤ 49)
    (hExt : ∀ v : V,
        (dom1 T v).card = 23 →
        (∀ h ∈ dom1 T v, ((dom1 T v).filter (fun u => T u h)).card = 11) →
        (∀ h ∈ dom1 T v, ∀ c ∈ (dom1 T v).filter (fun u => T u h), (dom3 T v h c).card = 5) →
        (∀ s : Finset V, s ⊆ dom1 T v → s.card = 3 →
            ∃ u ∈ dom1 T v, u ∉ s ∧ ∀ w ∈ s, T u w) →
        2475 ≤ (badSets T (dom1 T v)).card
        ∧ ∀ x ∈ outside T v,
            (∀ h ∈ dom1 T v,
              (((dom1 T v).filter (fun u => T u h)).filter (fun u => T x u)).card ≤ 6) →
            repairCount T (dom1 T v) x ≤ 66) :
    False := by
  have hS4 : ∀ D : Finset V, D.card ≤ 4 → ¬ Dominating T D := no_dom_le_four T ht h4 hasS4
  obtain ⟨v, hv⟩ := exists_indeg_23_le T ht hS4 (by omega) hle
  have hreg := core_regular T ht hS4 v hv
  have hdbl : ∀ h ∈ dom1 T v, ∀ c ∈ (dom1 T v).filter (fun u => T u h),
      (dom3 T v h c).card = 5 := fun h hh => core_doubly T ht hS4 v hv h hh
  have hs3 := core_hasS3 T ht hasS4 v
  obtain ⟨hbad, hcap⟩ := hExt v hv hreg hdbl hs3
  have hcov := badCount_le_sum T ht hasS4 v
  have hout := outside_card_eq T ht v hv
  have hsum : ∑ x ∈ outside T v, repairCount T (dom1 T v) x ≤ (outside T v).card * 66 := by
    calc ∑ x ∈ outside T v, repairCount T (dom1 T v) x
        ≤ ∑ _x ∈ outside T v, 66 :=
          Finset.sum_le_sum (fun x hx => hcap x hx
            (fun h hh => mask_admissible T ht hS4 v hv x hx h hh))
      _ = (outside T v).card * 66 := by rw [Finset.sum_const, smul_eq_mul]
  omega


/-! ## JOB 3 - ISOMORPHISM TRANSPORT

The real core H is only ISOMORPHIC to a catalogue row, never literally equal to it.
Sampling a few relabelings is evidence, not a theorem. These are the theorems. -/

section Transport

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (U : W → W → Prop) [DecidableRel U]
variable (e : V ≃ W) (he : ∀ a b : V, U (e a) (e b) ↔ T a b)

theorem mem_badSets_iff (H s : Finset V) :
    s ∈ badSets T H ↔ (s ⊆ H ∧ s.card = 4 ∧ ∀ u ∈ H, u ∉ s → ¬ ∀ w ∈ s, T u w) := by
  simp only [badSets, Finset.mem_filter, Finset.mem_powersetCard]
  tauto

theorem image_symm_eq (t : Finset W) : (t.image e.symm).image e = t := by
  rw [Finset.image_image]; simp

theorem image_symm_sub (H : Finset V) (t : Finset W) (hsub : t ⊆ H.image e) :
    t.image e.symm ⊆ H := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨c, hc, hce⟩ := Finset.mem_image.mp (hsub hb)
  rw [← hce]; simpa using hc

include he

theorem hasS3_transport (H : Finset V)
    (h : ∀ s : Finset V, s ⊆ H → s.card = 3 → ∃ u ∈ H, u ∉ s ∧ ∀ w ∈ s, T u w) :
    ∀ t : Finset W, t ⊆ H.image e → t.card = 3 →
      ∃ u ∈ H.image e, u ∉ t ∧ ∀ w ∈ t, U u w := by
  intro t hsub hcard
  have hc3 : (t.image e.symm).card = 3 := by
    rwa [Finset.card_image_of_injective _ e.symm.injective]
  obtain ⟨u, huH, hus, hud⟩ := h (t.image e.symm) (image_symm_sub e H t hsub) hc3
  refine ⟨e u, Finset.mem_image_of_mem _ huH, ?_, ?_⟩
  · intro hc
    exact hus (by simpa using Finset.mem_image_of_mem e.symm hc)
  · intro w hw
    have hw2 : e.symm w ∈ t.image e.symm := Finset.mem_image_of_mem _ hw
    have hres := (he u (e.symm w)).mpr (hud _ hw2)
    simpa using hres

theorem badSets_image (H : Finset V) :
    badSets U (H.image e) = (badSets T H).image (fun s => s.image e) := by
  ext t
  rw [mem_badSets_iff, Finset.mem_image]
  constructor
  · rintro ⟨hsub, hcard, hdom⟩
    refine ⟨t.image e.symm, ?_, image_symm_eq e t⟩
    rw [mem_badSets_iff]
    refine ⟨image_symm_sub e H t hsub, ?_, ?_⟩
    · rwa [Finset.card_image_of_injective _ e.symm.injective]
    · intro u huH hus hall
      refine hdom (e u) (Finset.mem_image_of_mem _ huH) ?_ ?_
      · intro hc
        exact hus (by simpa using Finset.mem_image_of_mem e.symm hc)
      · intro w hw
        have hw2 := hall (e.symm w) (Finset.mem_image_of_mem _ hw)
        have h2 := (he u (e.symm w)).mpr hw2
        simpa using h2
  · rintro ⟨s, hs, rfl⟩
    rw [mem_badSets_iff] at hs
    obtain ⟨hsub, hcard, hdom⟩ := hs
    refine ⟨Finset.image_subset_image hsub, ?_, ?_⟩
    · rwa [Finset.card_image_of_injective _ e.injective]
    · intro u huH hus hall
      obtain ⟨a, haH, rfl⟩ := Finset.mem_image.mp huH
      refine hdom a haH (fun hc => hus (Finset.mem_image_of_mem _ hc)) ?_
      intro w hw
      exact (he a w).mp (hall (e w) (Finset.mem_image_of_mem _ hw))

theorem badSets_card_transport (H : Finset V) :
    (badSets U (H.image e)).card = (badSets T H).card := by
  rw [badSets_image T U e he H,
    Finset.card_image_of_injective _ (Finset.image_injective e.injective)]

theorem maskOf_transport (H : Finset V) (x : V) :
    maskOf U (H.image e) (e x) = (maskOf T H x).image e := by
  ext b
  simp only [maskOf, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, haH, rfl⟩, hxb⟩
    exact ⟨a, ⟨haH, (he x a).mp hxb⟩, rfl⟩
  · rintro ⟨a, ⟨haH, hxa⟩, rfl⟩
    exact ⟨⟨a, haH, rfl⟩, (he x a).mpr hxa⟩

theorem admissible_transport (H : Finset V) (x h : V) :
    (((H.image e).filter (fun u => U u (e h))).filter (fun u => U (e x) u)).card
      = ((H.filter (fun u => T u h)).filter (fun u => T x u)).card := by
  have himg : ((H.image e).filter (fun u => U u (e h))).filter (fun u => U (e x) u)
      = ((H.filter (fun u => T u h)).filter (fun u => T x u)).image e := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨a, haH, rfl⟩, hah⟩, hxa⟩
      exact ⟨a, ⟨⟨haH, (he a h).mp hah⟩, (he x a).mp hxa⟩, rfl⟩
    · rintro ⟨a, ⟨⟨haH, hah⟩, hxa⟩, rfl⟩
      exact ⟨⟨⟨a, haH, rfl⟩, (he a h).mpr hah⟩, (he x a).mpr hxa⟩
  rw [himg, Finset.card_image_of_injective _ e.injective]

theorem repairCount_transport (H : Finset V) (x : V) :
    repairCount U (H.image e) (e x) = repairCount T H x := by
  unfold repairCount
  rw [badSets_image T U e he H, maskOf_transport T U e he H x]
  have himg : ((badSets T H).image (fun s => s.image e)).filter
        (fun t => t ⊆ (maskOf T H x).image e)
      = ((badSets T H).filter (fun s => s ⊆ maskOf T H x)).image (fun s => s.image e) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, hts⟩
      exact ⟨s, ⟨hs, (Finset.image_subset_image_iff e.injective).mp hts⟩, rfl⟩
    · rintro ⟨s, ⟨hs, hsm⟩, rfl⟩
      exact ⟨⟨s, hs, rfl⟩, Finset.image_subset_image hsm⟩
  rw [himg, Finset.card_image_of_injective _ (Finset.image_injective e.injective)]

end Transport

end F4
