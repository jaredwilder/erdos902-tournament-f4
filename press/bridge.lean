import Mathlib

/-!
THE BRIDGE. 2026-08-31, deeper into the night.

External audit, verbatim: "CAPACITY is named, but its semantics are not yet proved... Do that
bridge and the metaphor really dies." This file proves the interpreter:

  continuation_le_capacity : EVERY legal continuation's reciprocal mass is <= Capacity.

and its corollaries: negative slack means NO completion exists (DEATH as a law), and a first
word of 3 or more is impossible in any legal utterance from a clean start.
-/

namespace Speaker

/-- Capacity, as sealed in speaker_demo.lean. -/
def Capacity (k : ℕ) (S : ℕ) : ℚ :=
  2 * (1 - (1 : ℚ) / 2 ^ k) / (S + 1)

/-- A legal continuation after accumulated ordinary mass S: each word strictly exceeds the
    mass of everything before it (the superincreasing grammar), recursively. -/
def LegalCont (S : ℕ) : List ℕ → Prop
  | [] => True
  | w :: ws => S < w ∧ LegalCont (S + w) ws

/-- Reciprocal mass of an utterance. -/
def rmass (l : List ℕ) : ℚ :=
  (l.map (fun a => (1 : ℚ) / a)).sum

@[simp] theorem rmass_nil : rmass [] = 0 := rfl

@[simp] theorem rmass_cons (w : ℕ) (ws : List ℕ) :
    rmass (w :: ws) = 1 / w + rmass ws := by
  simp [rmass]

/-- Capacity is antitone in the accumulated mass: more already said, less can follow. -/
theorem capacity_anti (k : ℕ) {S T : ℕ} (h : S ≤ T) :
    Capacity k T ≤ Capacity k S := by
  unfold Capacity
  have hnum : (0 : ℚ) ≤ 2 * (1 - 1 / 2 ^ k) := by
    have : (1 : ℚ) / 2 ^ k ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num)
    linarith
  have hST : (S : ℚ) + 1 ≤ (T : ℚ) + 1 := by
    have : (S : ℚ) ≤ T := by exact_mod_cast h
    linarith
  gcongr

/-- ⭐ THE BRIDGE THEOREM. Every legal k-word continuation after mass S carries reciprocal
    mass at most Capacity k S. This is the statement that makes CAPACITY semantics, not a
    name: the speaker's bound on its own unfinished speech, certified for ALL futures. -/
theorem continuation_le_capacity :
    ∀ (ws : List ℕ) (S : ℕ), LegalCont S ws → rmass ws ≤ Capacity ws.length S := by
  intro ws
  induction ws with
  | nil =>
      intro S _
      simp [Capacity]
  | cons w ws ih =>
      intro S h
      obtain ⟨hw, hrest⟩ := h
      have hS1 : S + 1 ≤ w := hw
      have hw0 : (0 : ℚ) < w := by
        have : 0 < w := Nat.lt_of_lt_of_le (Nat.zero_lt_succ S) hS1
        exact_mod_cast this
      -- the head contributes at most 1/(S+1)
      have hhead : (1 : ℚ) / w ≤ 1 / (S + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast hS1
      -- the tail continues after mass S + w >= 2S + 1, so its capacity shrinks
      have htail : rmass ws ≤ Capacity ws.length (S + w) := ih (S + w) hrest
      have hmono : Capacity ws.length (S + w) ≤ Capacity ws.length (2 * S + 1) := by
        apply capacity_anti
        omega
      -- and Capacity k (2S+1) = (1 - 2^-k)/(S+1), half the numerator scale
      have hval : Capacity ws.length (2 * S + 1) = (1 - (1 : ℚ) / 2 ^ ws.length) / (S + 1) := by
        unfold Capacity
        have hd : ((2 * S + 1 : ℕ) : ℚ) + 1 = 2 * ((S : ℚ) + 1) := by push_cast; ring
        rw [hd]
        have hS : (0 : ℚ) < (S : ℚ) + 1 := by positivity
        field_simp
      rw [List.length_cons]
      have goal_eq : Capacity (ws.length + 1) S
          = 1 / (S + 1) + (1 - (1 : ℚ) / 2 ^ ws.length) / (S + 1) := by
        unfold Capacity
        have h2 : (2 : ℚ) ^ (ws.length + 1) = 2 * 2 ^ ws.length := by ring
        rw [h2]
        have hp : (0 : ℚ) < 2 ^ ws.length := by positivity
        field_simp
        ring
      rw [rmass_cons, goal_eq]
      have := hmono.trans_eq hval
      linarith [hhead, htail.trans this]

/-- ⭐ DEATH IS A LAW. If the remaining meaning R exceeds capacity (negative slack), then NO
    legal continuation of that length can carry it. Not "search failed" - nonexistence. -/
theorem no_completion_of_neg_slack (k S : ℕ) (R : ℚ)
    (hdead : Capacity k S < R) :
    ∀ ws : List ℕ, LegalCont S ws → ws.length = k → rmass ws ≠ R := by
  intro ws hleg hlen hR
  have := continuation_le_capacity ws S hleg
  rw [hlen, hR] at this
  linarith

/-- ⭐ THE FIRST WORD IS FORCED, as a law about UTTERANCES: a legal utterance from a clean
    start (mass 0) that opens with a word of 3 or more can never carry reciprocal mass 1,
    whatever and however many its remaining words are. Combines the bridge with the
    first-token arithmetic sealed in speaker_demo. -/
theorem no_utterance_starts_at_three (m : ℕ) (hm : 3 ≤ m) (ws : List ℕ)
    (h : LegalCont 0 (m :: ws)) : rmass (m :: ws) ≠ 1 := by
  obtain ⟨_, hrest⟩ := h
  simp only [Nat.zero_add] at hrest
  have htail : rmass ws ≤ Capacity ws.length m := continuation_le_capacity ws m hrest
  have hm0 : (0 : ℚ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hcap : Capacity ws.length m ≤ 2 / (m + 1) := by
    unfold Capacity
    have hnum : 2 * (1 - (1 : ℚ) / 2 ^ ws.length) ≤ 2 := by
      have : (0 : ℚ) ≤ 1 / 2 ^ ws.length := by positivity
      linarith
    have hden : (0 : ℚ) < (m : ℚ) + 1 := by linarith
    gcongr
  -- 1/m + 2/(m+1) < 1 for m >= 3: the sealed arithmetic heart
  have hq : (3 : ℚ) ≤ m := by exact_mod_cast hm
  have hbound : (1 : ℚ) / m + 2 / (m + 1) < 1 := by
    have h1 : (0 : ℚ) < m + 1 := by linarith
    rw [div_add_div _ _ (ne_of_gt hm0) (ne_of_gt h1), div_lt_one (by positivity)]
    nlinarith
  intro habs
  rw [rmass_cons] at habs
  have : (1 : ℚ) ≤ 1 / m + 2 / (m + 1) := by
    have := htail.trans hcap
    linarith
  linarith

end Speaker
