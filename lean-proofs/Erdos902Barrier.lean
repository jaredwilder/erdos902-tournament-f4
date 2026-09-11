/-
Erdos 902 — THE BARRIER ENGINE, formalised.

The measured fact: the union bound, both local-lemma forms and Shearer's optimum all land on
ln 2 * n^2 * 2^n. They differ only in a constant that decays to 1.

WHY they must. A sharper criterion buys a multiplicative slack G in the existence condition. But
the failure probability of a fixed n-set is q^(N-n) with q = 1 - 2^(-n), so buying slack G moves
the threshold by only

    Delta  =  log G / (-log q)   <=   2^n * log G.

For every criterion in the family log G = O(n), so Delta = O(n * 2^n) — one order BELOW the
n^2 * 2^n threshold itself. The factor of n cannot be reached this way.

This file proves that shift bound. It certifies the ENGINE of the barrier, not the asymptotics of
the threshold: the statement below is exactly "slack G moves the threshold by at most log G / x",
with x = 2^(-n).
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

/-- `-log (1 - x) ≥ x` on `[0,1)`: the one inequality the barrier rests on. -/
theorem neg_log_one_sub_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x ≤ -Real.log (1 - x) := by
  have hpos : (0:ℝ) < 1 - x := by linarith
  have := Real.log_le_sub_one_of_pos hpos
  linarith

/-- **The threshold-shift bound.**

`Δ` is how far a criterion may move the threshold when it buys multiplicative slack `G`.
It satisfies `Δ * (-log (1 - x)) = log G`, and is therefore at most `log G / x`.

With `x = 2^(-n)` this reads `Δ ≤ 2^n * log G`, which is the barrier: for every member of the
probabilistic family `log G = O(n)`, so `Δ = O(n 2^n)`, strictly below the `n^2 2^n` threshold. -/
theorem threshold_shift_le {x G Δ : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hG : 1 ≤ G)
    (hΔ : Δ * (-Real.log (1 - x)) = Real.log G) :
    Δ ≤ Real.log G / x := by
  have hlogG : 0 ≤ Real.log G := Real.log_nonneg hG
  have hkey : x ≤ -Real.log (1 - x) := neg_log_one_sub_ge (le_of_lt hx0) hx1
  have hLpos : 0 < -Real.log (1 - x) := lt_of_lt_of_le hx0 hkey
  -- Δ ≥ 0, since Δ * positive = nonneg
  have hΔ0 : 0 ≤ Δ := by
    by_contra hneg
    push_neg at hneg
    have : Δ * (-Real.log (1 - x)) < 0 := mul_neg_of_neg_of_pos hneg hLpos
    rw [hΔ] at this
    linarith
  rw [le_div_iff₀ hx0]
  calc Δ * x ≤ Δ * (-Real.log (1 - x)) := by
        exact mul_le_mul_of_nonneg_left hkey hΔ0
    _ = Real.log G := hΔ

/-- Specialised to the tournament setting: `x = 1/2^n`, so the shift is at most `2^n * log G`.

`n > 0` is required and is not a technicality: at `n = 0` we have `2^0 = 1`, the probability `x`
equals 1, and `log (1 - x)` is undefined — the statement is simply false there. -/
theorem threshold_shift_tournament {G Δ : ℝ} (n : ℕ) (hn : 0 < n) (hG : 1 ≤ G)
    (hΔ : Δ * (-Real.log (1 - 1 / (2:ℝ) ^ n)) = Real.log G) :
    Δ ≤ (2:ℝ) ^ n * Real.log G := by
  have h2pos : (0:ℝ) < (2:ℝ) ^ n := by positivity
  have h2n : (1:ℝ) < (2:ℝ) ^ n := by
    have hstep : (2:ℝ) ^ 1 ≤ (2:ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
    have hstep' : (2:ℝ) ≤ (2:ℝ) ^ n := by simpa using hstep
    linarith
  have hx0 : (0:ℝ) < 1 / (2:ℝ) ^ n := by positivity
  have hx1 : 1 / (2:ℝ) ^ n < 1 := by
    rw [div_lt_one h2pos]; exact h2n
  have h := threshold_shift_le hx0 hx1 hG hΔ
  have hrw : Real.log G / (1 / (2:ℝ) ^ n) = (2:ℝ) ^ n * Real.log G := by
    field_simp
  rwa [hrw] at h

#print axioms neg_log_one_sub_ge
#print axioms threshold_shift_le
#print axioms threshold_shift_tournament
