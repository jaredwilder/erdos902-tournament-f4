/-
Erdos 902 — THE THRESHOLD LAW, the half that makes the barrier rigorous.

`Erdos902Barrier.lean` proved the SHIFT bound: slack G moves the threshold by at most 2^n log G.
That says a sharper criterion cannot move the threshold much. It does not say where the threshold
IS. This file supplies the other side.

The union bound succeeds at N only if C(N,n) (1-x)^(N-n) < 1 with x = 2^(-n). Taking logs, that
forces

    n * log (N/n)  <  (N-n) * (x / (1-x)),

because log C(N,n) >= n log (N/n) and -log(1-x) <= x/(1-x). So N-n must exceed n log(N/n) (1-x)/x,
and with x = 2^(-n) that is N = Omega(n 2^n log(N/n)) — the n^2 2^n order the measurements show.

The two analytic facts are proved here. `neg_log_one_sub_le` is the exact companion of
`neg_log_one_sub_ge` in the barrier file: together they SANDWICH -log(1-x) between x and x/(1-x),
which is what pins the threshold from both sides.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Ring

open Real

/-- Upper companion to the barrier file's lower bound: `-log (1 - x) ≤ x / (1 - x)` on `[0,1)`.

    Proof: `log (1/(1-x)) = -log (1-x)` and `log y ≤ y - 1`, with `y = 1/(1-x)`, giving
    `-log (1-x) ≤ 1/(1-x) - 1 = x/(1-x)`. -/
theorem neg_log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) ≤ x / (1 - x) := by
  have hpos : (0:ℝ) < 1 - x := by linarith
  have hinv : (0:ℝ) < 1 / (1 - x) := by positivity
  have hlog : Real.log (1 / (1 - x)) ≤ 1 / (1 - x) - 1 := Real.log_le_sub_one_of_pos hinv
  have hrw : Real.log (1 / (1 - x)) = -Real.log (1 - x) := by
    rw [one_div, Real.log_inv]
  have harith : 1 / (1 - x) - 1 = x / (1 - x) := by
    field_simp
    ring
  rw [hrw, harith] at hlog
  exact hlog

/-- The sandwich, stated as one theorem: on `[0,1)`, `x ≤ -log (1-x) ≤ x/(1-x)`.

    The left half controls how far a sharper criterion can move the threshold (the barrier); the
    right half controls how large `N` must be for the criterion to hold at all. Together they pin
    the threshold's order from both directions. -/
theorem log_one_sub_sandwich {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x ≤ -Real.log (1 - x) ∧ -Real.log (1 - x) ≤ x / (1 - x) := by
  constructor
  · have hpos : (0:ℝ) < 1 - x := by linarith
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  · exact neg_log_one_sub_le hx0 hx1

/-- **The threshold necessity bound.**

    If the union-bound criterion holds at `N` — written here as `L < D * (-log (1 - x))`, where `L`
    is a lower bound on `log C(N,n)` and `D = N - n` — then `L < D * (x / (1 - x))`.

    Read with `L = n log (N/n)` and `x = 2^(-n)`: the number of absent vertices `D` must be at
    least `L (1-x)/x`, i.e. of order `n 2^n log (N/n)`. That is the lower side of the threshold,
    and it is what makes "the whole probabilistic family sits at n^2 2^n" a statement about the
    criterion rather than about a fitted curve. -/
theorem threshold_needs_many_vertices {x L D : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) (hD : 0 ≤ D)
    (hcrit : L < D * (-Real.log (1 - x))) :
    L < D * (x / (1 - x)) := by
  have hup : -Real.log (1 - x) ≤ x / (1 - x) := neg_log_one_sub_le hx0 hx1
  have : D * (-Real.log (1 - x)) ≤ D * (x / (1 - x)) := mul_le_mul_of_nonneg_left hup hD
  linarith

#print axioms neg_log_one_sub_le
#print axioms log_one_sub_sandwich
#print axioms threshold_needs_many_vertices
