/-
Erdos 902 -- the ARITHMETIC TAIL of the Erdos existence bound, with an EXPLICIT witness.

The counting argument needs one number-theoretic fact: at `M` vertices,

    C(M,n) * (2^n - 1)^(M-n)  <  (2^n)^(M-n).

Everything here is elementary Nat arithmetic -- no analysis, no logarithms, no real numbers.
The chain is:  two terms of the binomial theorem  ->  `2 a^(a+1) <= (a+1)^(a+1)`  ->  a
factor of 2 gained per block of `q = 2^n` steps  ->  a polynomial is beaten by `2^w`.

⭐ THE WITNESS IS NAMED, NOT HIDDEN BEHIND `∃`.  `M0 n = n + 3 n^2 2^n`.

⛔ EARLIER THIS FILE PROVED A NEEDLESSLY WEAK BOUND, and the weakness was entirely in one
careless choice.  `w` has only one job -- to satisfy `M < 2^w` -- and it was set to `2 n 2^n`
when `3n` does the job.  That inflated the witness from `n + 3 n^2 2^n` to `n + 2 n^2 4^n`:
an entire factor of `2^n`, bought by nothing.  With `w = 3n` the same skeleton delivers the
classical Erdos [Er63c] upper bound `O(n^2 2^n)` with the explicit constant 3.
-/
import Mathlib

namespace Erdos902Arith

/-! ### The two-terms-of-binomial engine -/

/-- Two terms of the binomial theorem, in the only form needed. -/
theorem binom_two_terms (a : ℕ) : ∀ k : ℕ, a ^ (k + 1) + (k + 1) * a ^ k ≤ (a + 1) ^ (k + 1) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have expand : (a + 1) * (a ^ (k + 1) + (k + 1) * a ^ k)
          = (a ^ (k + 1 + 1) + (k + 1 + 1) * a ^ (k + 1)) + (k + 1) * a ^ k := by ring
      calc a ^ (k + 1 + 1) + (k + 1 + 1) * a ^ (k + 1)
          <= (a + 1) * (a ^ (k + 1) + (k + 1) * a ^ k) := by rw [expand]; exact Nat.le_add_right _ _
        _ <= (a + 1) * (a + 1) ^ (k + 1) := Nat.mul_le_mul_left _ ih
        _ = (a + 1) ^ (k + 1 + 1) := by ring

/-- **One factor of two per block.**  `(1 - 1/q)^q <= 1/2`, stated without division. -/
theorem two_mul_pow_le (a : ℕ) : 2 * a ^ (a + 1) <= (a + 1) ^ (a + 1) := by
  have h := binom_two_terms a a
  have hle : a ^ (a + 1) <= (a + 1) * a ^ a := by
    calc a ^ (a + 1) = a * a ^ a := by ring
      _ <= (a + 1) * a ^ a := Nat.mul_le_mul_right _ (Nat.le_succ a)
  omega

/-- The gain compounds: `u` blocks give a factor `2^u`. -/
theorem pow_block (a u : ℕ) : 2 ^ u * a ^ ((a + 1) * u) <= (a + 1) ^ ((a + 1) * u) := by
  have h : (2 * a ^ (a + 1)) ^ u <= ((a + 1) ^ (a + 1)) ^ u :=
    Nat.pow_le_pow_left (two_mul_pow_le a) u
  calc 2 ^ u * a ^ ((a + 1) * u) = (2 * a ^ (a + 1)) ^ u := by
        rw [Nat.mul_pow, ← Nat.pow_mul]
    _ <= ((a + 1) ^ (a + 1)) ^ u := h
    _ = (a + 1) ^ ((a + 1) * u) := by rw [← Nat.pow_mul]

/-! ### The explicit witness -/

/-- **The explicit vertex count.**  `M0 n = n + 3 n^2 2^n`. -/
def M0 (n : ℕ) : ℕ := n + 3 * n ^ 2 * 2 ^ n

theorem M0_sub (n : ℕ) : M0 n - n = 3 * n ^ 2 * 2 ^ n := by simp [M0]

/-- `M0 n < 2^(3n)`.  This is the whole reason `w = 3n` is admissible, and it is tight at
`n = 1`: `7 < 8`. -/
theorem M0_lt_pow (n : ℕ) (hn : 1 <= n) : M0 n < 8 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [M0]
  | succ n hn ih =>
      have h2 : (0:ℕ) < 2 ^ n := pow_pos (by norm_num) n
      have hA : 6 * (n + 1) ^ 2 <= 24 * n ^ 2 := by nlinarith [hn]
      have hB : n + 1 <= 8 * n := by omega
      have hC : 6 * (n + 1) ^ 2 * 2 ^ n <= 24 * n ^ 2 * 2 ^ n := Nat.mul_le_mul_right _ hA
      have hIH : M0 n < 8 ^ n := ih
      simp only [M0] at hIH ⊢
      calc (n + 1) + 3 * (n + 1) ^ 2 * 2 ^ (n + 1)
          = (n + 1) + 6 * (n + 1) ^ 2 * 2 ^ n := by ring
        _ <= 8 * n + 24 * n ^ 2 * 2 ^ n := Nat.add_le_add hB hC
        _ = 8 * (n + 3 * n ^ 2 * 2 ^ n) := by ring
        _ < 8 * 8 ^ n := by exact mul_lt_mul_of_pos_left hIH (by norm_num)
        _ = 8 ^ (n + 1) := by ring

theorem n_le_M0_sub (n : ℕ) (hn : 1 <= n) : n <= M0 n - n := by
  rw [M0_sub]
  have h1 : 1 <= 2 ^ n := Nat.one_le_two_pow
  nlinarith [hn]

/-- **THE ARITHMETIC THE COUNTING NEEDS, AT AN EXPLICIT `M`.**
`C(M0 n, n) * (2^n - 1)^(M0 n - n) < (2^n)^(M0 n - n)` -- the union bound coming in under 1. -/
theorem good_M0 (n : ℕ) (hn : 1 <= n) :
    (Nat.choose (M0 n) n) * (2 ^ n - 1) ^ (M0 n - n) < (2 ^ n) ^ (M0 n - n) := by
  -- write `2^n` as `a+1` so that no truncated subtraction survives
  obtain ⟨a, ha⟩ : ∃ a, 2 ^ n = a + 1 := ⟨2 ^ n - 1, by
    have : 1 <= 2 ^ n := Nat.one_le_two_pow
    omega⟩
  have ha1 : 1 <= a := by
    have h2 : 2 <= 2 ^ n := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ <= 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hAsub : 2 ^ n - 1 = a := by omega
  rw [M0_sub, hAsub]
  -- hide the exponent behind a local BEFORE rewriting the base: `rw [ha]` would otherwise
  -- rewrite the `2^n` sitting INSIDE the exponent too, and the calc would no longer match.
  set T := 3 * n ^ 2 * 2 ^ n with hT
  rw [ha]
  -- goal: C(M0 n, n) * a ^ T < (a+1) ^ T
  have htqu : T = (a + 1) * (n * (3 * n)) := by rw [hT, ← ha]; ring
  have hM : M0 n < 2 ^ (3 * n) := by
    have h8 : (2:ℕ) ^ (3 * n) = 8 ^ n := by rw [Nat.pow_mul]
    rw [h8]; exact M0_lt_pow n hn
  have hMn : (M0 n) ^ n < 2 ^ (n * (3 * n)) := by
    have h1 : (M0 n) ^ n < (2 ^ (3 * n)) ^ n := Nat.pow_lt_pow_left hM (by omega)
    calc (M0 n) ^ n < (2 ^ (3 * n)) ^ n := h1
      _ = 2 ^ ((3 * n) * n) := by rw [← Nat.pow_mul]
      _ = 2 ^ (n * (3 * n)) := by rw [Nat.mul_comm]
  have hblock : 2 ^ (n * (3 * n)) * a ^ T <= (a + 1) ^ T := by
    rw [htqu]; exact pow_block a (n * (3 * n))
  have hapos : 0 < a ^ T := pow_pos (by omega) _
  calc Nat.choose (M0 n) n * a ^ T
      <= (M0 n) ^ n * a ^ T := Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)
    _ < 2 ^ (n * (3 * n)) * a ^ T := mul_lt_mul_of_pos_right hMn hapos
    _ <= (a + 1) ^ T := hblock

/-- The existential form, kept so downstream users need not change. -/
theorem exists_good_M (n : ℕ) (hn : 1 <= n) :
    ∃ M : ℕ, n <= M ∧ n <= M - n ∧
      (Nat.choose M n) * (2 ^ n - 1) ^ (M - n) < (2 ^ n) ^ (M - n) :=
  ⟨M0 n, by simp [M0], n_le_M0_sub n hn, good_M0 n hn⟩

end Erdos902Arith
