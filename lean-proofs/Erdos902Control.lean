/-
Erdos 902 -- KNOWN-ANSWER CONTROL for Erdos902ClosedForm.lean.

A lower bound theorem proves nothing if its hypothesis is unsatisfiable.  This file exhibits
the two extremal tournaments the literature pins and checks them AGAINST THE DEFINITION used
in the closed-form theorem, by kernel evaluation (`decide`), not by assertion:

  * the 3-cycle       satisfies S_1 on 3 vertices  -> with the bound, f(1) = 3
  * the Paley digraph satisfies S_2 on 7 vertices  -> with the bound, f(2) = 7

Both agree with Erdos / Szekeres-Szekeres.  If `HasSle` were mis-stated, these would fail.
`decide` is used, never `native_decide`: the axiom list must stay clean.
-/
import Erdos902ClosedForm
import Mathlib.Data.Fintype.Powerset

/-! ### f(1) = 3 : the 3-cycle -/

/-- The 3-cycle tournament: `a` beats `a+1`. -/
def cyc3 : Fin 3 → Fin 3 → Prop := fun a b => b = a + 1

instance : DecidableRel cyc3 := fun a b => inferInstanceAs (Decidable (b = a + 1))

theorem cyc3_isTournament : IsTournament cyc3 where
  irrefl := by decide
  total := by decide
  asymm := by decide

theorem cyc3_hasS1 : HasSle cyc3 1 := by unfold HasSle; decide

theorem schutteAt_one_three : SchutteAt 1 3 := ⟨cyc3, inferInstance, cyc3_isTournament, cyc3_hasS1⟩

/-- **f(1) = 3.**  Lower bound from the closed form, upper bound from the 3-cycle. -/
theorem f_one_eq_three : (∀ m, SchutteAt 1 m → 3 ≤ m) ∧ SchutteAt 1 3 :=
  ⟨fun m h => by simpa using schutte_card_bound 1 m h, schutteAt_one_three⟩

/-! ### f(2) = 7 : the Paley tournament on 7 points -/

/-- Paley tournament on `Fin 7`: `a` beats `b` iff `b - a` is a nonzero quadratic residue
mod 7, i.e. lies in `{1, 2, 4}`. -/
def paley7 : Fin 7 → Fin 7 → Prop := fun a b => b - a = 1 ∨ b - a = 2 ∨ b - a = 4

instance : DecidableRel paley7 := fun a b =>
  inferInstanceAs (Decidable (b - a = 1 ∨ b - a = 2 ∨ b - a = 4))

theorem paley7_isTournament : IsTournament paley7 where
  irrefl := by decide
  total := by decide
  asymm := by decide

set_option maxRecDepth 100000 in
theorem paley7_hasS2 : HasSle paley7 2 := by unfold HasSle; decide

theorem schutteAt_two_seven : SchutteAt 2 7 :=
  ⟨paley7, inferInstance, paley7_isTournament, paley7_hasS2⟩

/-- **f(2) = 7.**  Lower bound from the closed form, upper bound from the Paley tournament. -/
theorem f_two_eq_seven : (∀ m, SchutteAt 2 m → 7 ≤ m) ∧ SchutteAt 2 7 :=
  ⟨fun m h => by simpa using schutte_card_bound 2 m h, schutteAt_two_seven⟩

#print axioms f_one_eq_three
#print axioms f_two_eq_seven

/-! ### NEGATIVE controls: the definition must also say NO.

If `HasSle` were vacuously satisfiable the positive results above would be worthless.
The 3-cycle does NOT have S_2 (f(2) = 7 > 3), and the Paley tournament does NOT have S_3
(f(3) = 19 > 7).  Both refutations are kernel-checked. -/

set_option maxRecDepth 100000 in
theorem cyc3_not_hasS2 : ¬ HasSle cyc3 2 := by unfold HasSle; decide

set_option maxRecDepth 1000000 in
theorem paley7_not_hasS3 : ¬ HasSle paley7 3 := by unfold HasSle; decide

#print axioms cyc3_not_hasS2
#print axioms paley7_not_hasS3
