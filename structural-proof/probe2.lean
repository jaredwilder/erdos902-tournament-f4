import Mathlib
import F4Struct

open Finset

namespace F4Probe2

def row35 : List Nat := [4094, 258172, 7674200, 3901232, 5860064, 5152324, 6483336, 7643694, 2939058, 3700038, 5185942, 1529482, 1877209, 1984813, 6886573, 2453013, 2503649, 5297045, 6963803, 3377351, 4572515, 5389363, 637707]

def R35 (a b : Fin 23) : Prop := ((row35.getD a.val 0) >>> b.val) % 2 = 1
instance : DecidableRel R35 := fun a b => by unfold R35; infer_instance

def repairOf (W : Finset (Fin 23)) : Nat :=
  ((F4.badSets R35 (univ : Finset (Fin 23))).filter (fun s => s ⊆ W)).card

def Adm (W : Finset (Fin 23)) : Prop :=
  ∀ h : Fin 23, (((univ : Finset (Fin 23)).filter (fun u => R35 u h)) ∩ W).card ≤ 6

instance : DecidablePred Adm := fun W => by unfold Adm; infer_instance

-- PROBE 2 : the capacity bound, quantified over ALL subsets of Fin 23 (8.4M)
set_option maxRecDepth 10000 in
theorem probe_cap : ∀ W : Finset (Fin 23), Adm W → repairOf W ≤ 65 := by native_decide

end F4Probe2
