import Mathlib
import F4Struct

open Finset

namespace F4Probe

def row35 : List Nat := [4094, 258172, 7674200, 3901232, 5860064, 5152324, 6483336, 7643694, 2939058, 3700038, 5185942, 1529482, 1877209, 1984813, 6886573, 2453013, 2503649, 5297045, 6963803, 3377351, 4572515, 5389363, 637707]

def R35 (a b : Fin 23) : Prop := ((row35.getD a.val 0) >>> b.val) % 2 = 1

instance : DecidableRel R35 := fun a b => by unfold R35; infer_instance

-- PROBE 1 : abstract badSets cardinality over Fin 23
set_option maxRecDepth 4000 in
theorem probe_bad : (F4.badSets R35 (univ : Finset (Fin 23))).card = 2475 := by native_decide

end F4Probe
