import Mathlib

namespace F4P3

def row35 : List Nat := [4094, 258172, 7674200, 3901232, 5860064, 5152324, 6483336, 7643694, 2939058, 3700038, 5185942, 1529482, 1877209, 1984813, 6886573, 2453013, 2503649, 5297045, 6963803, 3377351, 4572515, 5389363, 637707]

def bitB (m v : Nat) : Bool := (m >>> v) % 2 == 1

def innArr : Array Nat := Id.run do
  let mut I := Array.replicate 23 0
  for i in List.range 23 do
    for j in List.range 23 do
      if bitB (row35.getD i 0) j then I := I.set! j (I[j]! ||| (1 <<< i))
  return I

def badArr : Array Nat := Id.run do
  let I := innArr
  let mut out : Array Nat := #[]
  for a in List.range 23 do
    for b in List.range 23 do
      if a < b then
        for c in List.range 23 do
          if b < c then
            for d in List.range 23 do
              if c < d then
                if I[a]! &&& I[b]! &&& I[c]! &&& I[d]! == 0 then
                  out := out.push ((1<<<a) ||| (1<<<b) ||| (1<<<c) ||| (1<<<d))
  return out

def popc (m : Nat) : Nat := ((List.range 23).filter (fun j => bitB m j)).length

def admB (I : Array Nat) (m : Nat) : Bool :=
  (List.range 23).all (fun h => popc (I[h]! &&& m) ≤ 6)

def repairB (bad : Array Nat) (m : Nat) : Nat := Id.run do
  let mut c := 0
  for b in bad do
    if b &&& m == b then c := c + 1
  return c

def badCountCheck : Nat := badArr.size

def capOK : Bool := Id.run do
  let I := innArr
  let bad := badArr
  let mut ok := true
  for m in [0:8388608] do
    if admB I m then
      if repairB bad m > 65 then ok := false
  return ok

theorem bad_size : badCountCheck = 2475 := by native_decide
theorem cap_ok : capOK = true := by native_decide

end F4P3
