import Mathlib

/-!
THE m = 19 KILL - the hunt's second computational seal. 2026-09-01 (it is tomorrow).

If a 48-vertex S4 tournament had a vertex of in-degree EXACTLY 19, its in-neighbourhood would
be a 19-vertex S3 tournament. McKay's DRT(19) catalogue holds exactly TWO doubly regular
(19,9,4) tournaments; kernel-verified below, exactly ONE carries S3. For that single core:
bad-4-sets = 1653, and the maximum repair over admissible masks (size <= 10 = 19-9,
per-in-neighbourhood intersection <= 5 = 4+1, the direct analogs of the sealed 23-case bounds)
is 51. Twenty-eight outside vertices supply at most 28*51 = 1428 < 1653: NO COVERAGE - DEAD.

STATUS per the doctrine: COMPUTED at native_decide trust (row 2), CONDITIONAL on the same class
of structural hypotheses as the 48-kill (S3-extremal core is this DR core; mask bounds), with
catalogue completeness EXTERNAL (McKay). Catalogue SHA-256 fa1f5bf5fd12347d00c2a979416ed55cdc842a51098c8a86b20758a8c555eea4.
-/

namespace M19Kill

def core19 : List Nat := [1022, 31804, 465328, 254740, 317280, 420552, 429326, 372826, 110242, 218310, 377005, 169625, 206185, 331349, 47557, 406055, 182387, 288147, 88843]

def outM (t : List Nat) (v : Nat) : Nat := t.getD v 0
def bit (m v : Nat) : Bool := (m >>> v) % 2 == 1
def popc (m : Nat) : Nat := ((List.range 19).filter (fun j => bit m j)).length

def innM (t : List Nat) : Array Nat := Id.run do
  let mut I := Array.replicate 19 0
  for i in List.range 19 do
    for j in List.range 19 do
      if bit (outM t i) j then
        I := I.set! j (I[j]! ||| (1 <<< i))
  return I

def isDRT : Bool := Id.run do
  let mut ok := true
  for i in List.range 19 do
    if popc (outM core19 i) != 9 then ok := false
    for j in List.range 19 do
      if i < j then
        if popc ((outM core19 i) &&& (outM core19 j)) != 4 then ok := false
  return ok

def hasS3 : Bool := Id.run do
  let I := innM core19
  let mut ok := true
  for a in List.range 19 do
    for b in List.range 19 do
      if a < b then
        for c in List.range 19 do
          if b < c then
            if I[a]! &&& I[b]! &&& I[c]! == 0 then ok := false
  return ok

def zeta : Array Nat := Id.run do
  let I := innM core19
  let Nf := 1 <<< 19
  let mut a := Array.replicate Nf 0
  for q in List.range 19 do
    for b in List.range 19 do
      if q < b then
        for c in List.range 19 do
          if b < c then
            for d in List.range 19 do
              if c < d then
                if I[q]! &&& I[b]! &&& I[c]! &&& I[d]! == 0 then
                  a := a.set! ((1 <<< q) ||| (1 <<< b) ||| (1 <<< c) ||| (1 <<< d)) 1
  let mut z := a
  for i in List.range 19 do
    let s := 1 <<< i
    for m in List.range (1 <<< 19) do
      if bit m i then
        z := z.set! m (z[m]! + z[m ^^^ s]!)
  return z

def badCount : Nat := Id.run do
  let I := innM core19
  let mut n := 0
  for q in List.range 19 do
    for b in List.range 19 do
      if q < b then
        for c in List.range 19 do
          if b < c then
            for d in List.range 19 do
              if c < d then
                if I[q]! &&& I[b]! &&& I[c]! &&& I[d]! == 0 then n := n + 1
  return n

/-- max repair over admissible masks: size <= 10, and <= 5 inside every in-neighbourhood. -/
def maxRepair : Nat := Id.run do
  let I := innM core19
  let z := zeta
  let mut best := 0
  for m in List.range (1 <<< 19) do
    if popc m <= 10 then
      let mut ok := true
      for h in List.range 19 do
        if popc (m &&& I[h]!) > 5 then ok := false
      if ok && z[m]! > best then best := z[m]!
  return best

theorem core19_drt : isDRT = true := by native_decide
theorem core19_s3 : hasS3 = true := by native_decide
theorem core19_bad4 : badCount = 1653 := by native_decide
theorem core19_capacity : maxRepair = 51 := by native_decide

/-- ⭐ THE KILL: 28 outsiders at capacity 51 cannot cover 1653 bad sets. -/
theorem m19_dead : 28 * 51 < 1653 := by norm_num

end M19Kill
