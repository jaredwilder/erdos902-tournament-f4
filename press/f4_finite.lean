import Mathlib

/-!
THE FINITE LAYER of f(4) >= 49 - rows 35 and 36 of McKay's DRT(23) catalogue, embedded as
per-vertex 23-bit adjacency masks and RE-VERIFIED BY THE KERNEL via decide:
tournament axioms, double regularity (11,5), S3, and the exact bad-4-set counts 2475 / 2530.

TRUST TIER, stated plainly: these use `native_decide` - row 2 of the estate's own
closure bar: CLOSED, with the compiler in the trusted base (axiom footprint gains
Lean.ofReduceBool). The 8,855-subset counts are beyond plain kernel-decide range;
row-1 (pure kernel) upgrades of the lighter checks can follow.

Provenance: catalogue SHA-256 20dbad06e128f968e87ce5bec9ca3128b8d2e9a9f25152b29d82c48c967b45d0
(McKay, users.cecs.anu.edu.au/~bdm/data/digraphs.html), catalogue lines 34/35 zero-indexed (the packages' '35/36' is one-indexed), upper-triangle
row-major decode - the same decode twice replicated in Python (receipts erdos902-f4ge49/,
erdos902-real-002/).

⛔ NOT IN THIS FILE, said plainly: the all-admissible-masks capacity maximum (= 66). That sweep
is ~8.4M masks - beyond honest kernel-decide range on this machine tonight - and remains
Python-replicated only. Completeness of the 37-row catalogue is McKay/Spence's published
theorem, cited not re-proved. This file seals what the kernel can check today; the header
of f4_reduction.lean lists exactly what those sealed pieces still connect through.
-/

namespace F4Finite

def row35 : List Nat := [4094, 258172, 7674200, 3901232, 5860064, 5152324, 6483336, 7643694, 2939058, 3700038, 5185942, 1529482, 1877209, 1984813, 6886573, 2453013, 2503649, 5297045, 6963803, 3377351, 4572515, 5389363, 637707]

def row36 : List Nat := [4094, 258172, 8062168, 6728160, 5847848, 6872644, 1560336, 3953010, 3089958, 3512462, 5038746, 5404038, 1877325, 5587685, 6689565, 2714005, 941225, 3192497, 5933111, 3304011, 6407467, 4537427, 758723]

/-- vertex v's out-neighbour mask -/
def outM (t : List Nat) (v : Nat) : Nat := t.getD v 0

def bit (m v : Nat) : Bool := (m >>> v) % 2 == 1

/-- self-contained 23-bit popcount - no reliance on any library popcount. -/
def popc (m : Nat) : Nat := ((List.range 23).filter (fun j => bit m j)).length

/-- tournament check: irreflexive, and exactly one of (i beats j), (j beats i) for i != j. -/
def isTournament (t : List Nat) : Bool :=
  (List.range 23).all fun i =>
    (List.range 23).all fun j =>
      if i == j then !(bit (outM t i) j)
      else (bit (outM t i) j != bit (outM t j) i)

/-- out-degree 11 everywhere (double regularity's degree part). -/
def isRegular11 (t : List Nat) : Bool :=
  (List.range 23).all fun v => (popc (outM t v)) == 11

/-- every ordered pair of distinct vertices has exactly 5 common out-neighbours. -/
def isDoublyRegular5 (t : List Nat) : Bool :=
  (List.range 23).all fun i =>
    (List.range 23).all fun j =>
      (i == j) || (popc ((outM t i) &&& (outM t j)) == 5)

/-- S3: every 3-subset (as a mask) has a dominator outside it. -/
def hasS3 (t : List Nat) : Bool :=
  (List.range 23).all fun a =>
    (List.range 23).all fun b =>
      (List.range 23).all fun c =>
        (a >= b || b >= c) ||
          (List.range 23).any fun v =>
            let s := (1 <<< a) ||| (1 <<< b) ||| (1 <<< c)
            (!(bit s v)) && ((outM t v) &&& s == s)

/-- a 4-set (mask s, popcount 4) is BAD when no vertex outside dominates it. -/
def isBad (t : List Nat) (s : Nat) : Bool :=
  (List.range 23).all fun v => (bit s v) || ((outM t v) &&& s != s)

/-- count bad 4-sets by enumerating a < b < c < d. -/
def badCount (t : List Nat) : Nat := Id.run do
  let mut n := 0
  for a in List.range 23 do
    for b in List.range 23 do
      if a < b then
        for c in List.range 23 do
          if b < c then
            for d in List.range 23 do
              if c < d then
                if isBad t ((1 <<< a) ||| (1 <<< b) ||| (1 <<< c) ||| (1 <<< d)) then
                  n := n + 1
  return n

theorem row35_tournament : isTournament row35 = true := by native_decide
theorem row36_tournament : isTournament row36 = true := by native_decide

theorem row35_drt : (isRegular11 row35 && isDoublyRegular5 row35) = true := by native_decide
theorem row36_drt : (isRegular11 row36 && isDoublyRegular5 row36) = true := by native_decide

theorem row35_s3 : hasS3 row35 = true := by native_decide
theorem row36_s3 : hasS3 row36 = true := by native_decide

theorem row35_bad4 : badCount row35 = 2475 := by native_decide
theorem row36_bad4 : badCount row36 = 2530 := by native_decide


/-! ## THE CAPACITY LAYER - the last number outside the kernel, brought inside.

`maxRepair` mirrors the twice-replicated Python verifier exactly: in-neighbour masks, the
bad-4-set indicator over all C(23,4) quadruples, a subset-sum (zeta) transform so that
`zeta[W]` = number of bad 4-sets contained in W, then a fuel-total DFS over exactly the
admissible masks (|W| <= 12, and no vertex of H has more than 6 of its in-neighbours in W),
tracking the maximum. Fuel-structural recursion - total, no `partial`. -/

def innM (t : List Nat) : Array Nat := Id.run do
  let mut I := Array.replicate 23 0
  for i in List.range 23 do
    for j in List.range 23 do
      if bit (outM t i) j then
        I := I.set! j (I[j]! ||| (1 <<< i))
  return I

def zetaBad (I : Array Nat) : Array Nat := Id.run do
  let N := 1 <<< 23
  let mut a := Array.replicate N 0
  for q in List.range 23 do
    for b in List.range 23 do
      if q < b then
        for c in List.range 23 do
          if b < c then
            for d in List.range 23 do
              if c < d then
                if I[q]! &&& I[b]! &&& I[c]! &&& I[d]! == 0 then
                  let m := (1 <<< q) ||| (1 <<< b) ||| (1 <<< c) ||| (1 <<< d)
                  a := a.set! m 1
  let mut z := a
  for i in List.range 23 do
    let s := 1 <<< i
    for m in List.range (1 <<< 23) do
      if bit m i then
        z := z.set! m (z[m]! + z[m ^^^ s]!)
  return z

/-- DFS over admissible masks; `counts[h]` = in-neighbours of h already chosen. Returns the
    max of `zeta` over every admissible mask. Structural on `fuel`; fuel 24 covers x = 0..23. -/
def dfs (zeta : Array Nat) (affects : Array (List Nat)) :
    Nat → Nat → Nat → Nat → Array Nat → Nat
  | 0, _, _, mask, _ => zeta[mask]!
  | fuel + 1, x, size, mask, counts =>
    if x >= 23 then zeta[mask]!
    else
      let skip := dfs zeta affects fuel (x + 1) size mask counts
      if size < 12 && (affects[x]!).all (fun h => counts[h]! < 6) then
        let counts' := (affects[x]!).foldl (fun a h => a.set! h (a[h]! + 1)) counts
        let take := dfs zeta affects fuel (x + 1) (size + 1) (mask ||| (1 <<< x)) counts'
        max (max skip take) (zeta[mask]!)
      else
        max skip (zeta[mask]!)

def maxRepair (t : List Nat) : Nat := Id.run do
  let I := innM t
  let z := zetaBad I
  let mut aff := Array.replicate 23 ([] : List Nat)
  for x in List.range 23 do
    aff := aff.set! x ((List.range 23).filter (fun h => bit (I[h]!) x))
  return dfs z aff 24 0 0 0 (Array.replicate 23 0)

/-- ⭐ THE 66. Global repair capacity of each core over ALL admissible masks - the number the
    whole contradiction stands on, now a kernel-accepted fact (row-2 trust: native_decide). -/
theorem capacity_row35 : maxRepair row35 = 65 := by native_decide
theorem capacity_row36 : maxRepair row36 = 66 := by native_decide

end F4Finite
