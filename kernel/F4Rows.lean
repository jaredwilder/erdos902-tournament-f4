/-!
# ERDOS 902 - THE FINITE LAYER, PURE KERNEL (no `native_decide`).

Rows 35 and 36 of the McKay/Spence DRT(23,11,5) catalogue - the only two of the
37 classes that carry S3 - re-verified by the LEAN KERNEL ITSELF: tournament
axioms, out-degree 11, every ordered pair with exactly 5 common out-neighbours,
S3, and the exact bad-4-set counts 2475 and 2530.

⭐ WHY THIS FILE EXISTS. The estate's `oracle/frontier_formalizer/press/f4_finite.lean`
already had these facts, but by `native_decide`, which puts the Lean COMPILER in
the trusted base (axiom footprint gains `Lean.ofReduceBool`). Everything here is
plain `decide`: the footprints are empty, so the counts 2475 / 2530 that the
whole f(4) >= 49 contradiction rests on are now kernel facts at row-1 trust.

Provenance: catalogue SHA-256
`20dbad06e128f968e87ce5bec9ca3128b8d2e9a9f25152b29d82c48c967b45d0`
(McKay, `users.cecs.anu.edu.au/~bdm/data/digraphs.html`), upper-triangle
row-major decode, one-indexed rows 35/36 = zero-indexed lines 34/35. The decode
was re-run independently for this file and agrees byte-for-byte with the decode
embedded in `f4_finite.lean` and with `verify_real_002.py`.

⛔ WHAT THIS FILE DOES NOT DO. It does not prove COMPLETENESS of the 37-class
catalogue - that is McKay/Spence's published census, cited, never encoded here
as proved. It also does not contain the admissible-mask capacity sweep (the 66);
that is ~1.15M masks over a 2^23 subset-sum transform and is outside kernel
`decide` range. See `F4Seal.lean` for how both enter as explicit hypotheses.

## Kernel-cost notes (why the definitions look the way they do)

`decide` reduces in the kernel with no compiler, so the encodings avoid the two
blow-ups the `native_decide` version could afford:
* 4-sets are generated ONLY in increasing order (8855 masks, not 23^4 = 279841
  loop iterations), by nested `above` lists;
* domination is tested by walking the out-mask list `t` directly rather than by
  indexing it 23 times per test (`covered` is 23 GMP-accelerated `Nat` ops).
A vertex inside `s` can never dominate `s` (its own bit is 0 in its out-mask, and
`isTournament` below is what certifies that), so `covered` needs no
"outside `s`" guard - it agrees with `verify_real_002.py`'s
`I[a]&I[b]&I[c]&I[d] == 0` test exactly.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace Erdos902F4Rows

/-- catalogue row 35 (one-indexed): out-neighbour mask of each of the 23 vertices. -/
def row35 : List Nat :=
  [4094, 258172, 7674200, 3901232, 5860064, 5152324, 6483336, 7643694, 2939058,
   3700038, 5185942, 1529482, 1877209, 1984813, 6886573, 2453013, 2503649,
   5297045, 6963803, 3377351, 4572515, 5389363, 637707]

/-- catalogue row 36 (one-indexed). -/
def row36 : List Nat :=
  [4094, 258172, 8062168, 6728160, 5847848, 6872644, 1560336, 3953010, 3089958,
   3512462, 5038746, 5404038, 1877325, 5587685, 6689565, 2714005, 941225,
   3192497, 5933111, 3304011, 6407467, 4537427, 758723]

/-- the 23 vertex labels. -/
def rng : List Nat := List.range 23

/-- the labels strictly above `a`. -/
def above (a : Nat) : List Nat := rng.filter (fun x => decide (a < x))

/-- flatten, hand-rolled from `foldr` and `++` only. -/
def cat (l : List (List Nat)) : List Nat := l.foldr (fun x acc => x ++ acc) []

/-- bit `v` of `m`. -/
def bit (m v : Nat) : Bool := (m >>> v) % 2 == 1

/-- self-contained 23-bit popcount. -/
def popc (m : Nat) : Nat := ((List.range 23).filter (fun j => bit m j)).length

/-- vertex `v`'s out-neighbour mask. -/
def outM (t : List Nat) (v : Nat) : Nat := t.getD v 0

/-- all 1771 three-element subsets of the 23 vertices, as masks. -/
def triples : List Nat :=
  cat (rng.map (fun a =>
    cat ((above a).map (fun b =>
      (above b).map (fun c => (1 <<< a) ||| (1 <<< b) ||| (1 <<< c))))))

/-- all 8855 four-element subsets of the 23 vertices, as masks. -/
def quads : List Nat :=
  cat (rng.map (fun a =>
    cat ((above a).map (fun b =>
      cat ((above b).map (fun c =>
        (above c).map (fun d =>
          (1 <<< a) ||| (1 <<< b) ||| (1 <<< c) ||| (1 <<< d))))))))

/-- some vertex of the core beats every member of the set `s`. -/
def covered (t : List Nat) (s : Nat) : Bool := t.any (fun m => (m &&& s) == s)

/-- tournament: irreflexive, and exactly one of `i -> j`, `j -> i` for `i != j`. -/
def isTournament (t : List Nat) : Bool :=
  rng.all fun i =>
    rng.all fun j =>
      if i == j then !(bit (outM t i) j)
      else (bit (outM t i) j != bit (outM t j) i)

/-- out-degree 11 at every vertex. -/
def isRegular11 (t : List Nat) : Bool := t.all (fun m => popc m == 11)

/-- every ordered pair of distinct vertices has exactly 5 common out-neighbours. -/
def isDoublyRegular5 (t : List Nat) : Bool :=
  rng.all fun i =>
    rng.all fun j =>
      (i == j) || (popc ((outM t i) &&& (outM t j)) == 5)

/-- S3: every 3-set is dominated by some vertex. -/
def hasS3 (t : List Nat) : Bool := triples.all (fun s => covered t s)

/-- the number of 4-sets with no dominator inside the core. -/
def badCount (t : List Nat) : Nat := (quads.filter (fun s => !(covered t s))).length

/-- sanity anchors for the generators themselves: the kernel checks that
`triples` and `quads` really are the C(23,3) and C(23,4) families. -/
theorem triples_card : triples.length = 1771 := by decide

theorem quads_card : quads.length = 8855 := by decide

theorem row35_tournament : isTournament row35 = true := by decide

theorem row36_tournament : isTournament row36 = true := by decide

theorem row35_regular11 : isRegular11 row35 = true := by decide

theorem row36_regular11 : isRegular11 row36 = true := by decide

theorem row35_doubly_regular : isDoublyRegular5 row35 = true := by decide

theorem row36_doubly_regular : isDoublyRegular5 row36 = true := by decide

theorem row35_s3 : hasS3 row35 = true := by decide

theorem row36_s3 : hasS3 row36 = true := by decide

/-- ⭐ THE 2475 - kernel-decided, no compiler in the trusted base. -/
theorem row35_bad4 : badCount row35 = 2475 := by decide

/-- ⭐ THE 2530 - kernel-decided. -/
theorem row36_bad4 : badCount row36 = 2530 := by decide

/-- ⭐ THE BAD FLOOR the contradiction actually uses. -/
theorem bad_floor : 2475 ≤ badCount row35 ∧ 2475 ≤ badCount row36 := by decide

end Erdos902F4Rows
