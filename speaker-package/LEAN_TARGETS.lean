/-
Targets to kernel-seal in the user's Lean fleet.

1. global finite capacity certificates for rows 35/36:
   every admissible mask of POP <= 12 repairs <= 65 / 66 bad four-sets.

2. no_order_48_from_global_capacity

3. f_four_ge_49 : 49 <= f 4

4. order49_no_indeg23

5. order49_regular
   (hT : IsTournament T)
   (hN : Fintype.card V = 49)
   (hS : HasSle T 4) :
   ∀ v : V, (inN T v).card = 24
-/
