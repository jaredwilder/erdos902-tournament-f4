"""Independent direct witness check, no subset-zeta or original DFS.

For the maximising capacity row #18, W={0,3,4,5,8,12,13,15,16,17,18}
satisfies all 23 admissibility constraints and contains exactly 85 internally
undominated 4-subsets (330 total 4-subsets of W).
"""
from itertools import combinations
from pathlib import Path
R=Path(__file__).with_name("drtourn23.txt").read_text().splitlines()
bits=R[17]
O=[0]*23;I=[0]*23;k=0
for a in range(23):
    for b in range(a+1,23):
        if bits[k]=="1":O[a]|=1<<b;I[b]|=1<<a
        else:O[b]|=1<<a;I[a]|=1<<b
        k+=1
w=504121
W=[i for i in range(23) if (w>>i)&1]
assert W==[0,3,4,5,8,12,13,15,16,17,18]
assert all((w&I[h]).bit_count()<=6 for h in range(23))
bad=[]
for quad in combinations(W,4):
    common=(1<<23)-1
    for a in quad:common&=I[a]
    if common==0:bad.append(quad)
assert len(bad)==85
print("EXTREMAL_WITNESS_PASS", "row=18", "mask=504121", "bad4=85", "total4=330")
