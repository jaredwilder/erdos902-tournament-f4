"""Independent positive control: Paley P67 has S4; P67 minus any vertex fails S4 in 330 four-sets."""
from itertools import combinations
N=67
QR={x*x%N for x in range(1,N)}
assert len(QR)==33
IN=[sum(1<<v for v in range(N) if v!=u and (v-u)%N in QR) for u in range(N)]
counts={}
for comb in combinations(range(N),4):
    m=(1<<N)-1
    for v in comb: m &= IN[v]
    counts[m.bit_count()]=counts.get(m.bit_count(),0)+1
assert sum(counts.values())==766480
assert counts.get(0,0)==0
del0=0
for quad in combinations(range(1,67),4):
    m=IN[quad[0]]&IN[quad[1]]&IN[quad[2]]&IN[quad[3]]
    if m == 1: del0+=1
assert del0==330
print('P67 S4 PASS, full 4set distribution:',counts,'\nP66 from deletion: bad4=',del0)
