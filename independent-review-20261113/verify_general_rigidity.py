"""Standard-library crosschecks for the general DRT quadratic mask identity.
Exhaustive subsets for Paley n=7,11,19 and 10,000 samples + all extremal
masks for Paley n=23. Computational tests supplement, not replace, the proof.
"""
from random import Random
import json

def check(p, exhaustive):
    t=(p-3)//4
    residues={i*i%p for i in range(1,p)}
    if len(residues)!=(p-1)//2:raise AssertionError("not Paley")
    inn=[0]*p;out=[0]*p
    for a in range(p):
        for b in range(p):
            if a!=b and (b-a)%p in residues:
                out[a]|=1<<b;inn[b]|=1<<a
    for a in range(p):
        assert out[a].bit_count()==2*t+1
        for b in range(a+1,p):
            assert (out[a]&out[b]).bit_count()==t
    rng=Random(p*7717)
    cases=range(1<<p) if exhaustive else (
        [rng.getrandbits(p) for _ in range(10000)] +
        [out[a]|(1<<a) for a in range(p)]
    )
    n=0;extremals=[]
    for w in cases:
        size=w.bit_count()
        counts=[(w&inn[x]).bit_count() for x in range(p)]
        assert sum(a*(t+1-a) for a in counts)==t*size*(2*t+2-size)
        admissible=all(a<=t+1 for a in counts)
        assert not(admissible and size>2*t+2)
        if admissible and size==2*t+2:
            witnesses=[a for a in range(p) if w==(out[a]|(1<<a))]
            assert len(witnesses)==1
            extremals.append(w)
        n+=1
    if exhaustive:assert len(extremals)==p
    else:assert len(set(extremals))==p
    return {'p':p,'t':t,'subsets_checked':n,
            'extremal_admissible':len(extremals),'distinct_extremal':len(set(extremals))}

if __name__=='__main__':
    v=[check(p,p<=19) for p in (7,11,19,23)]
    print(json.dumps({'verdict':'PASS','paley_controls':v},indent=2))
