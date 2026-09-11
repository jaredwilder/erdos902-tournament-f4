#!/usr/bin/env python3
from pathlib import Path
from itertools import combinations
from collections import defaultdict
import hashlib, json
import numpy as np

HERE=Path(__file__).resolve().parent

def parse(bits):
    out=[0]*23; k=0
    for i in range(23):
        for j in range(i+1,23):
            if bits[k]=='1': out[i]|=1<<j
            else: out[j]|=1<<i
            k+=1
    return out

def inn(out):
    I=[0]*23
    for i,row in enumerate(out):
        r=row
        while r:
            b=r & -r; r-=b
            j=b.bit_length()-1
            I[j]|=1<<i
    return I

def verify_drt(out):
    for i in range(23):
        if (out[i]>>i)&1 or out[i].bit_count()!=11: return False
        for j in range(i+1,23):
            if (((out[i]>>j)&1)+((out[j]>>i)&1))!=1: return False
            if (out[i]&out[j]).bit_count()!=5: return False
    return True

def has_s3(I):
    return all(I[a]&I[b]&I[c] for a,b,c in combinations(range(23),3))

def repair_zeta(I):
    N=1<<23
    a=np.zeros(N,dtype=np.uint16)
    for C in combinations(range(23),4):
        if I[C[0]]&I[C[1]]&I[C[2]]&I[C[3]]==0:
            a[sum(1<<x for x in C)]=1
    for i in range(23):
        s=1<<i
        v=a.reshape(-1,2*s)
        v[:,s:]+=v[:,:s]
    return a

def enumerate_admissible(I):
    affects=[[h for h in range(23) if (I[h]>>x)&1] for x in range(23)]
    counts=[0]*23; masks=[]
    def dfs(x,size,mask):
        if x==23:
            masks.append(mask); return
        dfs(x+1,size,mask)
        if size<12 and all(counts[h]<6 for h in affects[x]):
            for h in affects[x]: counts[h]+=1
            dfs(x+1,size+1,mask|(1<<x))
            for h in affects[x]: counts[h]-=1
    dfs(0,0,0)
    return masks

def profile(I):
    z=repair_zeta(I)
    masks=enumerate_admissible(I)
    best=[-1]*13; count=[0]*13; n=[0]*13
    for m in masks:
        s=m.bit_count(); r=int(z[m]); n[s]+=1
        if r>best[s]: best[s]=r; count[s]=1
        elif r==best[s]: count[s]+=1
    return {
      "admissible_total":len(masks),
      "profile":{str(s):{"admissible_count":n[s],"max_repair":best[s],"count_at_max":count[s]}
                 for s in range(13)},
      "global_max_repair":max(best)
    }

def main():
    raw=(HERE/"drtourn23.txt").read_bytes()
    rows=[x.strip() for x in raw.decode().splitlines() if x.strip()]
    assert len(rows)==37 and all(len(x)==253 for x in rows)

    decoded=[]
    survivors=[]
    for idx,b in enumerate(rows,1):
        O=parse(b); I=inn(O)
        assert verify_drt(O)
        decoded.append((O,I))
        if has_s3(I): survivors.append(idx)
    assert survivors==[35,36]

    cores={}
    for row in survivors:
        I=decoded[row-1][1]
        z=repair_zeta(I)
        bad4=int(z[(1<<23)-1])
        p=profile(I)
        p["bad4"]=bad4
        cores[str(row)]=p

    assert cores["35"]["bad4"]==2475
    assert cores["36"]["bad4"]==2530
    assert cores["35"]["global_max_repair"]==65
    assert cores["36"]["global_max_repair"]==66
    # Important top-layer anchors.
    assert cores["35"]["profile"]["12"]["admissible_count"]==23
    assert cores["35"]["profile"]["11"]["admissible_count"]==309
    assert cores["36"]["profile"]["12"]["admissible_count"]==23
    assert cores["36"]["profile"]["11"]["admissible_count"]==276

    CAP=66
    NEED=min(cores["35"]["bad4"],cores["36"]["bad4"])
    cap48=24*CAP
    cap49_23=25*CAP
    assert cap48==1584 < NEED
    assert cap49_23==1650 < NEED

    result={
      "catalogue_sha256":hashlib.sha256(raw).hexdigest(),
      "catalogue_rows":37,
      "S3_survivors":survivors,
      "cores":cores,
      "global_word":{"ADMISSIBLE_REPAIR_CAPACITY":CAP},
      "consequences":{
        "order48_total_repair_capacity":cap48,
        "minimum_core_need":NEED,
        "f4_ge_49_given_catalogue_completeness":True,
        "order49_indeg23_total_repair_capacity":cap49_23,
        "order49_indeg23_branch":"IMPOSSIBLE",
        "order49_if_S4":"24-regular"
      },
      "verdict":"PASS"
    }
    (HERE/"results.json").write_text(json.dumps(result,indent=2,sort_keys=True))
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=="__main__":
    main()
