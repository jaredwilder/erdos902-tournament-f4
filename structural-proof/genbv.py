import os
from itertools import combinations
HERE=os.environ["DROP"]; OUT=os.environ["SPD"]

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
            b=r&-r; r-=b; I[b.bit_length()-1]|=1<<i
    return I
def bits_of(m): return [i for i in range(23) if (m>>i)&1]

rows=[x.strip() for x in open(os.path.join(HERE,"drtourn23.txt"),encoding="utf-8").read().splitlines() if x.strip()]

def gen(rowidx, name, bound, thmname):
    O=parse(rows[rowidx-1]); I=inn(O)
    bad=[C for C in combinations(range(23),4) if I[C[0]]&I[C[1]]&I[C[2]]&I[C[3]]==0]
    terms=[ "ind12 (w.getLsbD %d && w.getLsbD %d && w.getLsbD %d && w.getLsbD %d)"%C for C in bad ]
    rep = "\n    + ".join(terms)
    conj=[]
    for h in range(23):
        mem=bits_of(I[h])
        ssum = " + ".join("ind6 (w.getLsbD %d)"%i for i in mem)
        conj.append("((%s).ule 6#6)"%ssum)
    admbody = "\n    && ".join(conj)
    L=[]
    L.append("def repair_%s (w : BitVec 23) : BitVec 12 :="%name)
    L.append("  " + rep)
    L.append("")
    L.append("def adm_%s (w : BitVec 23) : Bool :="%name)
    L.append("  " + admbody)
    L.append("")
    L.append("theorem %s : ∀ w : BitVec 23,"%thmname)
    L.append("    (!(adm_%s w) || (repair_%s w).ult %d#12) = true := by"%(name,name,bound))
    L.append("  intro w")
    L.append("  unfold adm_%s repair_%s ind12 ind6"%(name,name))
    L.append("  bv_decide")
    return "\n".join(L), len(bad)

hdr = "import Std.Tactic.BVDecide\n\nnamespace F4Cap\n\ndef ind12 (p : Bool) : BitVec 12 := if p then 1#12 else 0#12\ndef ind6 (p : Bool) : BitVec 6 := if p then 1#6 else 0#6\n\n"

b35,n35 = gen(35,"r35",67,"row35_no_67")
b36,n36 = gen(36,"r36",67,"row36_no_67")
open(os.path.join(OUT,"F4Cap35.lean"),"w",encoding="utf-8").write(hdr+b35+"\n\nend F4Cap\n")
open(os.path.join(OUT,"F4Cap36.lean"),"w",encoding="utf-8").write(hdr+b36+"\n\nend F4Cap\n")
# NEGATIVE CONTROL: row36 max is 66, so "< 66" must FAIL
bneg,_ = gen(36,"r36n",66,"row36_no_66_NEGCTRL")
open(os.path.join(OUT,"F4CapNeg.lean"),"w",encoding="utf-8").write(hdr+bneg+"\n\nend F4Cap\n")
print("row35 bad4=%d  row36 bad4=%d"%(n35,n36))
