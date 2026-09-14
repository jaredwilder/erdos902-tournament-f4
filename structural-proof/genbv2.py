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
def width(n): return max(1,(n).bit_length())
rows=[x.strip() for x in open(os.path.join(HERE,"drtourn23.txt"),encoding="utf-8").read().splitlines() if x.strip()]
def tree(exprs):
    cur=[(e,1) for e in exprs]
    while len(cur)>1:
        nxt=[]
        for i in range(0,len(cur)-1,2):
            (ea,ma),(eb,mb)=cur[i],cur[i+1]
            m=ma+mb; w=width(m)
            nxt.append(("(BitVec.setWidth %d %s + BitVec.setWidth %d %s)"%(w,ea,w,eb), m))
        if len(cur)%2==1: nxt.append(cur[-1])
        cur=nxt
    return cur[0]
def gen(rowidx,name,bound,thmname):
    O=parse(rows[rowidx-1]); I=inn(O)
    bad=[C for C in combinations(range(23),4) if I[C[0]]&I[C[1]]&I[C[2]]&I[C[3]]==0]
    leaves=["(BitVec.ofBool (w.getLsbD %d && w.getLsbD %d && w.getLsbD %d && w.getLsbD %d))"%C for C in bad]
    rep_expr,rep_max = tree(leaves); rw = width(rep_max)
    conj=[]
    for h in range(23):
        lv=["(BitVec.ofBool (w.getLsbD %d))"%i for i in bits_of(I[h])]
        e,mx = tree(lv); ww=width(mx)
        conj.append("((%s).ule 6#%d)"%(e,ww))
    L=[]
    L.append("def repair_%s (w : BitVec 23) : BitVec %d :="%(name,rw))
    L.append("  " + rep_expr); L.append("")
    L.append("def adm_%s (w : BitVec 23) : Bool :="%name)
    L.append("  " + "\n    && ".join(conj)); L.append("")
    L.append("theorem %s : ∀ w : BitVec 23,"%thmname)
    L.append("    (!(adm_%s w) || (repair_%s w).ult %d#%d) = true := by"%(name,name,bound,rw))
    L.append("  intro w")
    L.append("  unfold adm_%s repair_%s"%(name,name))
    L.append("  bv_decide (config := { timeout := 3600 })")
    return "\n".join(L), len(bad), rw
hdr="import Std.Tactic.BVDecide\n\nset_option maxRecDepth 4000000\nset_option maxHeartbeats 0\n\nnamespace F4CapT\n\n"
for idx,nm,bd,tn,fn in [(35,"r35",67,"row35_no_67","F4CapT35"),(36,"r36",67,"row36_no_67","F4CapT36"),(36,"r36n",66,"row36_no_66_NEGCTRL","F4CapTNeg")]:
    body,n,rw = gen(idx,nm,bd,tn)
    open(os.path.join(OUT,fn+".lean"),"w",encoding="utf-8").write(hdr+body+"\n\nend F4CapT\n")
    print("%s: bad=%d repairWidth=%d bound=%d"%(fn,n,rw,bd))
