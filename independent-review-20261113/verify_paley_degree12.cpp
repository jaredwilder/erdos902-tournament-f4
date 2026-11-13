// Class36 (Paley23) exhaustive 12-indegree extension court, 276 configurations.
// Self-contained C++17. Frozen isomorphism to cyclic Paley23 justifies 12 orbits.
// Every 12-set satisfying all lower intersections must equal I(a) union {b}.
#include <bits/stdc++.h>
using namespace std;
constexpr int N=23,M=1<<23;
using Bits=uint32_t;
int pc(Bits x){return __builtin_popcount(x);}
void zeta(vector<uint16_t>&z){
 for(int i=0;i<N;i++){
  int p=1<<i;
  for(int base=0;base<M;base+=2*p)
   for(int k=0;k<p;k++)z[base+p+k]+=z[base+k];
 }
}
int main(int argc,char**argv){try{
 if(argc!=2)throw runtime_error("usage: verify_paley_degree12 drtourn23.txt");
 ifstream f(argv[1]);string s;
 for(int i=0;i<36;i++)if(!getline(f,s))throw runtime_error("missing class36");
 if(s.size()!=253)throw runtime_error("invalid class36 encoding");
 Bits O[23]={},I[23]={};int k=0;
 for(int a=0;a<N;a++)for(int b=a+1;b<N;b++){
  if(s[k]=='1'){O[a]|=1u<<b;I[b]|=1u<<a;}
  else if(s[k]=='0'){O[b]|=1u<<a;I[a]|=1u<<b;}
  else throw runtime_error("non-binary catalogue row");
  k++;
 }
 // Verified explicit graph isomorphism between frozen row36 and QR23.
 const int p[23]={0,1,9,2,13,3,4,18,8,16,12,6,19,14,7,5,17,10,20,21,22,11,15};
 bool used[23]={},qr[23]={};
 for(int a=0;a<N;a++){
  if(p[a]<0||p[a]>=N||used[p[a]])throw runtime_error("invalid permutation");
  used[p[a]]=true;
 }
 for(int x=1;x<N;x++)qr[x*x%N]=true;
 for(int a=0;a<N;a++)for(int b=0;b<N;b++)if(a!=b)
  if(bool((O[a]>>b)&1u)!=qr[(p[b]-p[a]+N)%N])
   throw runtime_error("Paley isomorphism certificate failed");
 // All size-12 possible I_U(w) from the necessary triple >=5 condition.
 int valid=0,wrong=0;
 for(Bits w=0;w<Bits(M);w++){
  if(pc(w)!=12)continue;
  bool good=true;
  for(int h=0;h<N;h++)if(pc(w&I[h])<5){good=false;break;}
  if(!good)continue;
  valid++;int principal=0;
  for(int h=0;h<N;h++)if((w&I[h])==I[h])principal++;
  if(principal!=1)wrong++;
 }
 if(valid!=276||wrong)throw runtime_error("degree12 enumeration not 276 principal+one masks");
 cout<<"PALEY_DRT23_12_INDEGREE_SUBSETS=276 NONPRINCIPAL=0\n";
 // Because of cyclic translation symmetry, fixing pivot0 leaves 12 orbits:
 // 11 one-point shifts b in O(0), plus reverse clone b=0.
 vector<uint16_t> full(M,0);vector<int>bad;
 for(int a=0;a<N;a++)for(int b=a+1;b<N;b++)
 for(int c=b+1;c<N;c++)for(int d=c+1;d<N;d++)
  if(!(I[a]&I[b]&I[c]&I[d])){
   int q=(1<<a)|(1<<b)|(1<<c)|(1<<d);
   full[q]=1;bad.push_back(q);
  }
 zeta(full);if(bad.size()!=2530)throw runtime_error("wrong bad4");
 int capUniform=0;
 for(Bits m=0;m<Bits(M);m++){
  bool uniform=true;
  for(int h=0;h<N;h++)if(pc(m&I[h])>6){uniform=false;break;}
  if(uniform)capUniform=max(capUniform,(int)full[m]);
 }
 if(capUniform!=66)throw runtime_error("wrong uniform repair maximum");
 int shifted=0,reversed=0,minGap=1<<30;
 for(int b=0;b<N;b++)if(!((I[0]>>b)&1u)){
  Bits wOut=(O[0]|Bits(1)) & ~(Bits(1)<<b);
  if(pc(wOut)!=11)throw runtime_error("wrong extension degree");
  Bits wIn=((Bits(1)<<N)-1)^wOut;
  for(int x=0;x<N;x++)for(int y=x+1;y<N;y++)
   if(!(I[x]&I[y]&wIn))throw runtime_error("S3 extension fails");
  vector<uint16_t> previous(M,0);
  for(int q:bad)if((Bits(q)&wOut)==Bits(q))previous[q]=1;
  zeta(previous);
  int capU=0,capH=0,high=0,minHigh=1<<30;
  for(Bits m=0;m<Bits(M);m++){
   bool u=true,h=true;
   for(int i=0;i<N;i++){
    int a=pc(m&I[i]);
    if(a>6)u=false;
    if(a>6+int((wOut>>i)&1u))h=false;
    if(!u&&!h)break;
   }
   int gain=int(full[m])-int(previous[m]);
   if(u)capU=max(capU,gain);
   if(h){
    capH=max(capH,gain);
    if(gain>=132){high++;minHigh=min(minHigh,gain);}
   }
  }
  int own=previous[M-1];
  int gap=int(bad.size())-own-12*capU-12*capH;
  cout<<"PIVOT=0 EXTRA="<<b<<" OWN="<<own<<" CAPU="<<capU
      <<" CAPH="<<capH<<" GAP="<<gap
      <<" HIGH_HYBRID="<<high<<" HIGH_MIN="<<(high?minHigh:0)<<"\n";
  if(b==0){
   // Zero repairs from w; 12*66+12*146-2530=14 units of overlap slack.
   // Twelve hybrid vertices must each repair >=132 bad4; only 11 masks qualify.
   if(own!=0||capU!=66||capH!=146||gap!=-14||high!=11||minHigh!=146)
    throw runtime_error("reverse-clone pigeonhole exclusion failed");
   reversed++;
  }else{
   if(gap<=0)throw runtime_error("shifted extension has no strict deficit");
   shifted++;minGap=min(minGap,gap);
  }
 }
 if(shifted!=11||reversed!=1||minGap!=10)
  throw runtime_error("12 translation orbit regression");
 cout<<"SHIFTED_12_INDEGREE_EXTENSIONS_EXCLUDED="<<23*shifted
     <<"\nREVERSED_12_INDEGREE_CLONES_EXCLUDED="<<23*reversed
     <<"\nALL_PALEY_12_INDEGREE_EXTENSIONS_EXCLUDED="<<23*(shifted+reversed)
     <<"\nMIN_SHIFTED_GAP="<<minGap<<"\nPALEY_DEGREE12_COURT=PASS\n";
 return 0;
}catch(const exception&e){cerr<<"FAIL "<<e.what()<<"\n";return 2;}}
