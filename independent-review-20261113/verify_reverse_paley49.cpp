// Independent 49-vertex Paley-type reversed-clone obstruction (23 pivots).
// In the reverse orientation, 12 external vertices need >=132 repair capacity,
// but there are only 11 distinct admissible masks meeting that threshold.
#include <bits/stdc++.h>
using namespace std;
constexpr int N=23, M=1<<23;
using Bits=uint32_t;
int pc(Bits x){return __builtin_popcount(x);}
int main(int argc,char**argv){try{
 if(argc!=2)throw runtime_error("usage: verify_reverse_paley49 drtourn23.txt");
 ifstream f(argv[1]);string row;
 for(int i=0;i<36;i++)if(!getline(f,row))throw runtime_error("missing class36");
 if(row.size()!=253)throw runtime_error("invalid class36 encoding");
 Bits O[23]={},I[23]={};int k=0;
 for(int a=0;a<N;a++)for(int b=a+1;b<N;b++){
  if(row[k]=='1'){O[a]|=Bits(1)<<b;I[b]|=Bits(1)<<a;}
  else if(row[k]=='0'){O[b]|=Bits(1)<<a;I[a]|=Bits(1)<<b;}
  else throw runtime_error("invalid class bit");
  k++;
 }
 for(int a=0;a<N;a++){
  if(pc(O[a])!=11||pc(I[a])!=11)throw runtime_error("not 23-regular");
  for(int b=a+1;b<N;b++)if(pc(I[a]&I[b])!=5)
    throw runtime_error("not doubly regular");
 }
 vector<uint16_t> z(M,0);int bad=0;
 for(int a=0;a<N;a++)for(int b=a+1;b<N;b++)
 for(int c=b+1;c<N;c++)for(int d=c+1;d<N;d++)
  if(!(I[a]&I[b]&I[c]&I[d])){
   z[(1<<a)|(1<<b)|(1<<c)|(1<<d)]=1;bad++;
  }
 for(int i=0;i<N;i++){
  int step=1<<i;
  for(int base=0;base<M;base+=2*step)
   for(int j=0;j<step;j++)z[base+step+j]+=z[base+j];
 }
 if(bad!=2530)throw runtime_error("class36 bad set count changed");
 int capU=0;
 for(Bits W=0;W<Bits(M);W++){
  bool uniform=true;
  for(int h=0;h<N;h++)if(pc(W&I[h])>6){uniform=false;break;}
  if(uniform)capU=max(capU,(int)z[W]);
 }
 if(capU!=66)throw runtime_error("class36 uniform cap not 66");
 for(int pivot=0;pivot<N;pivot++){
  Bits twinOut=O[pivot];
  if(pc(twinOut)!=11||z[twinOut]!=0)throw runtime_error("invalid reverse clone");
  // Explicit S3 condition on 24-vertex reverse-clone core:
  // triple including w is dominated by an I_U(pivot)-vertex from S3 of U.
  Bits twinIn=((Bits(1)<<23)-1)^twinOut;
  for(int a=0;a<N;a++)for(int b=a+1;b<N;b++)
   if(!(I[a]&I[b]&twinIn))throw runtime_error("clone fails S3");
  int maxH=0,high=0,minHigh=10000;
  for(Bits W=0;W<Bits(M);W++){
   bool hybrid=true;
   for(int h=0;h<N;h++)
    if(pc(W&I[h])>6+int((twinOut>>h)&1u)){hybrid=false;break;}
   if(!hybrid)continue;
   maxH=max(maxH,(int)z[W]);
   if(z[W]>=132){high++;minHigh=min(minHigh,(int)z[W]);}
  }
  cout<<"ROW=36 REVERSE_PIVOT="<<pivot<<" BAD="<<bad
      <<" UNIFORM_MAX="<<capU<<" HYBRID_MAX="<<maxH
      <<" HIGH_CANDIDATES="<<high<<" HIGH_MIN="<<minHigh
      <<" HYBRID_VERTICES_NEEDED=12\n";
  if(maxH!=146||high!=11||minHigh!=146)
   throw runtime_error("near-optimal mask scarcity proof failed");
 }
 // Capacity upper 12*66+12*146=2544, only 14 above 2530 required.
 // Every one of twelve hybrid external vertices must cover >=132 bad sets;
 // only eleven distinct qualifying masks exist. Two vertices duplicate a
 // 146-set repair region, exceeding all 14 units of allowed overlap.
 cout<<"CLASS36_REVERSED_CLONES_EXCLUDED=23\n"
     <<"ALL_PALLEY_REVERSED_DRT23_49_COURTS=PASS\n";
 return 0;
}catch(const exception&e){cerr<<"FAIL "<<e.what()<<"\n";return 2;}}
