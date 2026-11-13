// 49-vertex S4 exclusion: independent 37-class DRT23 twin-extension court.
// Self-contained C++17. Every 23-bit mask in every S3-valid extension is inspected.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
constexpr int N=23, M=1<<23;
using Bits=uint32_t;
int pc(Bits x){return __builtin_popcount(x);}
struct Core{
 array<Bits,N> O{},I{};
 Core(const string&s){
  if(s.size()!=253)throw runtime_error("invalid catalogue row length");
  int k=0;
  for(int a=0;a<N;a++)for(int b=a+1;b<N;b++){
   if(s[k]=='1'){O[a]|=Bits(1)<<b;I[b]|=Bits(1)<<a;}
   else if(s[k]=='0'){O[b]|=Bits(1)<<a;I[a]|=Bits(1)<<b;}
   else throw runtime_error("invalid catalogue bit");
   k++;
  }
  for(int a=0;a<N;a++){
   if(pc(O[a])!=11||pc(I[a])!=11)throw runtime_error("not regular");
   for(int b=a+1;b<N;b++)if(pc(O[a]&O[b])!=5||pc(I[a]&I[b])!=5)
    throw runtime_error("not doubly regular");
  }
 }
};
bool clone_S3(const Core&t,int pivot){
 array<Bits,24> I{};
 for(int h=0;h<N;h++)I[h]=t.I[h];
 const Bits W=t.O[pivot]|(Bits(1)<<pivot);
 for(int h=0;h<N;h++){
  if(W&(Bits(1)<<h))I[h]|=Bits(1)<<23;
  else I[23]|=Bits(1)<<h;
 }
 for(int a=0;a<24;a++)for(int b=a+1;b<24;b++)for(int c=b+1;c<24;c++)
  if(!(I[a]&I[b]&I[c]))return false;
 return true;
}
void zeta(vector<uint16_t>&z){
 for(int bit=0;bit<N;bit++){
  int p=1<<bit;
  for(int base=0;base<M;base+=2*p)
   for(int k=0;k<p;k++)z[base+p+k]+=z[base+k];
 }
}
vector<int> bad4(const Core&t){
 vector<int>b;b.reserve(3000);
 for(int a=0;a<N;a++)for(int c=a+1;c<N;c++)
 for(int d=c+1;d<N;d++)for(int e=d+1;e<N;e++)
  if(!(t.I[a]&t.I[c]&t.I[d]&t.I[e]))
   b.push_back((1<<a)|(1<<c)|(1<<d)|(1<<e));
 return b;
}
int main(int argc,char**argv){
 try{
  if(argc!=2)throw runtime_error("usage: verify_clone49 drtourn23.txt");
  ifstream f(argv[1]);if(!f)throw runtime_error("cannot read catalogue");
  vector<Core> cores;string s;
  while(getline(f,s))if(!s.empty())cores.emplace_back(s);
  if(cores.size()!=37)throw runtime_error("expected exactly 37 classes");
  int viable=0,worst=1<<30,worstRow=0,worstPivot=0;
  int byClass[38]={};
  for(int ri=0;ri<37;ri++){
   const Core&t=cores[ri];
   vector<int> bad=bad4(t),pivots;
   for(int p=0;p<N;p++)if(clone_S3(t,p))pivots.push_back(p);
   if(pivots.empty()){
    if(ri==34||ri==35)throw runtime_error("missing known S3 core");
    continue;
   }
   if(ri!=34&&ri!=35)throw runtime_error("unexpected S3 class");
   if(pivots.size()!=23)throw runtime_error("expected 23 S3 extensions");
   viable+=23;byClass[ri+1]=23;
   vector<uint16_t> full(M,0);
   for(int q:bad)full[q]=1;
   zeta(full);
   if(full[M-1]!=(int)bad.size())throw runtime_error("bad subset zeta total");
   for(int pivot:pivots){
    Bits twin=t.O[pivot]|(Bits(1)<<pivot);
    vector<uint16_t> previous(M,0);
    for(int q:bad)if((Bits(q)&twin)==Bits(q))previous[q]=1;
    zeta(previous);
    int twinRepairs=previous[M-1];
    if(twinRepairs!=full[twin])throw runtime_error("overlap count mismatch");
    int capU=0,capH=0;
    for(Bits W=0;W<Bits(M);W++){
     bool uniform=true,hybrid=true;
     for(int h=0;h<N;h++){
      int a=pc(W&t.I[h]);
      if(a>6)uniform=false;
      if(a>6+int((twin>>h)&1u))hybrid=false;
      if(!uniform&&!hybrid)break;
     }
     int newRepairs=int(full[W])-int(previous[W]);
     if(newRepairs<0)throw runtime_error("bad overlap subtraction");
     if(uniform)capU=max(capU,newRepairs);
     if(hybrid)capH=max(capH,newRepairs);
    }
    // In a regular T49, w beats v and exactly 12 of U, leaving 11 X
    // vertices beaten by w (hybrid) and 13 that beat w (uniform).
    int needed=int(bad.size())-twinRepairs;
    int maximum=13*capU+11*capH;
    int gap=needed-maximum;
    cout<<"ROW="<<ri+1<<" PIVOT="<<pivot<<" BAD="<<bad.size()
        <<" TWIN="<<twinRepairs<<" NEW_UNIFORM="<<capU
        <<" NEW_HYBRID="<<capH<<" UNCOVERED_NEED="<<needed
        <<" MAX_NEW_REPAIRS="<<maximum<<" GAP="<<gap<<"\n";
    if(gap<worst){worst=gap;worstRow=ri+1;worstPivot=pivot;}
    if(gap<=0)throw runtime_error("49-vertex cloned-core obstruction failed");
   }
  }
  if(viable!=46||byClass[35]!=23||byClass[36]!=23||worst!=30)
   throw runtime_error("frozen 46-case regression failed");
  cout<<"CATALOGUE_CLASSES=37\nS3_CLONE_EXTENSIONS="<<viable
      <<"\nCLASS35_EXTENSIONS=23\nCLASS36_EXTENSIONS=23"
      <<"\nMIN_GAP="<<worst<<" WORST_ROW="<<worstRow
      <<" WORST_PIVOT="<<worstPivot
      <<"\nNO_49_S4_TOURNAMENT_WITH_DRT23_CLONED_INNEIGHBORHOOD=PASS\n";
  return 0;
 }catch(const exception&e){cerr<<"FAIL "<<e.what()<<"\n";return 2;}
}
