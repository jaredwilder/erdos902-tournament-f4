// DRT(23,11,5) uniform analytic/finite obstruction; stdlib C++17.
// Exact count over every admissible mask, for every one of the 37 published classes.
// Replay: g++ -O3 -std=c++17 uniform_f4.cpp -o /tmp/uniform_f4 && /tmp/uniform_f4 drtourn23.txt
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
constexpr int N=23, S=1<<N;
using Mask=uint32_t;
inline int pop(Mask a){return __builtin_popcount(a);}
struct Core {
 array<Mask,N> out{},in{};
 Core(const string&bits){
  if(bits.size()!=253)throw runtime_error("bad row length");
  int k=0;
  for(int i=0;i<N;i++)for(int j=i+1;j<N;j++){
   if(bits[k]=='1'){out[i]|=1u<<j;in[j]|=1u<<i;}
   else if(bits[k]=='0'){out[j]|=1u<<i;in[i]|=1u<<j;}
   else throw runtime_error("bad orientation bit");
   k++;
  }
  for(int i=0;i<N;i++)if(pop(out[i])!=11||pop(in[i])!=11)throw runtime_error("not regular");
  for(int i=0;i<N;i++)for(int j=i+1;j<N;j++)
   if(pop(out[i]&out[j])!=5 || pop(in[i]&in[j])!=5)
    throw runtime_error("not doubly regular");
 }
};
struct Result{int bad=0,cap=0,cap11=0,cap12=0,adm12=0;};
Result court(const Core&t,int row){
 vector<uint16_t> z(S,0);
 array<int,4> n{};
 for(int a=0;a<N;a++)for(int b=a+1;b<N;b++)
  for(int c=b+1;c<N;c++)for(int d=c+1;d<N;d++){
   int dominated=pop(t.in[a]&t.in[b]&t.in[c]&t.in[d]);
   if(dominated>3)throw runtime_error("universal 4-dominator bound false");
   n[dominated]++;
   if(!dominated)z[(1u<<a)|(1u<<b)|(1u<<c)|(1u<<d)]=1;
  }
 if(n[0]+n[1]+n[2]+n[3]!=8855 ||
    n[1]+2*n[2]+3*n[3]!=7590 ||
    n[2]+3*n[3]!=1265 || n[0]<2109)
    throw runtime_error("universal incidence identities failed");
 for(int b=0;b<N;b++){
  int step=1<<b;
  for(int base=0;base<S;base+=2*step)
   for(int off=0;off<step;off++)z[base+step+off]+=z[base+off];
 }
 Result r;r.bad=n[0];
 for(Mask w=0;w<(Mask)S;w++){
  int size=pop(w);
  if(size>12)continue; // general quadratic identity forbids larger admissible masks
  bool ok=true;
  for(int h=0;h<N;h++)if(pop(w&t.in[h])>6){ok=false;break;}
  if(!ok)continue;
  r.cap=max(r.cap,(int)z[w]);
  if(size==11)r.cap11=max(r.cap11,(int)z[w]);
  if(size==12){
   r.cap12=max(r.cap12,(int)z[w]);r.adm12++;
   bool closed=false;
   for(int h=0;h<N;h++)
    if(w==((1u<<h)|t.out[h])){closed=true;break;}
   if(!closed)throw runtime_error("12-set rigidity failed");
  }
 }
 if(r.adm12!=23 || r.cap>85)throw runtime_error("37-class cap/rigidity failed");
 mt19937_64 g(340000+row);
 for(int k=0;k<100;k++){
  Mask w=g()%(1u<<N);int size=pop(w),lhs=0;
  for(int h=0;h<N;h++){int a=pop(w&t.in[h]);lhs+=a*(6-a);}
  if(lhs!=5*size*(12-size))throw runtime_error("quadratic identity failed");
 }
 cout<<"ROW="<<row<<" BAD="<<r.bad<<" CAP="<<r.cap
     <<" CAP11="<<r.cap11<<" CAP12="<<r.cap12
     <<" ADMISSIBLE12="<<r.adm12<<" Q3="<<n[3]<<"\n";
 return r;
}
int main(int argc,char**argv){
 try{
  if(argc<2)throw runtime_error("usage: uniform_f4 catalogue.txt");
  ifstream f(argv[1]);if(!f)throw runtime_error("cannot read catalogue");
  string s;vector<Core> all;
  while(getline(f,s))if(!s.empty())all.emplace_back(s);
  if(all.size()!=37)throw runtime_error("expected 37 rows");
  int maxcap=0,minbad=100000,maxcap12=0;
  for(int i=0;i<37;i++){
   auto r=court(all[i],i+1);
   maxcap=max(maxcap,r.cap);minbad=min(minbad,r.bad);maxcap12=max(maxcap12,r.cap12);
  }
  if(maxcap!=85 || maxcap12!=69 || minbad!=2475)throw runtime_error("frozen snapshot regression");
  cout<<"UNIVERSAL_BAD_LOWER=2109\n"
      <<"ALL_37_CAP_UPPER="<<maxcap<<"\n"
      <<"OUTSIDE_24_MAX_REPAIR="<<24*maxcap<<"\n"
      <<"CLASSIFICATION_UNIFORM_GAP="<<2109-24*maxcap<<"\n"
      <<"ALL_37_CAP_12_UPPER="<<maxcap12<<"\n"
      <<"MINIMUM_FULL_12_MASKS_IN_ORDER48=12\n"
      <<"DEGREE_BUDGET_MAX_REPAIRS="<<12*maxcap+12*maxcap12<<"\n"
      <<"DEGREE_BUDGET_GAP="<<2109-(12*maxcap+12*maxcap12)<<"\n"
      <<"THEOREM_CONDITIONAL_ON_PUBLISHED_37_CLASS_COUNT=PASS\n";
  return 0;
 }catch(const exception&e){cerr<<"FAIL "<<e.what()<<"\n";return 2;}
}