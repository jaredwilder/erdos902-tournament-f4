// Independent exact certificate checker for f(4)>=49.
// Self-contained: stdlib, C++17; source data from published DRT23 catalogue.
// This file is deliberately separate from speaker-package/verify_real_002.py.
#include <bits/stdc++.h>
using namespace std;
static constexpr int N=23,M=1<<N;
static uint16_t z[M];
struct T {uint32_t O[N]={},I[N]={};};
T parse(const string&s){
 T t;int k=0;
 for(int i=0;i<N;i++)for(int j=i+1;j<N;j++){
   if(s[k++]=='1'){t.O[i]|=1<<j;t.I[j]|=1<<i;}
   else {t.O[j]|=1<<i;t.I[i]|=1<<j;}
 }
 if(k!=253)throw runtime_error("bad encoding");
 return t;
}
int pcount(uint32_t a){return __builtin_popcount(a);}
bool drt(const T&t){
 for(int i=0;i<N;i++){
   if(pcount(t.O[i])!=11)return false;
   for(int j=i+1;j<N;j++)if(pcount(t.O[i]&t.O[j])!=5)return false;
 }
 return true;
}
bool s3(const T&t){
 for(int i=0;i<N;i++)for(int j=i+1;j<N;j++)for(int k=j+1;k<N;k++)
   if(!(t.I[i]&t.I[j]&t.I[k]))return false;
 return true;
}
struct Stats{int bad4=0,maxRepair=0,totalAdm=0,adm12=0,adm11=0;vector<int> badMasks;};
Stats profile(const T&t){
 memset(z,0,sizeof(z));Stats r;
 for(int a=0;a<N;a++)for(int b=a+1;b<N;b++)for(int c=b+1;c<N;c++)for(int d=c+1;d<N;d++){
    if(!(t.I[a]&t.I[b]&t.I[c]&t.I[d])){
      int s=(1<<a)|(1<<b)|(1<<c)|(1<<d);
      z[s]=1;r.bad4++;r.badMasks.push_back(s);
    }
 }
 for(int b=0;b<N;b++){
   int step=1<<b;
   for(int base=0;base<M;base+=step*2)
     for(int j=0;j<step;j++)z[base+step+j]+=z[base+j];
 }
 if(z[M-1]!=r.bad4)throw runtime_error("subset-zeta total disagrees");
 for(int m=0;m<M;m++){
   int s=pcount(m);if(s>12)continue;
   bool ok=true;
   for(int h=0;h<N;h++)if(pcount(m&t.I[h])>6){ok=false;break;}
   if(!ok)continue;
   r.totalAdm++;
   if(s==12)r.adm12++;
   if(s==11)r.adm11++;
   r.maxRepair=max(r.maxRepair,(int)z[m]);
 }
 mt19937 gen(4196);
 for(int j=0;j<30;j++){
    int m=gen()&(M-1), brute=0;
    for(int b:r.badMasks)brute+=((b&m)==b);
    if(z[m]!=brute)throw runtime_error("direct bad-subset crosscheck failed");
 }
 return r;
}
int main(int argc,char**argv){
 if(argc<2){cerr<<"Usage: independent_f4 catalogue.txt\n";return 2;}
 ifstream f(argv[1]);string s;vector<T> ts;
 while(getline(f,s))if(!s.empty()){
  if(s.size()!=253)throw runtime_error("bad row length");
  T t=parse(s);if(!drt(t))throw runtime_error("not DRT");ts.push_back(t);
 }
 if(ts.size()!=37)throw runtime_error("not 37 classes");
 vector<int> survivors;
 for(int i=0;i<37;i++)if(s3(ts[i]))survivors.push_back(i+1);
 cout<<"N_CATALOGUE="<<ts.size()<<" S3_ROWS=";
 for(auto v:survivors)cout<<v<<",";cout<<"\n";
 if(survivors!=vector<int>({35,36}))throw runtime_error("unexpected S3 cores");
 for(auto idx:survivors){
    Stats st=profile(ts[idx-1]);
    cout<<"ROW="<<idx<<" BAD4="<<st.bad4<<" MAX_REPAIR="<<st.maxRepair
        <<" ADMISSIBLE="<<st.totalAdm<<" SIZE11="<<st.adm11<<" SIZE12="<<st.adm12<<"\n";
    if(idx==35 && (st.bad4!=2475||st.maxRepair!=65||st.totalAdm!=1153310||st.adm12!=23||st.adm11!=309))throw runtime_error("row35 fails");
    if(idx==36 && (st.bad4!=2530||st.maxRepair!=66||st.totalAdm!=1152232||st.adm12!=23||st.adm11!=276))throw runtime_error("row36 fails");
 }
 cout<<"48_VERTEX_CAPACITY="<<24*66<<" BAD4_MIN="<<2475<<" SHORTFALL="<<2475-24*66<<"\n";
 if(!(24*66<2475))throw runtime_error("capacity contradiction missing");
 cout<<"INDEPENDENT_FINITE_CHECK=PASS\n";
}
