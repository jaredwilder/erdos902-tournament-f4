// Eight-vertex degree-sequence fingerprints separate remaining DRT23 pairs.
// Isomorphic tournaments have identical distributions of induced degree sequences.
#include <bits/stdc++.h>
using namespace std;
struct T{int a[23][23];};
vector<T>read(string p){ifstream f(p);string s;vector<T>v;while(getline(f,s))if(!s.empty()){T t{};int k=0;for(int i=0;i<23;i++)for(int j=i+1;j<23;j++){int b=s[k++]-'0';t.a[i][j]=b;t.a[j][i]=1-b;}v.push_back(t);}return v;}
map<uint64_t,int> hist(const T&t,int k){vector<int>p;map<uint64_t,int> H;
 function<void(int)>f=[&](int a){if(p.size()==k){int d[10]={};for(int i=0;i<k;i++)for(int j=i+1;j<k;j++){d[i]+=t.a[p[i]][p[j]];d[j]+=t.a[p[j]][p[i]];}
 sort(d,d+k);uint64_t code=0;for(int i=0;i<k;i++)code=code*11+d[i];H[code]++;return;}
 for(int i=a;i<=23-(k-(int)p.size());i++){p.push_back(i);f(i+1);p.pop_back();}};f(0);return H;}
int main(int argc,char**argv){if(argc<2)return 2;auto v=read(argv[1]);for(auto [a,b]:vector<pair<int,int>>({{1,35},{26,37}})){for(int k=8;k<=10;k++){auto x=hist(v[a-1],k), y=hist(v[b-1],k);cerr<<"pair "<<a<<","<<b<<" k="<<k<<" hist sizes "<<x.size()<<","<<y.size()<<" differ="<<(x!=y)<<"\n";if(x!=y)break; if(k==10)exit(9);}}cout<<"ALL_37_DISTINCT_UP_TO_ISOMORPHISM=PASS (with the k=6 court)\n";}
