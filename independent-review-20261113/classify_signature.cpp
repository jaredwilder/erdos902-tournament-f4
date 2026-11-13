// Independent isomorphism-invariant fingerprint of 37 DRT23 catalogue rows.
// All 56 unlabeled 6-vertex tournaments are constructed by relabeling.
#include <bits/stdc++.h>
using namespace std;
struct Tour{int a[23][23];};
vector<Tour> read(const string&path){
 ifstream f(path);string s;vector<Tour> out;
 while(getline(f,s))if(!s.empty()){
  Tour t{};int p=0;
  for(int j=1;j<23;j++)for(int i=0;i<j;i++){} // order actual upper triangle is i-outer, j-inner
  for(int i=0;i<23;i++)for(int j=i+1;j<23;j++){int z=s[p++]-'0';t.a[i][j]=z;t.a[j][i]=1-z;}
  out.push_back(t);
 }
 return out;
}
struct CMap{
 int k,bits,K;vector<int> cl;int counts;
 CMap(int n):k(n),bits(n*(n-1)/2),K(1<<bits),cl(K,0),counts(0){
  int id[7][7]={};int bit=0;
  for(int j=1;j<k;j++)for(int i=0;i<j;i++)id[i][j]=bit++;
  vector<int> perm(k);iota(perm.begin(),perm.end(),0);
  vector<vector<int>> maps;
  do{
   vector<int> m;for(int j=1;j<k;j++)for(int i=0;i<j;i++){
    int a=perm[i],b=perm[j];m.push_back(a<b?id[a][b]:(id[b][a]|0x8000));
   }maps.push_back(m);
  }while(next_permutation(perm.begin(),perm.end()));
  for(int c=0;c<K;c++)if(!cl[c]){
   counts++;
   for(const auto&m:maps){int code=0;for(int b=0;b<bits;b++)code|=((((c>>(m[b]&0x7fff))&1)^(m[b]>>15))<<b);cl[code]=counts;}
  }
 }
};
vector<long> hist(const Tour&t,const CMap&m){
 vector<long> h(m.counts);vector<int> pick;
 function<void(int)> dfs=[&](int x){
   if(pick.size()==m.k){int code=0,bit=0;
      for(int j=1;j<m.k;j++)for(int i=0;i<j;i++)code|=t.a[pick[i]][pick[j]]<<bit++;
      h[m.cl[code]-1]++;return;
   }
   for(int i=x;i<=23-(m.k-(int)pick.size());i++){pick.push_back(i);dfs(i+1);pick.pop_back();}
 };
 dfs(0);return h;
}
int main(int argc,char**argv){if(argc<2)return 2;auto ts=read(argv[1]);
 for(int k=5;k<=7;k++){
  auto c=CMap(k);cerr<<"k="<<k<<" tournament classes="<<c.counts<<"\n";
  vector<vector<long>> sig;for(auto&t:ts)sig.push_back(hist(t,c));
  map<vector<long>,vector<int>> groups;for(int i=0;i<(int)ts.size();i++)groups[sig[i]].push_back(i+1);
  cout<<"k="<<k<<" distinct signatures="<<groups.size()<<" / 37\n";
  if(k==6){
    vector<vector<int>> collisions;
    for(const auto& [signature, ids]:groups)if(ids.size()>1)collisions.push_back(ids);
    sort(collisions.begin(),collisions.end());
    if(groups.size()!=35 || collisions!=vector<vector<int>>({{1,35},{26,37}})){
       cerr<<"Unexpected 6-subtournament profile collisions: refused\n";exit(8);
    }
    cout<<"SIX_CLASS_PROFILE=PASS (35 distinct + 2 candidate pairs)\n";
  }
  for(const auto&[s,ids]:groups)if(ids.size()>1){cout<<"  collision ";for(int i:ids)cout<<i<<" ";cout<<"\n";}
  if(groups.size()==37){cout<<"37 IDENTIFIED DISTINCT BY k="<<k<<"-SUBTOURNAMENT PROFILE\n";break;}
 }
}
