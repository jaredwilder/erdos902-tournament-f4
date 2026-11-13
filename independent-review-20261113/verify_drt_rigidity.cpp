// Independent exhaustive rigidity audit. For each of the 37 DRT23 classes,
// every 11-subset meeting every in-neighborhood in >=5 points is principal.
#include <bits/stdc++.h>
using namespace std;
int pc(uint32_t x){return __builtin_popcount(x);}
int main(int argc,char**argv){try{
 if(argc!=2)throw runtime_error("usage: verify_drt_rigidity drtourn23.txt");
 ifstream f(argv[1]);string s;int row=0,validTotal=0;
 while(getline(f,s))if(!s.empty()){
  if(s.size()!=253)throw runtime_error("invalid class row");row++;
  uint32_t I[23]={};int p=0;
  for(int a=0;a<23;a++)for(int b=a+1;b<23;b++){
   char bit=s[p++];
   if(bit=='1')I[b]|=1u<<a;
   else if(bit=='0')I[a]|=1u<<b;
   else throw runtime_error("invalid class bit");
  }
  int valid=0;
  for(uint32_t w=0;w<(1u<<23);w++){
   if(pc(w)!=11)continue;
   bool okay=true;
   for(int h=0;h<23;h++)if(pc(w&I[h])<5){okay=false;break;}
   if(!okay)continue;
   bool principal=false;
   for(int h=0;h<23;h++)if(w==I[h])principal=true;
   if(!principal)throw runtime_error("rigidity counterexample");
   valid++;
  }
  if(valid!=23)throw runtime_error("unexpected number of admissible 11sets");
  validTotal+=valid;
  cout<<"ROW="<<row<<" ADMISSIBLE11="<<valid<<" NONPRINCIPAL=0\n";
 }
 if(row!=37||validTotal!=851)throw runtime_error("bad catalogue");
 cout<<"GENERAL_RIGIDITY_37_CLASS_FINITE_COURT=PASS\n";
 return 0;
 }catch(const exception&e){cerr<<"FAIL "<<e.what()<<"\n";return 2;}}
