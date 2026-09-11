#include <array>
#include <cstdint>
#include <vector>
using U=uint64_t;
static int pc(U x){return __builtin_popcountll(x);}
static int first(U x){return __builtin_ctzll(x);}
// Exact completed singleton-star count, assuming a C4-free partial base.
extern "C" int star_count(const U*input,int s,U*nodes){
 if(s<7||s>=49)return -1;
 int need=7-pc(input[s]);if(need!=2&&need!=3)return -1;
 U covered=0;for(U ns=input[s];ns;ns&=ns-1){U sup=input[first(ns)]&127;if(covered&sup)return -1;covered|=sup;}
 std::vector<int>eligible;
 for(int p=7;p<49;p++)if(pc(input[p]&127)==2&&!(input[p]&127&covered)){
  bool ok=true;for(U ns=input[s];ns;ns&=ns-1)if(input[p]&input[first(ns)]){ok=false;break;}
  if(ok)eligible.push_back(p);
 }
 int count=0;
 auto visit=[&](auto&&self,int index,int left,U used,std::array<int,3> selected,int n)->void{
  ++*nodes;
  if(!left){if(used==127)count++;return;}
  for(int i=index;i<int(eligible.size());i++){
   int p=eligible[i];U sup=input[p]&127;if(sup&used)continue;
   bool ok=true;for(int j=0;j<n;j++)if(input[p]&input[selected[j]]){ok=false;break;}
   if(!ok)continue;selected[n]=p;self(self,i+1,left-1,used|sup,selected,n+1);
  }
 };
 visit(visit,0,need,covered,{},0);return count;
}
// Each receipt is depth,s,chosen[7], using supplied order/E. Returns first bad receipt+1, else0.
extern "C" int verify_prefixes(const U*base,const int*E,const int*order,const U*receipts,int n,U*nodes){
 if(n<0)return -1;
 U em=0;unsigned permutation=0;
 for(int i=0;i<7;i++){if(E[i]<7||E[i]>=49||order[i]<0||order[i]>=7)return -1;em|=U(1)<<E[i];permutation|=1u<<order[i];}
 if(pc(em)!=7||permutation!=127)return -1;
 for(int k=0;k<n;k++){
  const U*r=receipts+9*k;if(r[0]>7||r[1]<7||r[1]>=49)return k+1;
  int depth=int(r[0]),s=int(r[1]);if(pc(base[s]&127)!=1)return k+1;
  std::array<U,49>g;for(int v=0;v<49;v++)g[v]=base[v];U used=0;unsigned assigned=0;
  for(int j=0;j<depth;j++)assigned|=1u<<order[j];
  for(int i=0;i<7;i++){
   U mask=r[i+2];if(!(assigned>>i&1)){if(mask)return k+1;continue;}
   if(mask>>49||mask&used||pc(mask)!=pc(base[E[i]]&em))return k+1;
   U covered=0;for(U ns=base[E[i]];ns;ns&=ns-1){U support=base[first(ns)]&127;if(covered&support)return k+1;covered|=support;}
   for(U ps=mask;ps;ps&=ps-1){int p=first(ps);U support=base[p]&127;if(p<7||pc(support)!=2||base[p]!=support||covered&support)return k+1;covered|=support;g[p]|=U(1)<<E[i];g[E[i]]|=U(1)<<p;}
   if(covered!=127)return k+1;used|=mask;
  }
  if(star_count(g.data(),s,nodes)!=0)return k+1;
 }
 return 0;
}
