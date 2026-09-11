#include <cstdint>
#include <vector>
#include <array>
using U=uint64_t;
static int pc(U x){return __builtin_popcountll(x);}
static int first(U x){return __builtin_ctzll(x);}
// Caller supplies validated singleton-complete a6/a7 graph. Buffer holds1024 masks.
extern "C" int enumerate_rows(const U*g,int u,U*out,U*nodes){
 if(u<7||u>=49)return -1;
 int need=7-pc(g[u]);if(need<2||need>5)return -1;
 U own=g[u]&127;if(pc(own)!=1&&pc(own)!=2)return -1;
 U covered=0;for(U ns=g[u];ns;ns&=ns-1){U sup=g[first(ns)]&127;if(covered&sup)return -1;covered|=sup;}
 std::vector<int>eligible;
 for(int v=7;v<49;v++){
  U sup=g[v]&127;
  if(v==u||!sup||sup&covered||(g[u]>>v&1)||(pc(own)==1&&pc(sup)==1))continue;
  bool ok=true;for(U ns=g[u];ns;ns&=ns-1)if(g[v]&g[first(ns)]){ok=false;break;}
  if(ok)eligible.push_back(v);
 }
 int n=0;bool overflow=false;
 auto visit=[&](auto&&self,int index,int left,U colours,U mask,std::array<int,5>chosen,int used)->void{
  ++*nodes;
  if(!left){if(colours==127){if(n<1024)out[n++]=mask;else overflow=true;}return;}
  if(int(eligible.size())-index<left)return;
  int remaining=7-pc(colours);if(remaining<left||remaining>2*left)return;
  for(int i=index;i<int(eligible.size());i++){
   int v=eligible[i];U sup=g[v]&127;if(sup&colours)continue;
   bool ok=true;for(int j=0;j<used;j++)if(g[v]&g[chosen[j]]){ok=false;break;}
   if(!ok)continue;chosen[used]=v;self(self,i+1,left-1,colours|sup,mask|(U(1)<<v),chosen,used+1);
  }
 };
 visit(visit,0,need,covered,0,{},0);return overflow?-2:n;
}
