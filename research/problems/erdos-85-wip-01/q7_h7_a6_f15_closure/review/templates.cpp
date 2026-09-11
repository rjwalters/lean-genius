#include <cstdint>
#include <vector>
#include <algorithm>
#include <functional>
using M=uint64_t;
extern "C" int domains(const M*g,int u,M*out){
 int pvertex[7][7];std::vector<int>single[7];for(int v=7;v<42;v++){unsigned sp=g[v]&127;if(__builtin_popcount(sp)==1)single[__builtin_ctz(sp)].push_back(v);else{int a=__builtin_ctz(sp),b=__builtin_ctz(sp&(sp-1));pvertex[a][b]=pvertex[b][a]=v;}}
 unsigned missing=0;for(int h=0;h<7;h++)if(!(g[u]&g[h]))missing|=1<<h;
 int need=7-__builtin_popcountll(g[u]),np=__builtin_popcount(missing)-need;std::vector<M>answer;
 auto check=[&](M row){if(row&((M(1)<<u)|g[u]))return;M ns=g[u]|row;if(__builtin_popcountll(ns)!=7)return;for(M a=ns;a;a&=a-1){int v=__builtin_ctzll(a);for(M b=a&(a-1);b;b&=b-1)if(g[v]&g[__builtin_ctzll(b)]&~(M(1)<<u))return;}answer.push_back(row);};
 for(unsigned pc=0;pc<128;pc++)if(!(pc&~missing)&&__builtin_popcount(pc)==2*np){
  unsigned sc=missing^pc;if(__builtin_popcountll(g[u]&127)==1&&sc)continue;
  std::function<void(unsigned,M)>ss=[&](unsigned left,M row){if(!left){check(row);return;}int h=__builtin_ctz(left);for(int v:single[h])ss(left^(1<<h),row|(M(1)<<v));};
  std::function<void(unsigned,M)>pp=[&](unsigned left,M row){if(!left){ss(sc,row);return;}int a=__builtin_ctz(left);left^=1<<a;for(int b=a+1;b<7;b++)if(left>>b&1)pp(left^(1<<b),row|(M(1)<<pvertex[a][b]));};
  pp(pc,0);
 }
 std::sort(answer.begin(),answer.end());if(answer.size()>1024||std::adjacent_find(answer.begin(),answer.end())!=answer.end())return -1;std::copy(answer.begin(),answer.end(),out);return answer.size();
}
