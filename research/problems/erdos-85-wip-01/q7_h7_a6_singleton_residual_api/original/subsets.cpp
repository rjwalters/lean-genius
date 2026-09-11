#include <algorithm>
#include <cstdint>
#include <vector>
#include <functional>
#include <chrono>
using Mask=uint64_t;
extern "C" int verify_domain(const Mask*g,int u,const Mask*expected,int count,int cap,double seconds,int*used){
 auto deadline=std::chrono::steady_clock::now()+std::chrono::duration<double>(seconds);
 unsigned represented=0;for(Mask ns=g[u];ns;ns&=ns-1)represented|=unsigned(g[__builtin_ctzll(ns)]&127);
 unsigned missing=127^represented;std::vector<int> candidates;
 for(int v=7;v<49;v++){
  unsigned support=g[v]&127;
  if(!support || v==u || (g[u]>>v&1) || (support&~missing))continue;
  if(__builtin_popcountll(g[u]&127)==1 && __builtin_popcount(support)==1)continue;
  bool ok=true;for(Mask ns=g[u];ns;ns&=ns-1)if(g[v]&g[__builtin_ctzll(ns)]&~(Mask(1)<<u)){ok=false;break;}
  if(ok)candidates.push_back(v);
 }
 std::vector<Mask> actual;
 std::function<void(int,int,unsigned,Mask,Mask)> dfs=[&](int at,int need,unsigned left,Mask row,Mask neighbours){
  if(++*used>cap || std::chrono::steady_clock::now()>deadline)throw 1;
  if(!need){if(!left)actual.push_back(row);return;}
  if(int(candidates.size())-at<need || __builtin_popcount(left)<need || __builtin_popcount(left)>2*need)return;
  for(int j=at;j<int(candidates.size());j++){
   int v=candidates[j];unsigned support=g[v]&127;
   if(support&~left || (g[v]&neighbours))continue;
   dfs(j+1,need-1,left^support,row|(Mask(1)<<v),neighbours|g[v]);
  }
 };
 try{dfs(0,7-__builtin_popcountll(g[u]),missing,0,0);}catch(int){return -1;}
 std::sort(actual.begin(),actual.end());std::vector<Mask>wanted(expected,expected+count);std::sort(wanted.begin(),wanted.end());
 return actual==wanted && std::adjacent_find(wanted.begin(),wanted.end())==wanted.end();
}
