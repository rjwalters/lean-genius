#include <cstdint>
#include <vector>
#include <algorithm>
#include <chrono>
#include <stdexcept>
using U=uint64_t;
struct Checker {
 const U *g; int u; std::vector<int> candidates; std::vector<U> colours,compat,answers;
 int64_t nodes=0,limit; std::chrono::steady_clock::time_point end;
 void dfs(U avail,int need,U left,U row){
  if(++nodes>limit || std::chrono::steady_clock::now()>end)throw std::runtime_error("LIMIT");
  if(need==0){if(left==0)answers.push_back(row);return;}
  if(__builtin_popcountll(avail)<need)return;
  U possible=0;for(U t=avail;t;t&=t-1)possible|=colours[__builtin_ctzll(t)];
  if(left&~possible)return;
  while(avail){int j=__builtin_ctzll(avail);avail&=avail-1;
   if(!(colours[j]&~left))dfs(avail&compat[j],need-1,left^colours[j],row|(U(1)<<candidates[j]));
  }
 }
 void run(){
  U missing=127;for(U t=g[u];t;t&=t-1)missing&=~(g[__builtin_ctzll(t)]&127);
  for(int v=7;v<49;v++)if(v!=u && !(g[0]>>v&1) && !(g[v]&127&~missing)){
   bool ok=true;for(U t=g[u];t;t&=t-1)if(g[v]&g[__builtin_ctzll(t)]){ok=false;break;}
   if(ok){candidates.push_back(v);colours.push_back(g[v]&127);}
  }
  for(int v:candidates){U mask=0;for(size_t j=0;j<candidates.size();j++)if(v!=candidates[j] && !(g[v]&g[candidates[j]]))mask|=U(1)<<j;compat.push_back(mask);}
  dfs((U(1)<<candidates.size())-1,7-__builtin_popcountll(g[u]),missing,0);
 }
};
extern "C" int verify_domain(const U*g,int u,const U*expected,int n,int64_t limit,double seconds,int64_t*out_nodes,int64_t*out_rows){
 if(u<7||u>=49||n<0||limit<0||seconds<0)return -2;
 Checker c;c.g=g;c.u=u;c.limit=limit;c.end=std::chrono::steady_clock::now()+std::chrono::duration_cast<std::chrono::steady_clock::duration>(std::chrono::duration<double>(seconds));
 try{c.run();}catch(...){*out_nodes=c.nodes;*out_rows=c.answers.size();return -1;}
 *out_nodes=c.nodes;*out_rows=c.answers.size();std::sort(c.answers.begin(),c.answers.end());
 std::vector<U> supplied(expected,expected+n);std::sort(supplied.begin(),supplied.end());
 return c.answers==supplied ? 1:0;
}
