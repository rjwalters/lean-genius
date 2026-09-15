#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <functional>
#include <sstream>
#include <vector>
using U=uint64_t;
static int pc(U m){return __builtin_popcountll(m);}
static std::vector<int> bits(U m){std::vector<int> v;while(m){int i=__builtin_ctzll(m);v.push_back(i);m&=m-1;}return v;}
struct Limit{};
// Valid-a7-prefix premise is a caller obligation. This validates basic layout only.
extern "C" const char* pair_rows(const U*input,int u,int future_host,int cap,double seconds){
 static thread_local std::string result;
 std::array<U,49> g{},sup{};std::copy(input,input+49,g.begin());
 auto invalid=[&](){result="{\"status\":\"INVALID_INPUT\"}";return result.c_str();};
 if(u<21||u>=42||cap<0||!std::isfinite(seconds)||seconds<0||seconds>86400||(future_host!=0&&future_host!=1))return invalid();
 U whole=(U(1)<<49)-1,active=((U(1)<<42)-1)^127,empty=whole^((U(1)<<42)-1);
 for(int v=0;v<49;v++){
  if((g[v]&~whole)||(g[v]>>v&1))return invalid();
  for(int w:bits(g[v]))if(!(g[w]>>v&1))return invalid();
  sup[v]=g[v]&127;
 }
 int hosted=pc(g[u]&empty);
 if(pc(sup[u])!=2||(g[u]&active)||hosted>1||pc(g[u])!=2+hosted)return invalid();
 for(int v=7;v<42;v++)if(pc(sup[v])<1||pc(sup[v])>2)return invalid();
 for(int v=42;v<49;v++)if(sup[v])return invalid();
 std::array<std::vector<int>,7>buckets;
 for(int v=7;v<42;v++)if(v!=u&&!(g[u]>>v&1)){
  bool good=true;for(int w:bits(g[u]))if(g[v]&g[w]){good=false;break;}
  if(good)for(int h:bits(sup[v]))buckets[h].push_back(v);
 }
 auto deadline=std::chrono::steady_clock::now()+std::chrono::duration_cast<std::chrono::steady_clock::duration>(std::chrono::duration<double>(seconds));
 int64_t nodes=0;bool complete=true;std::vector<U> out;
 auto tick=[&](){if(++nodes>cap||std::chrono::steady_clock::now()>deadline)throw Limit{};};
 std::function<void(U,int,U,U)> dfs=[&](U left,int need,U row,U neighbours){
  tick();if(!need){if(!left)out.push_back(row);return;}
  if(pc(left)<need||pc(left)>2*need)return;
  int h=__builtin_ctzll(left);
  for(int v:buckets[h])if(!(sup[v]&~left)&&!(g[v]&neighbours))dfs(left^sup[v],need-1,row|(U(1)<<v),neighbours|g[v]);
 };
 try{if(hosted||future_host)dfs(127,4,0,0);if(!hosted)dfs(127,5,0,0);}catch(const Limit&){complete=false;}
 std::ostringstream s;s<<"{\"status\":\""<<(complete?"COMPLETE":"UNKNOWN")<<"\",\"nodes\":"<<nodes<<",\"rows\":[";
 bool first=true;for(U row:out){if(!first)s<<',';first=false;s<<row;}s<<"]}";result=s.str();return result.c_str();
}
