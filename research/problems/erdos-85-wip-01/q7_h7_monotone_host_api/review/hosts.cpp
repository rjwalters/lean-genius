#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <functional>
#include <map>
#include <sstream>
#include <stdexcept>
#include <vector>
using U=uint64_t;
static int pc(U x){return __builtin_popcountll(x);}
static std::vector<int> bits(U x){std::vector<int> v;while(x){int i=__builtin_ctzll(x);v.push_back(i);x&=x-1;}return v;}
struct Limit{};
struct Prune{int depth,s;std::array<U,7> chosen;};
struct Search{
 std::array<U,49> g{},support{},host{},forbidden{};
 std::array<int,128> pv{};std::vector<int>E,S,order;
 std::array<std::vector<U>,7>options;std::array<std::vector<U>,49>rows;
 std::array<U,7>chosen{};std::vector<std::array<U,7>>solutions;std::vector<Prune>prunes;
 int64_t nodes=0;int cap;bool complete=true;const U*fixed;
 std::chrono::steady_clock::time_point deadline;
 Search(const U*input,int limit,double seconds,const U*restrict_to):cap(limit),fixed(restrict_to){
  if(!std::isfinite(seconds)||std::abs(seconds)>86400)throw std::invalid_argument("invalid duration");
  std::copy(input,input+49,g.begin());
  deadline=std::chrono::steady_clock::now()+std::chrono::duration_cast<std::chrono::steady_clock::duration>(std::chrono::duration<double>(seconds));
 }
 void require(bool ok){if(!ok)throw std::invalid_argument("invalid base");}
 void tick(){if(++nodes>cap || std::chrono::steady_clock::now()>deadline)throw Limit{};}
 void validate(){
  require(cap>=0);U whole=(U(1)<<49)-1,sm=0,em=0;std::map<U,int>counts,wanted;
  for(int u=0;u<49;u++){
   require(!(g[u]&~whole) && !(g[u]>>u&1));support[u]=g[u]&127;
   for(int v:bits(g[u]))require(g[v]>>u&1);
  }
  for(int h=0;h<7;h++){require(pc(g[h])==8&&!support[h]);wanted[U(1)<<h]=2;for(int j=0;j<h;j++)wanted[(U(1)<<h)|(U(1)<<j)]=1;}
  for(int u=7;u<49;u++){
   if(!support[u]){E.push_back(u);em|=U(1)<<u;}
   else{counts[support[u]]++;if(pc(support[u])==1){S.push_back(u);sm|=U(1)<<u;}else{require(pc(support[u])==2&&g[u]==support[u]);pv[support[u]]=u;}}
  }
  require(E.size()==7&&S.size()==14&&counts==wanted);
  for(int u=0;u<49;u++)for(int v=0;v<u;v++)require(pc(g[u]&g[v])<=1);
  for(int e:E){int d=pc(g[e]&em);require(d<=3&&pc(g[e]&sm)==7-2*d);}
  for(int s:S){int d=pc(g[s]&em);require((d==1||d==2)&&pc(g[s]&sm)==5-2*d);}
  int mixed=0;
  for(int h=0;h<7;h++){
   std::vector<int>ds;for(int s:S)if(support[s]==(U(1)<<h))ds.push_back(pc(g[s]&em));std::sort(ds.begin(),ds.end());
   if(ds==std::vector<int>({1,2})){mixed++;for(int s:S)if(support[s]==(U(1)<<h))for(int t:bits(g[s]&sm))require(support[t]!=support[s]);}
   else require(ds==std::vector<int>({2,2}));
  }
  require(mixed==3||mixed==7);
  for(int s:S){
   for(int e:bits(g[s]&em))forbidden[s]|=g[e]&em;
   for(int t:bits(g[s]&sm))forbidden[s]|=g[t]&em;
  }
 }
 std::vector<U> matchings(U left){
  std::vector<U>out;
  std::function<void(U,U)>rec=[&](U unused,U m){
   tick();if(!unused){out.push_back(m);return;}
   int a=__builtin_ctzll(unused);unused^=U(1)<<a;
   for(int b:bits(unused)){int v=pv[(U(1)<<a)|(U(1)<<b)];require(v>=7);rec(unused^(U(1)<<b),m|(U(1)<<v));}
  };rec(left,0);return out;
 }
 U missing(int u){U used=0;for(int v:bits(g[u])){require(!(used&support[v]));used|=support[v];}return 127^used;}
 void prepare(){
  U em=0;for(int e:E)em|=U(1)<<e;
  for(int i=0;i<7;i++){
   U left=missing(E[i]);require(pc(left)==2*pc(g[E[i]]&em));options[i]=matchings(left);
   if(fixed){require(std::find(options[i].begin(),options[i].end(),fixed[i])!=options[i].end());options[i]={fixed[i]};}
   order.push_back(i);
  }
  for(int s:S){U left=missing(s);require(pc(left)==2*(7-pc(g[s])));rows[s]=matchings(left);}
  std::stable_sort(order.begin(),order.end(),[&](int a,int b){return pc(g[E[a]]&em)>pc(g[E[b]]&em);});
  std::stable_sort(S.begin(),S.end(),[&](int a,int b){return rows[a].size()<rows[b].size();});
 }
 int empty_singleton(){
  for(int s:S){
   bool found=false;
   for(U row:rows[s]){
    tick();U seen=0;bool good=true;
    for(U todo=row;todo;todo&=todo-1){int p=__builtin_ctzll(todo);if(host[p]&(forbidden[s]|seen)){good=false;break;}seen|=host[p];}
    if(good){found=true;break;}
   }
   if(!found)return s;
  }
  return -1;
 }
 void visit(int depth,U used){
  tick();
  if(depth){int s=empty_singleton();if(s>=0){prunes.push_back({depth,s,chosen});return;}}
  if(depth==7){solutions.push_back(chosen);return;}
  int i=order[depth];
  for(U m:options[i]){
   tick();if(m&used)continue;
   chosen[i]=m;for(int p:bits(m))host[p]=U(1)<<E[i];
   visit(depth+1,used|m);
   for(int p:bits(m))host[p]=0;chosen[i]=0;
  }
 }
 void run(){validate();try{prepare();visit(0,0);}catch(const Limit&){complete=false;}}
 static void masks(std::ostringstream&o,const std::array<U,7>&ms){o<<'[';for(int i=0;i<7;i++){if(i)o<<',';o<<ms[i];}o<<']';}
 std::string json(){
  std::ostringstream o;o<<"{\"status\":\""<<(complete?"COMPLETE":"UNKNOWN")<<"\",\"nodes\":"<<nodes<<",\"empty_vertices\":[";
  for(int i=0;i<7;i++){if(i)o<<',';o<<E[i];}o<<"],\"order\":[";for(size_t i=0;i<order.size();i++){if(i)o<<',';o<<order[i];}
  o<<"],\"solutions\":[";bool first=true;for(auto&ms:solutions){if(!first)o<<',';first=false;masks(o,ms);}o<<"],\"prunes\":[";
  first=true;for(auto&p:prunes){if(!first)o<<',';first=false;o<<"{\"depth\":"<<p.depth<<",\"singleton\":"<<p.s<<",\"chosen\":";masks(o,p.chosen);o<<'}';}
  o<<"]}";return o.str();
 }
};
static const char* invoke(const U*g,int cap,double seconds,const U*fixed){
 static thread_local std::string result;
 try{Search s(g,cap,seconds,fixed);s.run();result=s.json();}catch(const std::exception&){result="{\"status\":\"INVALID_INPUT\"}";}
 return result.c_str();
}
extern "C" const char* enumerate_hosts(const U*g,int cap,double seconds){return invoke(g,cap,seconds,nullptr);}
extern "C" const char* check_fixed_hosts(const U*g,const U*fixed,int cap,double seconds){return invoke(g,cap,seconds,fixed);}
