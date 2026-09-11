#include <algorithm>
#include <array>
#include <cstdint>
#include <functional>
#include <map>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
#include <time.h>
#ifdef __APPLE__
#include <mach/mach_time.h>
#endif
using U=uint64_t;
static int pc(U x){return __builtin_popcountll(x);}
static std::vector<int> bits(U x){std::vector<int> v;while(x){int i=__builtin_ctzll(x);v.push_back(i);x&=x-1;}return v;}
extern "C" double native_now(){
#ifdef __APPLE__
 static const mach_timebase_info_data_t scale=[](){mach_timebase_info_data_t s;mach_timebase_info(&s);return s;}();
 return double(mach_absolute_time())*double(scale.numer)/double(scale.denom)*1e-9;
#else
 timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;
#endif
}
struct Limit{};
struct Event{int u,v;std::vector<U> removed;};
struct Checker{
 std::array<U,49> g{},support{};std::vector<int> active,empties;
 std::array<std::vector<U>,49> initial,domains;std::array<bool,49> ready{};std::vector<Event> events;
 int64_t nodes=0;int max_nodes,empty=-1,current=-1;double deadline;
 std::string status="ARC_FEASIBLE",stage="generation";
 Checker(const U*input,int cap,double end):max_nodes(cap),deadline(end){std::copy(input,input+49,g.begin());}
 void tick(){++nodes;if(nodes>max_nodes||native_now()>deadline)throw Limit{};}
 void require(bool b){if(!b)throw std::invalid_argument("invalid empty-first H7 graph");}
 void validate(){
  U whole=(U(1)<<49)-1,active_mask=0;
  for(int u=0;u<49;++u){require(!(g[u]&~whole));require(!(g[u]&(U(1)<<u)));for(int v:bits(g[u]))require(g[v]&(U(1)<<u));support[u]=g[u]&127;}
  for(int h=0;h<7;++h)require(pc(g[h])==8 && !support[h]);
  std::map<U,int> counts,wanted;
  for(int u=7;u<49;++u){if(support[u]){active.push_back(u);active_mask|=U(1)<<u;++counts[support[u]];}else empties.push_back(u);}
  require(active.size()==35 && empties.size()==7);
  for(int i=0;i<7;++i){wanted[U(1)<<i]=2;for(int j=0;j<i;++j)wanted[(U(1)<<i)|(U(1)<<j)]=1;}
  require(counts==wanted);
  for(int e:empties){require(pc(g[e])==7);for(int h=0;h<7;++h)require(pc(g[e]&g[h])==1);}
  U sm=0,em=0;for(int e:empties)em|=U(1)<<e;
  for(int u:active)if(pc(support[u])==1)sm|=U(1)<<u;
  for(int u:active){
   int n=7-pc(g[u]);
   if(pc(support[u])==2){require(!(g[u]&active_mask));require(n==4||n==5);}
   else{int ec=pc(g[u]&em);require(ec==1||ec==2);require(pc(g[u]&sm)==5-2*ec);require(n==2||n==3);
    }
  }
  int mixed=0;
  for(int h=0;h<7;h++){std::vector<int> ec;for(int u:bits(sm))if(support[u]==(U(1)<<h))ec.push_back(pc(g[u]&em));std::sort(ec.begin(),ec.end());
   if(ec==std::vector<int>({1,2})){++mixed;for(int u:bits(sm))if(support[u]==(U(1)<<h))for(int v:bits(g[u]&sm))require(support[u]!=support[v]);}
   else require(ec==std::vector<int>({2,2}));
  }
  require(mixed==3);
  for(int u=0;u<49;++u)for(int v=0;v<u;++v)require(pc(g[u]&g[v])<=1);
 }
 void run(){
  validate();
  try{
   for(int u:active){
    current=u;std::array<std::vector<int>,7>buckets;U used=0;for(int w:bits(g[u])){require(!(used&support[w]));used|=support[w];}
    for(int v:active)if(v!=u && !(g[u]>>v&1) && !(pc(support[u])==1 && pc(support[v])==1)){
     bool good=true;for(int w:bits(g[u]))if(g[v]&g[w]){good=false;break;}
     if(good)for(int h:bits(support[v]))buckets[h].push_back(v);
    }
    std::vector<U> answers;
    std::function<void(U,int,U,U)> dfs=[&](U left,int need,U row,U neighbours){
     tick();if(need==0){if(left==0)answers.push_back(row);return;}
     if(pc(left)<need||pc(left)>2*need)return;
     int h=__builtin_ctzll(left);
     for(int v:buckets[h])if(!(support[v]&~left) && !(g[v]&neighbours))dfs(left^support[v],need-1,row|(U(1)<<v),neighbours|g[v]);
    };
    dfs(127^used,7-pc(g[u]),0,0);initial[u]=std::move(answers);ready[u]=true;
   }
   for(int u:active)if(initial[u].empty()){status="INFEASIBLE_ROW";empty=u;return;}
   stage="arc";domains=initial;bool changed=true;
   while(changed){changed=false;
    for(int u:active)for(int v:active)if(u!=v){
     std::vector<U> removed;
     for(U a:domains[u]){
      bool found=false;
      for(U b:domains[v]){tick();if(((a>>v)&1)==((b>>u)&1) && pc((g[u]|a)&(g[v]|b))<=1){found=true;break;}}
      if(!found)removed.push_back(a);
     }
     if(!removed.empty()){
      std::vector<U> kept;for(U a:domains[u])if(std::find(removed.begin(),removed.end(),a)==removed.end())kept.push_back(a);
      domains[u]=std::move(kept);events.push_back({u,v,std::move(removed)});changed=true;
      if(domains[u].empty()){status="INFEASIBLE_ARC";empty=u;return;}
     }
    }
   }
  }catch(const Limit&){status="UNKNOWN";}
 }
 static void list(std::ostringstream&o,const std::vector<U>&xs){o<<'[';bool first=true;for(U x:xs){if(!first)o<<',';first=false;o<<x;}o<<']';}
 void mapping(std::ostringstream&o,const std::array<std::vector<U>,49>&a){o<<'{';bool first=true;for(int u:active)if(ready[u]){if(!first)o<<',';first=false;o<<'"'<<u<<"\":";list(o,a[u]);}o<<'}';}
 std::string json(){
  std::ostringstream o;o<<"{\"status\":\""<<status<<"\",\"nodes\":"<<nodes<<",\"initial\":";mapping(o,initial);
  if(status=="UNKNOWN"){o<<",\"stage\":\""<<stage<<'"';if(stage=="generation")o<<",\"vertex\":"<<current;}
  if(status=="INFEASIBLE_ROW"||status=="INFEASIBLE_ARC")o<<",\"empty_vertex\":"<<empty;
  if(stage=="arc"){
   o<<",\"events\":[";bool first=true;for(const auto&e:events){if(!first)o<<',';first=false;o<<"{\"vertex\":"<<e.u<<",\"against\":"<<e.v<<",\"removed\":";list(o,e.removed);o<<'}';}o<<']';
   if(status=="UNKNOWN"||status=="ARC_FEASIBLE"){o<<",\"remaining\":";mapping(o,domains);}
  }
  o<<'}';return o.str();
 }
};
extern "C" const char* check_rows(const U*adjacency,int max_nodes,double deadline){
 static thread_local std::string result;
 try{Checker c(adjacency,max_nodes,deadline);c.run();result=c.json();}
 catch(const std::exception&){result="{\"status\":\"INVALID_INPUT\"}";}
 return result.c_str();
}
