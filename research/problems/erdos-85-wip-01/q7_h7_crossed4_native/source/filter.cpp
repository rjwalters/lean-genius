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
 std::array<U,49> g{};U hosts=0;std::vector<int> outside;std::array<int,49> host{};std::array<U,49> masks{};
 std::array<std::vector<U>,49> initial,domains;std::array<bool,49> ready{};std::vector<Event> events;
 int64_t nodes=0;int max_nodes,empty=-1;double deadline;std::string status="ARC_CONSISTENT",stage="GENERATION";
 Checker(const U *input,int cap,double end):max_nodes(cap),deadline(end){std::copy(input,input+49,g.begin());}
 void tick(){++nodes;if(nodes>max_nodes || native_now()>deadline)throw Limit{};}
 void require(bool b){if(!b)throw std::invalid_argument("invalid complete H7 host graph");}
 void validate(){
  U whole=(U(1)<<49)-1;
  for(int u=0;u<49;++u){require(!(g[u]&~whole));require(!(g[u]&(U(1)<<u)));for(int v:bits(g[u]))require(g[v]&(U(1)<<u));}
  for(int c=0;c<7;++c)require(pc(g[c])==8 && !(g[c]&127));
  hosts=g[0];require(pc(hosts)==8);
  for(int u=7;u<49;++u)if(!(hosts&(U(1)<<u)))outside.push_back(u);
  require(outside.size()==34);
  for(int u=0;u<49;++u)for(int v=0;v<u;++v)require(pc(g[u]&g[v])<=1);
  for(int h:bits(hosts))require(pc(g[h])==7 && pc(g[h]&hosts)==1);
  for(int u:outside){require(pc(g[u]&hosts)==1);host[u]=__builtin_ctzll(g[u]&hosts);require((g[u]&~U(127))==(U(1)<<host[u]));masks[u]=g[u]&127;}
 }
 void run(){
  validate();
  try{
   for(int u:outside){
    U missing=127;for(int v:bits(g[u]))if(v>=7)missing&=~(g[v]&127);
    int need=7-pc(g[u]);std::map<int,std::vector<int>> options;
    for(int v:outside){
     if(u==v || (masks[v]&missing)!=masks[v])continue;
     bool legal=true;for(int w:bits(g[u]))if(g[v]&g[w]){legal=false;break;}
     if(legal)options[host[v]].push_back(v);
    }
    std::vector<std::pair<int,std::vector<int>>> groups(options.begin(),options.end());
    std::sort(groups.begin(),groups.end(),[](const auto&a,const auto&b){return a.second.size()!=b.second.size()?a.second.size()<b.second.size():a.first<b.first;});
    std::vector<U> answers;
    std::function<void(int,U,int,U)> dfs=[&](int i,U left,int n,U selected){
     tick();if(n==0){if(left==0)answers.push_back(selected);return;}
     int remaining=int(groups.size())-i;if(remaining<n)return;
     if(remaining>n)dfs(i+1,left,n,selected);
     for(int v:groups[i].second)if((masks[v]&left)==masks[v])dfs(i+1,left^masks[v],n-1,selected|(U(1)<<v));
    };
    dfs(0,missing,need,0);initial[u]=std::move(answers);ready[u]=true;
    if(initial[u].empty()){status="INFEASIBLE_LOCAL";empty=u;return;}
   }
   domains=initial;stage="ARC";bool changed=true;
   while(changed){changed=false;
    for(int u:outside)for(int v:outside)if(u!=v){
     int limit=1-pc(g[u]&g[v]);std::vector<U> removed;
     for(U a:domains[u]){
      bool found=false;
      for(U b:domains[v]){tick();if(((a>>v)&1)==((b>>u)&1) && pc(a&b)<=limit){found=true;break;}}
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
 static void list(std::ostringstream&o,const std::vector<U>&v){o<<'[';bool first=true;for(U x:v){if(!first)o<<',';first=false;o<<x;}o<<']';}
 void mapping(std::ostringstream&o,const std::array<std::vector<U>,49>&a){o<<'{';bool first=true;for(int u:outside)if(ready[u]){if(!first)o<<',';first=false;o<<'"'<<u<<"\":";list(o,a[u]);}o<<'}';}
 std::string json(){
  std::ostringstream o;o<<"{\"status\":\""<<status<<"\",\"nodes\":"<<nodes<<",\"initial\":";mapping(o,initial);o<<",\"events\":[";
  bool first=true;for(const auto&e:events){if(!first)o<<',';first=false;o<<"{\"vertex\":"<<e.u<<",\"against\":"<<e.v<<",\"removed\":";list(o,e.removed);o<<'}';}o<<']';
  if(status=="UNKNOWN")o<<",\"stage\":\""<<stage<<'"';
  if(empty>=0)o<<",\"empty_vertex\":"<<empty;
  if(status=="ARC_CONSISTENT"){o<<",\"remaining\":";mapping(o,domains);}
  o<<'}';return o.str();
 }
};
extern "C" const char* check_rows(const U* adjacency,int max_nodes,double deadline){
 static thread_local std::string result;
 try{Checker c(adjacency,max_nodes,deadline);c.run();result=c.json();}
 catch(const std::exception&){result="{\"status\":\"INVALID_INPUT\"}";}
 return result.c_str();
}
