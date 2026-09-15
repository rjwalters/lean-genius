#include <algorithm>
#include <array>
#include <cstdint>
#include <cmath>
#include <functional>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
#include <time.h>
#ifdef __APPLE__
#include <mach/mach_time.h>
#endif
using U=uint64_t;using M=uint16_t;
static int pc(U x){return __builtin_popcountll(x);}
static std::vector<int> bits(U x){std::vector<int>v;while(x){int u=__builtin_ctzll(x);x&=x-1;v.push_back(u);}return v;}
extern "C" double projection_now(){
#ifdef __APPLE__
 static const mach_timebase_info_data_t s=[](){mach_timebase_info_data_t q;mach_timebase_info(&q);return q;}();return double(mach_absolute_time())*double(s.numer)/double(s.denom)*1e-9;
#else
 timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;
#endif
}
struct Limit{};
struct Branch{int family;int kind;int value;}; // 0 child, 1 capacity, 2 common-neighbour
struct Node{int depth;std::vector<Branch>branches;};
struct Checker{
 std::array<U,49>g{};std::array<std::vector<M>,21>fs;
 std::array<int,14>capacity{},used{};std::array<int,21>order{};std::array<M,21>assigned{},witness{};std::array<bool,21>present{};
 std::vector<Node>tree;int cap,empty=-1;double deadline;std::string status="UNKNOWN";
 Checker(const U*input,int c,double d):cap(c),deadline(d){std::copy(input,input+49,g.begin());}
 void clockcheck(){if(projection_now()>deadline)throw Limit();}
 void require(bool b){if(!b)throw std::invalid_argument("invalid H7 a6 host graph");}
 void validate(){
  require(cap>=0&&cap<=1000000&&std::isfinite(deadline));
  const U all=(U(1)<<49)-1;
  for(int u=0;u<49;++u){require(!(g[u]&~all)&&!(g[u]>>u&1));for(int v:bits(g[u]))require(g[v]>>u&1);}
  for(int h=0;h<7;++h)require(pc(g[h])==8&&!(g[h]&127));
  std::array<int,128>supports{};
  for(int s=7;s<21;++s){require(pc(g[s]&127)==1);require(pc(g[s])==4||pc(g[s])==5);++supports[g[s]&127];capacity[s-7]=7-pc(g[s]);}
  for(int h=0;h<7;++h)require(supports[1<<h]==2);
  U singleton_mask=((U(1)<<21)-1)^127,empty_mask=((U(1)<<49)-1)^((U(1)<<42)-1);
  for(int s=7;s<21;++s){int ec=pc(g[s]&empty_mask);require(ec==1||ec==2);require(pc(g[s]&singleton_mask)==5-2*ec);}
  int mixed=0;for(int h=0;h<7;++h){std::vector<int>ec;for(int s=7;s<21;++s)if((g[s]&127)==U(1<<h))ec.push_back(pc(g[s]&empty_mask));std::sort(ec.begin(),ec.end());if(ec==std::vector<int>{1,2})++mixed;else require(ec==std::vector<int>{2,2});}require(mixed==3);
  U active=((U(1)<<42)-1)^127;int pair_demand=0;
  for(int p=21;p<42;++p){require(pc(g[p]&127)==2&&!(g[p]&active));require(pc(g[p])==2||pc(g[p])==3);++supports[g[p]&127];pair_demand+=7-2*pc(g[p]);}require(pair_demand==39);
  for(int a=0;a<7;++a)for(int b=a+1;b<7;++b)require(supports[(1<<a)|(1<<b)]==1);
  int total=0;for(int x:capacity)total+=x;require(total==39);
  for(int e=42;e<49;++e){require(!(g[e]&127)&&pc(g[e])==7);for(int h=0;h<7;++h)require(pc(g[e]&g[h])==1);}
  for(int u=0;u<49;++u)for(int v=0;v<u;++v)require(pc(g[u]&g[v])<=1);
 }
 bool matching(int left,const std::array<int,7>&adj){
  if(!left)return true;int h=__builtin_ctz(unsigned(left));int vs=adj[h]&left;
  while(vs){int v=__builtin_ctz(unsigned(vs));vs&=vs-1;if(matching(left^(1<<h)^(1<<v),adj))return true;}return false;
 }
 void buildfamilies(){
  for(int p=21;p<42;++p){clockcheck();int demand=7-2*pc(g[p]);std::vector<int>cand;U blocked=0;
   for(int w:bits(g[p]))blocked|=g[w];for(int s=7;s<21;++s)if(!(g[s]&blocked))cand.push_back(s);
   auto add=[&](M family){U ban=blocked;int usedhigh=0;for(int s:bits(family)){ban|=g[s+7];usedhigh|=int(g[s+7]&127);}require(pc(usedhigh)==demand);
    int left=127^usedhigh;std::array<int,7>adj{};
    for(int q=21;q<42;++q)if(q!=p&&!(int(g[q]&127)&~left)&&!(g[q]&ban)){auto hs=bits(g[q]&127);adj[hs[0]]|=1<<hs[1];adj[hs[1]]|=1<<hs[0];}
    if(matching(left,adj))fs[p-21].push_back(family);
   };
   if(demand==1){for(int s:cand)add(M(1<<(s-7)));}
   else{require(demand==3);for(size_t i=0;i<cand.size();++i)for(size_t j=i+1;j<cand.size();++j){int a=cand[i],b=cand[j];if(g[a]&g[b])continue;for(size_t k=j+1;k<cand.size();++k){int c=cand[k];if(!(g[a]&g[c])&&!(g[b]&g[c]))add(M((1<<(a-7))|(1<<(b-7))|(1<<(c-7))));}}}
   if(fs[p-21].empty()&&empty<0)empty=p;
  }
 }
 bool visit(int depth){
  clockcheck();if(int(tree.size())>=cap)throw Limit();int index=int(tree.size());tree.push_back(Node{depth,{}});
  if(depth==21){require(used==capacity);witness=assigned;return true;}
  int pi=order[depth],p=pi+21;
  for(size_t i=0;i<fs[pi].size();++i){M f=fs[pi][i];int over=-1;for(int s:bits(f))if(used[s]>=capacity[s]){over=s;break;}
   if(over>=0){tree[index].branches.push_back(Branch{int(i),1,over});continue;}
   int conflict=-1;for(int d=0;d<depth;++d){int qi=order[d];if(pc(f&assigned[qi])+pc(g[p]&g[qi+21])>1){conflict=qi+21;break;}}
   if(conflict>=0){tree[index].branches.push_back(Branch{int(i),2,conflict});continue;}
   assigned[pi]=f;present[pi]=true;for(int s:bits(f))++used[s];int child=int(tree.size());bool positive=visit(depth+1);tree[index].branches.push_back(Branch{int(i),0,child});for(int s:bits(f))--used[s];present[pi]=false;assigned[pi]=0;if(positive)return true;
  }
  return false;
 }
 void run(){validate();try{clockcheck();buildfamilies();if(empty>=0){status="EMPTY_FAMILY";return;}for(int i=0;i<21;++i)order[i]=i;std::sort(order.begin(),order.end(),[&](int a,int b){return fs[a].size()!=fs[b].size()?fs[a].size()<fs[b].size():a<b;});status=visit(0)?"FEASIBLE_PROJECTION":"INFEASIBLE_PROJECTION";}catch(const Limit&){status="UNKNOWN";}}
 template<class T>static void list(std::ostream&o,const T&xs){o<<'[';bool first=true;for(auto x:xs){if(!first)o<<',';first=false;o<<+x;}o<<']';}
 std::string json(){std::ostringstream o;o<<"{\"status\":\""<<status<<"\",\"nodes\":"<<tree.size();
  if(status=="EMPTY_FAMILY"){o<<",\"pair_vertex\":"<<empty<<'}';return o.str();}
  if(status=="UNKNOWN"){o<<'}';return o.str();}
  o<<",\"families\":{";for(int i=0;i<21;++i){if(i)o<<',';o<<'"'<<i+21<<"\":";list(o,fs[i]);}o<<"},\"capacity\":";list(o,capacity);o<<",\"order\":[";for(int i=0;i<21;++i){if(i)o<<',';o<<order[i]+21;}o<<']';
  if(status=="FEASIBLE_PROJECTION"){o<<",\"witness\":{";for(int i=0;i<21;++i){if(i)o<<',';o<<'"'<<i+21<<"\":"<<witness[i];}o<<"},\"tree\":null}";return o.str();}
  o<<",\"witness\":null,\"tree\":[";for(size_t i=0;i<tree.size();++i){if(i)o<<',';auto&n=tree[i];o<<"{\"depth\":"<<n.depth<<",\"branches\":[";for(size_t j=0;j<n.branches.size();++j){if(j)o<<',';auto b=n.branches[j];o<<"{\"family\":"<<b.family<<",\""<<(b.kind==0?"child":b.kind==1?"capacity_reject":"common_neighbour_reject")<<"\":"<<b.value<<'}';}o<<"]}";}o<<"]}";return o.str();
 }
};
extern "C" const char* check_projection(const U*g,int cap,double deadline){static thread_local std::string out;try{if(!g)throw std::invalid_argument("null graph");Checker c(g,cap,deadline);c.run();out=c.json();}catch(const std::exception&e){out="{\"status\":\"INVALID\"}";}return out.c_str();}
