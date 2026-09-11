#include <cstdint>
#include <vector>
#include <functional>
#include <chrono>
using U=uint64_t;
static bool exists(U*g,int s,int&nodes){
 unsigned left=127;
 for(U ns=g[s];ns;ns&=ns-1)left^=unsigned(g[__builtin_ctzll(ns)]&127);
 std::vector<int> choices;
 for(int v=21;v<42;v++){
  if(g[s]>>v&1)continue;
  if((g[v]&127)&~left)continue;
  bool ok=true;
  for(U ns=g[s];ns;ns&=ns-1)if(g[v]&g[__builtin_ctzll(ns)]&~(U(1)<<s)){ok=false;break;}
  if(ok)choices.push_back(v);
 }
 std::function<bool(int,int,unsigned,U)> dfs=[&](int at,int need,unsigned remaining,U neighbour_union){
  if(++nodes>100000)throw 1;
  if(!need)return remaining==0;
  if(int(choices.size())-at<need)return false;
  for(int j=at;j<int(choices.size());j++){
   int v=choices[j];unsigned colours=g[v]&127;
   if(colours&~remaining || (g[v]&neighbour_union))continue;
   if(dfs(j+1,need-1,remaining^colours,neighbour_union|g[v]))return true;
  }
  return false;
 };
 return dfs(0,7-__builtin_popcountll(g[s]),left,0);
}
extern "C" int verify_batch(const U*base,const uint32_t*records,const uint8_t*codes,int count,double seconds,int*bad,uint64_t*total,int*maxnodes){
 auto deadline=std::chrono::steady_clock::now()+std::chrono::duration<double>(seconds);
 for(int r=0;r<count;r++){
  if(std::chrono::steady_clock::now()>deadline){*bad=r;return -2;}
  U g[49]={};auto add=[&](int a,int b){g[a]|=U(1)<<b;g[b]|=U(1)<<a;};auto ren=[](int a){return a<7?a+42:a;};
  for(int a=0;a<21;a++)for(int b=0;b<a;b++)if(base[a]>>b&1)add(ren(a),ren(b));
  const uint32_t* rec=records+14*r;
  for(int h=0;h<7;h++){if(rec[h]>=7){*bad=r;return -3;}add(h,14+h);add(h,7+rec[h]);}
  int k=0;
  for(int a=0;a<7;a++)for(int b=a+1;b<7;b++,k++){
   add(21+k,a);add(21+k,b);
   for(int e=0;e<7;e++)if(rec[7+e]>>k&1)add(21+k,42+e);
  }
  int nodes=0;bool ok=true;
  try{
   if(codes[r]=='.'){for(int s=7;s<21;s++)if(!exists(g,s,nodes)){ok=false;break;}}
   else{int s=codes[r]-'A'+7;ok=s>=7&&s<=20&&!exists(g,s,nodes);}
  }catch(int){*bad=r;return -1;}
  *total+=nodes;if(nodes>*maxnodes)*maxnodes=nodes;
  if(!ok){*bad=r;return 0;}
 }
 return 1;
}
