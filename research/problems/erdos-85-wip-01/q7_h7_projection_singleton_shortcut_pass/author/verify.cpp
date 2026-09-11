#include <cstdint>
#include <chrono>
using U=uint64_t;
static int pi(int a,int b){if(a>b){int t=a;a=b;b=t;}int n=0;for(int x=0;x<7;x++)for(int y=x+1;y<7;y++,n++)if(x==a&&y==b)return 21+n;return -1;}
static bool row(U*g,int s,int left,U chosen,int&nodes){
 ++nodes;
 if(!left){U ns=g[s]|chosen;if(__builtin_popcountll(ns)!=7)return false;for(U a=ns;a;a&=a-1){int x=__builtin_ctzll(a);for(U b=a&(a-1);b;b&=b-1){int y=__builtin_ctzll(b);if(g[x]&g[y]&~(U(1)<<s))return false;}}return true;}
 int a=__builtin_ctz((unsigned)left);left^=1<<a;
 for(int b=a+1;b<7;b++)if(left>>b&1)if(row(g,s,left^(1<<b),chosen|(U(1)<<pi(a,b)),nodes))return true;
 return false;
}
static bool exists(U*g,int s,int&nodes){int left=0;for(int h=0;h<7;h++)if(!(g[s]&g[h]))left|=1<<h;return row(g,s,left,0,nodes);}
extern "C" int verify_graph(U*g,int code){int nodes=0;if(code=='.'){for(int s=7;s<21;s++)if(!exists(g,s,nodes))return 0;}else{int s=code-'A'+7;if(s<7||s>20||exists(g,s,nodes))return 0;}return nodes<100000;}
extern "C" int verify_batch(U*base,uint32_t*records,uint8_t*codes,int count,double seconds,int*bad){
 auto deadline=std::chrono::steady_clock::now()+std::chrono::duration<double>(seconds);
 for(int k=0;k<count;k++){
  if(std::chrono::steady_clock::now()>deadline){*bad=k;return -2;}
  U g[49]={};auto edge=[&](int u,int v){g[u]|=U(1)<<v;g[v]|=U(1)<<u;};
  for(int u=0;u<21;u++)for(U m=base[u];m;m&=m-1){int v=__builtin_ctzll(m);if(u<v)edge(u<7?42+u:u,v<7?42+v:v);}
  uint32_t*r=records+14*k;
  for(int h=0;h<7;h++){edge(h,14+h);edge(h,7+r[h]);}
  for(int a=0;a<7;a++)for(int b=a+1;b<7;b++){int p=pi(a,b);edge(p,a);edge(p,b);}
  for(int e=0;e<7;e++)for(uint32_t m=r[7+e];m;m&=m-1)edge(42+e,21+__builtin_ctz(m));
  if(!verify_graph(g,codes[k])){*bad=k;return 0;}
 }
 return 1;
}
