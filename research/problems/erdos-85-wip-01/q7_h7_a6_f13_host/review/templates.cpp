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
extern "C" int verify_prefix_batch(U*base,int*E,U*chosen,int*codes,int count){
 for(int k=0;k<count;k++){
  U g[49];for(int u=0;u<49;u++)g[u]=base[u];
  for(int e=0;e<7;e++)for(U m=chosen[7*k+e];m;m&=m-1){int v=__builtin_ctzll(m);g[E[e]]|=U(1)<<v;g[v]|=U(1)<<E[e];}
  if(!verify_graph(g,codes[k]))return k+1;
 }
 return 0;
}
