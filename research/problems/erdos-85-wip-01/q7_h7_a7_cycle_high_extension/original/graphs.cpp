#include <cstdint>
#include <ctime>
extern "C" int verify_graphs(const uint64_t* base,const uint32_t* records,int n) {
  for(int r=0;r<n;r++) {
    uint64_t g[49]={};
    auto add=[&](int a,int b){g[a]|=1ULL<<b;g[b]|=1ULL<<a;};
    auto ren=[](int a){return a<7?a+42:a;};
    for(int a=0;a<21;a++)for(int b=0;b<a;b++)if(base[a]>>b&1)add(ren(a),ren(b));
    const uint32_t* rec=records+14*r;
    unsigned seen=0;
    for(int i=0;i<7;i++) {
      if(rec[i]>=7 || (seen>>rec[i]&1))return -1;
      seen|=1U<<rec[i];add(i,14+i);add(i,7+rec[i]);
    }
    int k=0;
    for(int a=0;a<7;a++)for(int b=a+1;b<7;b++,k++) {
      add(21+k,a);add(21+k,b);
      for(int e=0;e<7;e++)if(rec[7+e]>>k&1)add(21+k,42+e);
    }
    for(int a=0;a<49;a++)for(int b=0;b<a;b++)if(__builtin_popcountll(g[a]&g[b])>1)return -2;
    for(int h=0;h<7;h++)if(__builtin_popcountll(g[h])!=8)return -3;
    for(int e=42;e<49;e++) {
      if(__builtin_popcountll(g[e])!=7)return -4;
      for(int h=0;h<7;h++)if(__builtin_popcountll(g[e]&g[h])!=1)return -5;
    }
    for(int s=7;s<21;s++)if(__builtin_popcountll(g[s])!=(s<14?4:5))return -6;
  }
  return 1;
}
