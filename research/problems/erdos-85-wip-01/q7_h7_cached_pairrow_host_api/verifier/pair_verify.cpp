// Independent increasing-vertex subset enumeration for pair-row endpoints.
// Input must be a valid a7 partial-host graph; caller establishes this premise.
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <vector>
using U=uint64_t;
static int pc(U x){return __builtin_popcountll(x);}
static int first(U x){return __builtin_ctzll(x);}
struct Cutoff {};

// Return 0 only for an exhaustively empty optimistic domain; 1 found, 2 cap,
// 3 basic input violation. Node count is returned separately.
extern "C" int pair_row_exists(const U*g,int u,int future,int cap,double seconds,U*nodes){
    *nodes=0;
    if(u<21||u>=42||(future!=0&&future!=1)||cap<0||!std::isfinite(seconds)||seconds<0||seconds>86400)return 3;
    U whole=(U(1)<<49)-1,A=((U(1)<<42)-1)^127,E=whole^((U(1)<<42)-1);
    for(int v=0;v<49;v++){
        if(g[v]&~whole||g[v]>>v&1)return 3;
        for(U m=g[v];m;m&=m-1)if(!(g[first(m)]>>v&1))return 3;
    }
    int hosted=pc(g[u]&E);
    if(pc(g[u]&127)!=2||hosted>1||pc(g[u])!=2+hosted||g[u]&A)return 3;
    for(int v=7;v<42;v++)if(pc(g[v]&127)<1||pc(g[v]&127)>2)return 3;
    for(int v=42;v<49;v++)if(g[v]&127)return 3;
    std::vector<int>eligible;
    for(int v=7;v<42;v++){
        if(v==u||g[u]>>v&1)continue;
        bool good=true;
        for(U m=g[u];m;m&=m-1)if(g[v]&g[first(m)]){good=false;break;}
        if(good)eligible.push_back(v);
    }
    bool allow4=hosted||future,allow5=!hosted;
    auto end=std::chrono::steady_clock::now()+std::chrono::duration_cast<std::chrono::steady_clock::duration>(std::chrono::duration<double>(seconds));
    auto visit=[&](auto&&self,int index,U support,std::array<int,5>chosen,int count)->bool{
        if(++*nodes>U(cap)||std::chrono::steady_clock::now()>end)throw Cutoff{};
        if(support==127)return (count==4&&allow4)||(count==5&&allow5);
        if(count==5)return false;
        int missing=7-pc(support);
        bool viable=false;
        for(int size=4;size<=5;size++)if((size==4?allow4:allow5)&&size>=count){
            int left=size-count;
            if(left<=missing&&missing<=2*left&&int(eligible.size())-index>=left)viable=true;
        }
        if(!viable)return false;
        for(int i=index;i<int(eligible.size());i++){
            int v=eligible[i];U sup=g[v]&127;
            if(sup&support)continue;
            bool good=true;
            for(int j=0;j<count;j++)if(g[v]&g[chosen[j]]){good=false;break;}
            if(!good)continue;
            chosen[count]=v;
            if(self(self,i+1,support|sup,chosen,count+1))return true;
        }
        return false;
    };
    try{return visit(visit,0,0,{},0)?1:0;}catch(const Cutoff&){return 2;}
}

// Singleton counterpart; every residual neighbor is a pair-support vertex.
extern "C" int singleton_row_exists(const U*g,int u,int cap,double seconds,U*nodes){
    *nodes=0;
    if(u<7||u>=21||cap<0||!std::isfinite(seconds)||seconds<0||seconds>86400)return 3;
    int need=7-pc(g[u]);if(need<2||need>3||pc(g[u]&127)!=1)return 3;
    U used=0;
    for(U m=g[u];m;m&=m-1){U s=g[first(m)]&127;if(used&s)return 3;used|=s;}
    std::vector<int>eligible;
    for(int v=21;v<42;v++){
        if(g[u]>>v&1)continue;
        U sup=g[v]&127;if(pc(sup)!=2||sup&used)continue;
        bool good=true;
        for(U m=g[u];m;m&=m-1)if(g[v]&g[first(m)]){good=false;break;}
        if(good)eligible.push_back(v);
    }
    auto end=std::chrono::steady_clock::now()+std::chrono::duration_cast<std::chrono::steady_clock::duration>(std::chrono::duration<double>(seconds));
    auto visit=[&](auto&&self,int index,U support,std::array<int,3>chosen,int count)->bool{
        if(++*nodes>U(cap)||std::chrono::steady_clock::now()>end)throw Cutoff{};
        if(count==need)return support==127;
        if(int(eligible.size())-index<need-count)return false;
        for(int i=index;i<int(eligible.size());i++){
            int v=eligible[i];U sup=g[v]&127;if(sup&support)continue;
            bool good=true;for(int j=0;j<count;j++)if(g[v]&g[chosen[j]]){good=false;break;}
            if(!good)continue;
            chosen[count]=v;
            if(self(self,i+1,support|sup,chosen,count+1))return true;
        }
        return false;
    };
    try{return visit(visit,0,used,{},0)?1:0;}catch(const Cutoff&){return 2;}
}
