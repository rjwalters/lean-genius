#include "projection.cpp"
#include <cassert>
#include <iostream>
static void setup(Checker&c){
 const int triples[9][3]={{0,1,4},{1,2,5},{2,3,6},{4,5,8},{5,6,9},{6,7,10},{8,9,12},{10,11,0},{12,13,2}};
 const int singles[12]={0,1,3,4,7,8,9,10,11,12,13,13};
 c.capacity={3,3,3,2,3,3,3,2,3,3,3,2,3,3};
 for(int p=0;p<21;++p)c.order[p]=p;
 for(int p=0;p<9;++p){M m=0;for(int s:triples[p])m|=1<<s;c.fs[p].push_back(m);}
 for(int p=9;p<21;++p)c.fs[p].push_back(M(1<<singles[p-9]));
}
int main(){
 U graph[49]{};Checker positive(graph,10000,projection_now()+10);setup(positive);
 assert(positive.visit(0));positive.status="FEASIBLE_PROJECTION";assert(positive.tree.size()==22);
 std::array<int,14>counts{};for(M f:positive.witness)for(int s:bits(f))++counts[s];assert(counts==positive.capacity);
 for(int p=0;p<21;++p)for(int q=0;q<p;++q)assert(pc(positive.witness[p]&positive.witness[q])<=1);
 Checker negative(graph,10000,projection_now()+10);setup(negative);negative.g[21]=1;negative.g[22]=1;assert(!negative.visit(0));assert(negative.tree.size()==2);
 Checker capped(graph,1,projection_now()+10);setup(capped);bool limit=false;try{capped.visit(0);}catch(const Limit&){limit=true;}assert(limit&&capped.tree.size()==1);
 std::array<int,7>adj{};adj[0]=2;adj[1]=1;adj[2]=8;adj[3]=4;adj[4]=32;adj[5]=16;assert(positive.matching(63,adj));adj.fill(0);for(int v=1;v<6;++v){adj[0]|=1<<v;adj[v]=1;}assert(!positive.matching(63,adj));
 std::cout<<"{\"status\":\"PASS_SYNTHETIC_ENGINE_UNITS\",\"positive\":"<<positive.json()<<",\"negative_nodes\":2,\"cap_nodes\":1,\"scope\":\"Synthetic choice-engine state only; not a valid H7 graph fixture.\"}\n";
}
