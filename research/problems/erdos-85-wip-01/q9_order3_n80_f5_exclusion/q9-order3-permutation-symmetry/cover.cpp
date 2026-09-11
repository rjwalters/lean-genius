#include <algorithm>
#include <array>
#include <chrono>
#include <iostream>
#include <vector>
#include <cstdint>
#include <fstream>
using namespace std;
array<array<int,3>,6> ps;
int invp[6],comp[6][6],P[5][5],h[5][3];
bool allowed[1296]; uint64_t masks[10][1296][4],coord[5][3][4];vector<pair<int,int>> edges;
long long nodes,leaves,retained,capacity_prunes,local_prunes;
vector<int> assignment(10),example;
chrono::steady_clock::time_point started; bool timeout=false;
vector<unsigned char> seen(60466176,0);
int gauge[6][2][2];ofstream orbitout;
void record_orbit(){
 int key=0;for(int z:assignment)key=6*key+z;
 if(seen[key])return;
 array<int,5> gp={0,1,2,3,4};int minimum=60466176,size=0;
 do{for(int bits=0;bits<32;++bits){
  int code=0;for(auto [u,v]:edges)code=6*code+gauge[P[gp[u]][gp[v]]][(bits>>u)&1][(bits>>v)&1];
  minimum=min(minimum,code);if(!seen[code]){seen[code]=1;++size;}
 }}while(next_permutation(gp.begin(),gp.end()));
 orbitout<<"{\"representative_code\":"<<minimum<<",\"orbit_size\":"<<size<<"}\n";
}
void visit(int depth){
 ++nodes;
 if((nodes&16383)==0 && chrono::duration<double>(chrono::steady_clock::now()-started).count()>60){timeout=true;return;}
 if(depth==10){
  ++leaves;
  uint64_t support[4]={~0ULL,~0ULL,~0ULL,(1ULL<<51)-1}; int edge_index=0;
  for(auto [u,v]:edges){
   int key=P[u][v];
   for(int w=0;w<5;++w)if(w!=u&&w!=v)key=6*key+comp[P[u][w]][P[w][v]];
   if(!allowed[key]){++local_prunes;return;}
   int count=0;for(int b=0;b<4;++b){support[b]&=masks[edge_index][key][b];count+=__builtin_popcountll(support[b]);}
   ++edge_index;if(count<10){++local_prunes;return;}
  }
  for(int u=0;u<5;++u)for(int a=0;a<3;++a){int count=0;for(int b=0;b<4;++b)count+=__builtin_popcountll(support[b]&coord[u][a][b]);if(count<(a?3:4)){++local_prunes;return;}}
  ++retained;record_orbit();if(example.empty())example=assignment;return;
 }
 auto [u,v]=edges[depth];
 for(int z=0;z<6;++z){
  int zu=invp[z],a=ps[zu][0],b=ps[z][0];
  ++h[u][a];++h[v][b];
  if(h[u][a]>(a?3:2)||h[v][b]>(b?3:2))++capacity_prunes;
  else {P[u][v]=z;P[v][u]=zu;assignment[depth]=z;visit(depth+1);}
  --h[u][a];--h[v][b];if(timeout)return;
 }
}
int main(){
 array<int,3> p={0,1,2};int k=0;do{ps[k++]=p;}while(next_permutation(p.begin(),p.end()));
 for(int a=0;a<6;++a){array<int,3> iv;for(int i=0;i<3;++i)iv[ps[a][i]]=i;invp[a]=find(ps.begin(),ps.end(),iv)-ps.begin();
 for(int b=0;b<6;++b){array<int,3> c;for(int i=0;i<3;++i)c[i]=ps[b][ps[a][i]];comp[a][b]=find(ps.begin(),ps.end(),c)-ps.begin();}}
 for(int i=0;i<1296;++i){int x;cin>>x;if(!cin)return 2;allowed[i]=x;}
 for(int u=0;u<5;++u)for(int v=u+1;v<5;++v)edges.push_back({u,v});
 for(int e=0;e<10;++e)for(int k=0;k<1296;++k)for(int b=0;b<4;++b){cin>>masks[e][k][b];if(!cin)return 3;}
 for(int u=0;u<5;++u)for(int a=0;a<3;++a)for(int b=0;b<4;++b){cin>>coord[u][a][b];if(!cin)return 4;}
 for(int z=0;z<6;++z)for(int a=0;a<2;++a)for(int b=0;b<2;++b){array<int,3> q;for(int i=0;i<3;++i){int j=(a&&i)?3-i:i;int v=ps[z][j];q[i]=(b&&v)?3-v:v;}gauge[z][a][b]=find(ps.begin(),ps.end(),q)-ps.begin();}
 orbitout.open("orbits.jsonl");
 started=chrono::steady_clock::now();
 for(int z=0;z<6;++z){
  if(timeout){cout<<"{\"root\":"<<z<<",\"status\":\"UNVISITED\"}\n";continue;}
  nodes=leaves=retained=capacity_prunes=local_prunes=0;example.clear();
  P[0][1]=z;P[1][0]=invp[z];assignment[0]=z;
  ++h[0][ps[invp[z]][0]];++h[1][ps[z][0]];visit(1);--h[0][ps[invp[z]][0]];--h[1][ps[z][0]];
  cout<<"{\"root\":"<<z<<",\"status\":\""<<(timeout?"UNKNOWN":"COMPLETE")<<"\",\"nodes\":"<<nodes<<",\"capacity_prunes\":"<<capacity_prunes<<",\"leaves\":"<<leaves<<",\"local_prunes\":"<<local_prunes<<",\"retained\":"<<retained<<",\"example\":[";
  for(size_t i=0;i<example.size();++i)cout<<(i?",":"")<<example[i];
  cout<<"],\"elapsed_total_seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<"}\n";
 }
}
