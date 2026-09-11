#include <array>
#include <bitset>
#include <chrono>
#include <fstream>
#include <iostream>
#include <algorithm>
using namespace std;
using Bits=bitset<243>;
array<array<int,3>,6> perm;
int inverse[6], compose[6][6], eu[10],ev[10],assignment[10],loads[5][3];
bool localOK[1296],stopped=false;
Bits supports[10][1296],coordinate[5][3];
unsigned long long nodes=0,countOK=0;
chrono::steady_clock::time_point began;
Bits getBits(istream& in){Bits r;for(int j=0;j<4;j++){unsigned long long x;in>>x;for(int k=0;k<64 && 64*j+k<243;k++)r[64*j+k]=(x>>k)&1;}return r;}
bool accept(){
 int P[5][5]={};for(int e=0;e<10;e++){P[eu[e]][ev[e]]=assignment[e];P[ev[e]][eu[e]]=inverse[assignment[e]];}
 Bits possible;possible.set();
 // Reverse pair order, independently of the producer's forward traversal.
 for(int e=9;e>=0;e--){int u=eu[e],v=ev[e],key=P[u][v];
  for(int w=0;w<5;w++)if(w!=u&&w!=v)key=key*6+compose[P[u][w]][P[w][v]];
  if(!localOK[key])return false;possible &=supports[e][key];
 }
 if(possible.count()<10)return false;
 for(int u=0;u<5;u++)for(int a=0;a<3;a++)if((possible&coordinate[u][a]).count()<unsigned(a==0?4:3))return false;
 return true;
}
void traverse(int edge){
 nodes++;
 if((nodes&4095)==0 && chrono::duration<double>(chrono::steady_clock::now()-began).count()>60){stopped=true;return;}
 if(edge==0){countOK+=accept();return;}
 int u=eu[edge],v=ev[edge];
 for(int z=0;z<6;z++){
  int a=perm[inverse[z]][0],b=perm[z][0];
  if(loads[u][a]+1>(a==0?2:3)||loads[v][b]+1>(b==0?2:3))continue;
  loads[u][a]++;loads[v][b]++;assignment[edge]=z;traverse(edge-1);loads[u][a]--;loads[v][b]--;if(stopped)return;
 }
}
int main(int argc,char**argv){
 ifstream input(argv[1]);array<int,3> p={0,1,2};int n=0;do{perm[n++]=p;}while(next_permutation(p.begin(),p.end()));
 for(int i=0;i<6;i++){array<int,3> q;for(int a=0;a<3;a++)q[perm[i][a]]=a;inverse[i]=find(perm.begin(),perm.end(),q)-perm.begin();
  for(int j=0;j<6;j++){for(int a=0;a<3;a++)q[a]=perm[j][perm[i][a]];compose[i][j]=find(perm.begin(),perm.end(),q)-perm.begin();}}
 int e=0;for(int u=0;u<5;u++)for(int v=u+1;v<5;v++){eu[e]=u;ev[e++]=v;}
 for(int i=0;i<1296;i++){int v;input>>v;localOK[i]=v;}
 for(int e=0;e<10;e++)for(int i=0;i<1296;i++)supports[e][i]=getBits(input);
 for(int u=0;u<5;u++)for(int a=0;a<3;a++)coordinate[u][a]=getBits(input);
 if(!input)return 2;began=chrono::steady_clock::now();
 for(int root=0;root<6;root++){
  if(stopped){cout<<"{\"root\":"<<root<<",\"status\":\"UNVISITED\"}\n";continue;}
  nodes=countOK=0;assignment[0]=root;int a=perm[inverse[root]][0],b=perm[root][0];loads[0][a]++;loads[1][b]++;
  traverse(9);loads[0][a]--;loads[1][b]--;
  cout<<"{\"root\":"<<root<<",\"status\":\""<<(stopped?"UNKNOWN":"COMPLETE")<<"\",\"nodes\":"<<nodes<<",\"retained\":"<<countOK<<",\"elapsed\":"<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<"}\n";
 }
 return stopped?3:0;
}
