#include <array>
#include <bitset>
#include <vector>
#include <iostream>
#include <chrono>
using namespace std;
using B=bitset<243>;
array<array<int,5>,243> W;B compatible[243],cell[5][3];int U[10],V[10],capacity[10][3][3],used[10][3][3],marg[5][3];long nodes;bool limited,found,wall=false;chrono::steady_clock::time_point start;
bool can(int x){for(int u=0;u<5;u++)if(marg[u][W[x][u]]>=(W[x][u]?3:4))return false;for(int k=0;k<10;k++)if(used[k][W[x][U[k]]][W[x][V[k]]]>=capacity[k][W[x][U[k]]][W[x][V[k]]])return false;return true;}
void visit(B candidates,int depth){
 if(nodes>=100000){limited=true;return;}nodes++;
 if((nodes&1023)==0 && chrono::duration<double>(chrono::steady_clock::now()-start).count()>60){limited=wall=true;return;}
 if(depth==10){found=true;return;}
 if(candidates.count()<unsigned(10-depth))return;
 for(int u=0;u<5;u++)for(int a=0;a<3;a++)if(marg[u][a]+(candidates&cell[u][a]).count()<unsigned(a?3:4))return;
 // Decreasing word order; every subset has exactly one path.
 for(int x=242;x>=0;x--)if(candidates[x]){
  candidates.reset(x);if(!can(x))continue;
  for(int u=0;u<5;u++)marg[u][W[x][u]]++;
  for(int k=0;k<10;k++)used[k][W[x][U[k]]][W[x][V[k]]]++;
  B next=candidates&compatible[x];for(int y=0;y<243;y++)if(next[y]&&!can(y))next.reset(y);
  visit(next,depth+1);
  for(int u=0;u<5;u++)marg[u][W[x][u]]--;
  for(int k=0;k<10;k++)used[k][W[x][U[k]]][W[x][V[k]]]--;
  if(limited||found)return;
 }
}
int main(){
 for(int x=0;x<243;x++){int z=x;for(int u=4;u>=0;u--){W[x][u]=z%3;z/=3;cell[u][W[x][u]].set(x);}}
 for(int x=0;x<243;x++)for(int y=0;y<243;y++){int a=0;for(int u=0;u<5;u++)a+=W[x][u]==W[y][u];if(a<=3)compatible[x].set(y);}
 int k=0;for(int u=0;u<5;u++)for(int v=u+1;v<5;v++){U[k]=u;V[k++]=v;}
 int cases;cin>>cases;start=chrono::steady_clock::now();
 for(int c=0;c<cases;c++){int code,n;cin>>code>>n;B b;for(int i=0;i<n;i++){int x;cin>>x;b.set(x);}for(int k=0;k<10;k++)for(int a=0;a<3;a++)for(int z=0;z<3;z++)cin>>capacity[k][a][z];if(!cin)return 2;
 nodes=0;limited=found=false;bool unvisited=wall||chrono::duration<double>(chrono::steady_clock::now()-start).count()>60;if(!unvisited)visit(b,0);
 cout<<"{\"code\":"<<code<<",\"status\":\""<<(unvisited?"UNVISITED":limited?"UNKNOWN":found?"POSITIVE":"COMPLETE_NEGATIVE")<<"\",\"nodes\":"<<nodes<<"}\n";
 }
}
