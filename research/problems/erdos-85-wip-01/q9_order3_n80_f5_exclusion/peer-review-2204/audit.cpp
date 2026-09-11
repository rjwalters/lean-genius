#include <array>
#include <bitset>
#include <vector>
#include <iostream>
#include <chrono>
using namespace std;
using B=bitset<243>;
array<array<int,5>,243> W;B compatible[243],cell[5][3];int U[10],V[10],capacity[10][3][3],used[10][3][3],marg[5][3];long nodes;bool limited,found,wall=false;chrono::steady_clock::time_point start;
bool can(int x){for(int u=0;u<5;u++)if(marg[u][W[x][u]]>=(W[x][u]?3:4))return false;for(int k=0;k<10;k++)if(used[k][W[x][U[k]]][W[x][V[k]]]>=capacity[k][W[x][U[k]]][W[x][V[k]]])return false;return true;}
int bound[243][15];vector<array<int,4>> rows[10];vector<int> selected;long rejected;
bool rowOK(){
 for(int i=0;i<10;i++){
  bool ok=false;
  for(auto profile:rows[i]){
   int load[15]={};for(int j:profile)for(int u=0;u<5;u++)load[3*u+W[selected[j]][u]]++;
   bool fits=true;for(int k=0;k<15;k++)if(load[k]>bound[selected[i]][k])fits=false;
   if(fits){ok=true;break;}
  }
  if(!ok)return false;
 }
 return true;
}
void visit(B candidates,int depth){
 if(nodes>=100000){limited=true;return;}nodes++;
 if((nodes&1023)==0 && chrono::duration<double>(chrono::steady_clock::now()-start).count()>60){limited=wall=true;return;}
 if(depth==10){if(rowOK())found=true;else rejected++;return;}
 if(candidates.count()<unsigned(10-depth))return;
 for(int u=0;u<5;u++)for(int a=0;a<3;a++)if(marg[u][a]+(candidates&cell[u][a]).count()<unsigned(a?3:4))return;
 // Ascending subset order, matching producer domain; independent bitset state and row enumeration.
 for(int x=0;x<243;x++)if(candidates[x]){
  candidates.reset(x);if(!can(x))continue;
  for(int u=0;u<5;u++)marg[u][W[x][u]]++;
  for(int k=0;k<10;k++)used[k][W[x][U[k]]][W[x][V[k]]]++;
  B next=candidates&compatible[x];for(int y=0;y<243;y++)if(next[y]&&!can(y))next.reset(y);
  selected.push_back(x);visit(next,depth+1);selected.pop_back();
  for(int u=0;u<5;u++)marg[u][W[x][u]]--;
  for(int k=0;k<10;k++)used[k][W[x][U[k]]][W[x][V[k]]]--;
  if(limited||found)return;
 }
}
int main(){
 for(int x=0;x<243;x++){int z=x;for(int u=4;u>=0;u--){W[x][u]=z%3;z/=3;cell[u][W[x][u]].set(x);}}
 for(int x=0;x<243;x++)for(int y=0;y<243;y++){int a=0;for(int u=0;u<5;u++)a+=W[x][u]==W[y][u];if(a<=3)compatible[x].set(y);}
 int k=0;for(int u=0;u<5;u++)for(int v=u+1;v<5;v++){U[k]=u;V[k++]=v;}
 for(int i=0;i<10;i++){
  for(int a=0;a<10;a++)for(int b=a;b<10;b++)for(int c=b;c<10;c++)for(int d=c;d<10;d++){
   int mult[10]={};mult[a]++;mult[b]++;mult[c]++;mult[d]++;int norm=0,mx=0;
   for(int x:mult){norm+=x*x;if(x>mx)mx=x;}
   if(mx<=2&&norm<=6&&(mult[i]==0||mult[i]==2))rows[i].push_back({a,b,c,d});
  }
  if(rows[i].size()!=414)return 4;
 }
 int cases;cin>>cases;start=chrono::steady_clock::now();
 for(int c=0;c<cases;c++){int code,n;cin>>code>>n;B b;for(int i=0;i<n;i++){int x;cin>>x;b.set(x);}for(int k=0;k<10;k++)for(int a=0;a<3;a++)for(int z=0;z<3;z++)cin>>capacity[k][a][z];for(int x=0;x<243;x++)for(int k=0;k<15;k++)cin>>bound[x][k];if(!cin)return 2;
 nodes=0;rejected=0;limited=found=false;bool unvisited=wall||chrono::duration<double>(chrono::steady_clock::now()-start).count()>60;if(!unvisited)visit(b,0);
 cout<<"{\"code\":"<<code<<",\"status\":\""<<(unvisited?"UNVISITED":limited?"UNKNOWN":found?"POSITIVE":"COMPLETE_NEGATIVE")<<"\",\"nodes\":"<<nodes<<",\"rejected\":"<<rejected<<"}\n";
 }
}
