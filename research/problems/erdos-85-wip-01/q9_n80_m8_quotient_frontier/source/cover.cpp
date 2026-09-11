#include <array>
#include <vector>
#include <map>
#include <iostream>
#include <sstream>
#include <chrono>
#include <algorithm>
using Row=std::array<int,10>;
std::array<std::map<int,std::vector<Row>>,10> indexed;
std::vector<Row> roots;int q[10][10]={},root=0;long nodes=0,kept=0,bytes=0,triangle_prunes=0;
auto started=std::chrono::steady_clock::now();
struct Cap{std::string reason;};
double elapsed(){return std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();}
bool bipartite(int last){
 int color[10];std::fill(color,color+10,-1);
 for(int a=0;a<=last;a++)if(q[a][a]==2&&color[a]<0){
  std::vector<int> queue{a};color[a]=0;
  for(int k=0;k<(int)queue.size();k++){
   int u=queue[k];for(int v=0;v<=last;v++)if(v!=u&&q[v][v]==2&&q[u][v]){
    if(color[v]==color[u])return false;
    if(color[v]<0){color[v]=1-color[u];queue.push_back(v);}
   }
  }
 }
 return true;
}
void visit(int i){
 if(i==10){
  for(int u=0;u<10;u++)if((9-q[u][u])%2){
   bool saturated=true;
   for(int v=0;v<10;v++)if(v!=u&&q[u][v]){int dot=0;for(int k=0;k<10;k++)dot+=q[u][k]*q[k][v];if(dot!=8)saturated=false;}
   if(saturated){triangle_prunes++;return;}
  }
  std::ostringstream s;s<<"{\"root\":"<<root<<",\"matrix\":[";
  for(int u=0;u<10;u++){if(u)s<<',';s<<'[';for(int v=0;v<10;v++){if(v)s<<',';s<<q[u][v];}s<<']';}s<<"]}\n";
  auto line=s.str();if(bytes+(long)line.size()>20000000)throw Cap{"artifact"};std::cout<<line;bytes+=line.size();kept++;return;
 }
 int key=0;for(int j=0;j<i;j++)key=4*key+q[i][j];auto found=indexed[i].find(key);if(found==indexed[i].end())return;
 for(const Row&r:found->second){
  if(nodes==100000)throw Cap{"nodes"};if(elapsed()>=60)throw Cap{"time"};nodes++;
  for(int j=i;j<10;j++)q[i][j]=q[j][i]=r[j];
  bool ok=true;
  for(int j=0;j<i&&ok;j++){
   if(q[i][i]==1&&q[j][j]==1&&q[i][j])ok=false;
   int dot=0;for(int k=0;k<10;k++)dot+=q[i][k]*q[j][k];if(dot>8)ok=false;
  }
  if(ok&&bipartite(i))visit(i+1);
 }
}
int main(){
 int profiles=0;
 for(int a=0;a<3;a++)for(int code=0;code<(1<<18);code++){
  std::array<int,9>x;int z=code,sum=a,norm=a*a;for(int j=8;j>=0;j--){x[j]=z%4;z/=4;sum+=x[j];norm+=x[j]*x[j];}
  if(sum!=9||norm>15)continue;profiles++;
  for(int i=0;i<10;i++){Row r{};r[i]=a;int k=0,key=0;for(int j=0;j<10;j++)if(j!=i)r[j]=x[k++];for(int j=0;j<i;j++)key=4*key+r[j];indexed[i][key].push_back(r);if(i==0&&std::is_sorted(x.begin(),x.end()))roots.push_back(r);}
 }
 if(roots.size()!=13)return 2;
 started=std::chrono::steady_clock::now();int visited=0,unknown=0;long total=0;
 for(root=0;root<13;root++){
  if(elapsed()>=60||bytes>=20000000)break;
  for(auto&r:q)for(int&v:r)v=0;for(int j=0;j<10;j++)q[0][j]=q[j][0]=roots[root][j];
  nodes=kept=triangle_prunes=0;std::string reason="none";
  try{visit(1);}catch(Cap c){reason=c.reason;unknown++;}
  visited++;total+=kept;
  std::cout<<"{\"case\":"<<root<<",\"status\":\""<<(reason=="none"?"COMPLETE":"UNKNOWN")<<"\",\"reason\":\""<<reason<<"\",\"nodes\":"<<nodes<<",\"triangle_prunes\":"<<triangle_prunes<<",\"retained\":"<<kept<<"}\n";
  if(reason=="time"||reason=="artifact")break;
 }
 std::cout<<"{\"summary\":true,\"profiles\":"<<profiles<<",\"roots\":13,\"visited\":"<<visited<<",\"unknown\":"<<unknown<<",\"unvisited\":"<<13-visited<<",\"retained\":"<<total<<",\"seconds\":"<<elapsed()<<"}\n";
}
