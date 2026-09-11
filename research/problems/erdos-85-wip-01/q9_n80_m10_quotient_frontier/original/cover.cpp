#include <array>
#include <vector>
#include <map>
#include <iostream>
#include <sstream>
#include <chrono>
#include <algorithm>
using Row=std::array<int,8>;
std::array<std::map<int,std::vector<Row>>,8> index_rows;
std::vector<Row> roots; int q[8][8]={},root_id=0; long nodes=0,retained=0,bytes=0;
auto began=std::chrono::steady_clock::now();
struct Cap {std::string reason;};
double elapsed(){return std::chrono::duration<double>(std::chrono::steady_clock::now()-began).count();}
void visit(int i){
 if(i==8){
  std::ostringstream s;s<<"{\"root\":"<<root_id<<",\"matrix\":[";
  for(int u=0;u<8;u++){if(u)s<<',';s<<'[';for(int v=0;v<8;v++){if(v)s<<',';s<<q[u][v];}s<<']';}s<<"]}\n";
  auto text=s.str();if(bytes+(long)text.size()>40000000)throw Cap{"artifact"};std::cout<<text;bytes+=text.size();retained++;return;
 }
 int key=0;for(int j=0;j<i;j++)key=4*key+q[i][j];
 auto found=index_rows[i].find(key);if(found==index_rows[i].end())return;
 for(const Row& r:found->second){
  if(nodes==100000)throw Cap{"nodes"};if(elapsed()>=60)throw Cap{"time"};nodes++;
  for(int j=i;j<8;j++)q[i][j]=q[j][i]=r[j];
  bool ok=true;
  for(int j=0;j<i && ok;j++){
   if(q[i][i]==1 && q[j][j]==1 && q[i][j]>0){ok=false;break;}
   int dot=0;for(int k=0;k<8;k++)dot+=q[i][k]*q[j][k];if(dot>10)ok=false;
  }
  if(ok)visit(i+1);
 }
}
int main(){
 int profiles=0;
 for(int a=0;a<3;a++)for(int code=0;code<(1<<14);code++){
  std::array<int,7>x{};int z=code,sum=a,square=a*a;for(int j=6;j>=0;j--){x[j]=z%4;z/=4;sum+=x[j];square+=x[j]*x[j];}
  if(sum!=9 || square>18)continue;profiles++;
  for(int i=0;i<8;i++){
   Row r{};r[i]=a;int k=0,key=0;for(int j=0;j<8;j++)if(j!=i)r[j]=x[k++];for(int j=0;j<i;j++)key=4*key+r[j];index_rows[i][key].push_back(r);
   if(i==0 && std::is_sorted(x.begin(),x.end()))roots.push_back(r);
  }
 }
 if(profiles!=1800 || roots.size()!=16)return 2;
 began=std::chrono::steady_clock::now();int visited=0,unknown=0;long total=0;
 for(root_id=0;root_id<(int)roots.size();root_id++){
  if(elapsed()>=60 || bytes>=40000000)break;
  for(auto& row:q)for(int& value:row)value=0;
  for(int j=0;j<8;j++)q[0][j]=q[j][0]=roots[root_id][j];
  nodes=0;retained=0;std::string reason="none";
  try{visit(1);}catch(Cap c){reason=c.reason;unknown++;}
  visited++;total+=retained;
  std::cout<<"{\"case\":"<<root_id<<",\"status\":\""<<(reason=="none"?"COMPLETE":"UNKNOWN")<<"\",\"reason\":\""<<reason<<"\",\"nodes\":"<<nodes<<",\"retained\":"<<retained<<"}\n";
  if(reason=="time" || reason=="artifact")break;
 }
 std::cout<<"{\"summary\":true,\"profiles\":"<<profiles<<",\"roots\":16,\"visited\":"<<visited<<",\"unknown\":"<<unknown<<",\"unvisited\":"<<16-visited<<",\"retained\":"<<total<<",\"seconds\":"<<elapsed()<<"}\n";
}
