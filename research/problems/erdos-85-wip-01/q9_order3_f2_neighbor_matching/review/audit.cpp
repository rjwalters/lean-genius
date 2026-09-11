#include <array>
#include <vector>
#include <fstream>
#include <iostream>
#include <chrono>
#include <cassert>
#include <cstdint>
using namespace std;
int main(int argc,char**argv){
 ifstream in(argv[1]);auto start=chrono::steady_clock::now();int id,count=0,tests=0;uint64_t checksum=0;
 while(in>>id){
  assert(id==count);array<unsigned,18> adj;for(auto &v:adj)in>>v;array<array<int,2>,20> origin;for(auto &v:origin)in>>v[0]>>v[1];
  array<array<int,2>,60> endpoint;
  for(int j=0;j<20;j++)for(int g=0;g<3;g++)for(int side=0;side<2;side++){
   int v=origin[j][side];endpoint[3*j+g][side]=v<0?-1:(v/3)*3+(v%3+g)%3;
  }
  for(int i=0;i<20;i++){
   array<vector<int>,69> edges;int need=9-(origin[i][0]>=0)-(origin[i][1]>=0);
   for(int t=59;t>=0;t--){
    if(t==3*i)continue;bool forbidden=false;
    for(int a=0;a<2;a++)for(int b=0;b<2;b++)if(origin[i][a]>=0&&endpoint[t][b]>=0){
     int u=origin[i][a]+9*a,v=endpoint[t][b]+9*b;
     if(adj[u]&(1u<<v))forbidden=true;
    }
    if(forbidden)continue;
    int l=endpoint[t][0]<0?9+t:endpoint[t][0];int r=endpoint[t][1]<0?9+t:endpoint[t][1];edges[l].push_back(r);
   }
   array<int,69> ml,mr;ml.fill(-1);mr.fill(-1);int flow=0;
   while(flow<need){
    array<int,69> predecessor;predecessor.fill(-1);array<bool,69> visited{};vector<int> q;
    for(int l=68;l>=0;l--)if(ml[l]<0&&!edges[l].empty()){q.push_back(l);visited[l]=true;}
    int finish=-1;
    for(size_t k=0;k<q.size()&&finish<0;k++)for(int r:edges[q[k]])if(predecessor[r]<0){
     predecessor[r]=q[k];if(mr[r]<0){finish=r;break;}
     if(!visited[mr[r]]){visited[mr[r]]=true;q.push_back(mr[r]);}
    }
    if(finish<0)break;
    for(int r=finish;r>=0;){int l=predecessor[r],old=ml[l];ml[l]=r;mr[r]=l;r=old;}
    flow++;
   }
   assert(flow>=need);int chosen=0;
   for(int l=0;l<69;l++)if(ml[l]>=0){assert(mr[ml[l]]==l);bool valid=false;for(int r:edges[l])valid|=(r==ml[l]);assert(valid);chosen++;checksum=checksum*1099511628211ULL+(l*69+ml[l]+1);}
   assert(chosen==need);tests++;
  }
  count++;
  if(chrono::duration<double>(chrono::steady_clock::now()-start).count()>60){cout<<"{\"status\":\"UNKNOWN\",\"visited\":"<<count<<"}\n";return 2;}
 }
 assert(count==56916&&tests==1138320);
 cout<<"{\"status\":\"COMPLETE_PASS\",\"original_review_cap_seconds\":60,\"parameters\":"<<count<<",\"row_matchings\":"<<tests<<",\"checked_matching_checksum\":"<<checksum<<",\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"}\n";
}
