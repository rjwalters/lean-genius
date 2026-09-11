#include <array>
#include <vector>
#include <fstream>
#include <iostream>
#include <chrono>
#include <functional>
#include <queue>
#include <cassert>
using namespace std;
int main(int argc,char**argv){
 ifstream in(argv[1]);ofstream out(argv[2]);auto start=chrono::steady_clock::now();int id,visited=0,excluded=0,tests=0;bool timeout=false;
 while(in>>id){
  array<int,18> adj;array<int,20>A,B;for(int &x:adj)in>>x;for(int j=0;j<20;j++)in>>A[j]>>B[j];
  if(chrono::duration<double>(chrono::steady_clock::now()-start).count()>=60){timeout=true;break;}
  bool bad=false;
  for(int i=0;i<20;i++){
   tests++;int need=9-(A[i]>=0)-(B[i]>=0);int forbidden=(A[i]<0?0:adj[A[i]])|(B[i]<0?0:adj[9+B[i]]);
   array<vector<int>,69> edges;
   for(int j=0;j<20;j++)for(int g=0;g<3;g++){
    if(j==i&&g==0)continue;
    int a=A[j]<0?-1:(A[j]/3)*3+(A[j]%3+g)%3;
    int b=B[j]<0?-1:(B[j]/3)*3+(B[j]%3+g)%3;
    int bits=(a<0?0:1<<a)|(b<0?0:1<<(9+b));if(bits&forbidden)continue;
    int l=a<0?9+3*j+g:a,r=b<0?9+3*j+g:b;edges[l].push_back(r);
   }
   array<int,69> mr;mr.fill(-1);int flow=0;
   function<bool(int,array<bool,69>&)> augment=[&](int l,array<bool,69>&seen){
    for(int r:edges[l])if(!seen[r]){seen[r]=true;if(mr[r]<0||augment(mr[r],seen)){mr[r]=l;return true;}}return false;
   };
   for(int l=0;l<69&&flow<need;l++){array<bool,69> seen{};if(augment(l,seen))flow++;}
   if(flow>=need)continue;
   array<int,69> ml;ml.fill(-1);for(int r=0;r<69;r++)if(mr[r]>=0)ml[mr[r]]=r;
   array<bool,69> vl{},vr{};queue<int> todo;for(int l=0;l<69;l++)if(ml[l]<0){vl[l]=true;todo.push(l);}
   while(!todo.empty()){int l=todo.front();todo.pop();for(int r:edges[l])if(ml[l]!=r&&!vr[r]){vr[r]=true;if(mr[r]>=0&&!vl[mr[r]]){vl[mr[r]]=true;todo.push(mr[r]);}}}
   vector<int> lc,rc;for(int l=0;l<69;l++)if(!vl[l])lc.push_back(l);for(int r=0;r<69;r++)if(vr[r])rc.push_back(r);
   assert((int)(lc.size()+rc.size())==flow);for(int l=0;l<69;l++)for(int r:edges[l])assert(!vl[l]||vr[r]);
   out<<id<<" "<<i<<" "<<need<<" "<<flow<<" "<<lc.size();for(int x:lc)out<<" "<<x;out<<" "<<rc.size();for(int x:rc)out<<" "<<x;out<<"\n";bad=true;excluded++;break;
  }
  if(!bad)out<<id<<" -1\n";visited++;
 }
 double seconds=chrono::duration<double>(chrono::steady_clock::now()-start).count();
 cout<<"{\"status\":\""<<(timeout?"UNKNOWN":"COMPLETE")<<"\",\"original_wall_cap\":60,\"visited\":"<<visited<<",\"excluded\":"<<excluded<<",\"retained\":"<<visited-excluded<<",\"row_tests\":"<<tests<<",\"seconds\":"<<seconds<<"}\n";
}
