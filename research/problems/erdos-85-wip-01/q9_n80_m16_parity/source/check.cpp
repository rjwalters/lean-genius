#include <chrono>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>
#include "inputs.h"
int main(){
 if(std::ifstream("launch.json").good())throw std::runtime_error("preserve original pass");
 std::ofstream("launch.json")<<"{\"seconds\":60,\"max_combinations_per_case\":100000,\"case\":\"type,diagonal signs,first two edge values\"}\n";
 auto start=std::chrono::steady_clock::now();
 auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
 std::ofstream out("retained.jsonl"),stats("results.json");stats<<"[\n";
 int u[10]={0,0,0,0,1,1,1,2,2,3},v[10]={1,2,3,4,2,3,4,3,4,4};
 for(int type=0;type<6;++type){
  int h[5][5]={},sq[5][5]={};std::vector<int> twos;
  for(int i=0;i<5;++i){if(Q[type][i][i]==2)twos.push_back(i);else h[i][i]=Q[type][i][i];
   for(int j=0;j<5;++j)for(int k=0;k<5;++k)sq[i][j]+=Q[type][i][k]*Q[type][k][j];}
  long long tested=0,retained=0,maxcase=0,cases=0;bool stopped=false;
  for(int signs=0;signs<(1<<twos.size())&&!stopped;++signs){
   for(int j=0;j<(int)twos.size();++j)h[twos[j]][twos[j]]=(signs>>j&1)?2:-2;
   for(int x=-Q[type][0][1];x<=Q[type][0][1]&&!stopped;x+=2)for(int y=-Q[type][0][2];y<=Q[type][0][2]&&!stopped;y+=2){
    h[0][1]=h[1][0]=x;h[0][2]=h[2][0]=y;
    long long combos=1;for(int e=2;e<10;++e)combos*=Q[type][u[e]][v[e]]+1;
    if(combos>100000)throw std::runtime_error("case cap");maxcase=std::max(maxcase,combos);
    if(elapsed()>60){stopped=true;break;}++cases;
    for(long long code=0;code<combos;++code){
     ++tested;long long rest=code;
     for(int e=2;e<10;++e){int degree=Q[type][u[e]][v[e]],value=2*(rest%(degree+1))-degree;rest/=degree+1;h[u[e]][v[e]]=h[v[e]][u[e]]=value;}
     bool ok=true;
     for(int i=0;i<5&&ok;++i)for(int j=i;j<5&&ok;++j){
      int value=0;for(int k=0;k<5;++k)value+=h[i][k]*h[k][j];
      if(i==j){bool allowed=false;int pairs=(sq[i][i]-9)/2;
       for(int even=0;even<=3;++even)for(int odd=0;odd<=4;++odd)if(even+odd==pairs&&value==9+2*(even-odd))allowed=true;
       if(!allowed)ok=false;
      }else{int bound=std::min(sq[i][j],16-sq[i][j]);if(value>bound||value< -bound||(value-sq[i][j])%2)ok=false;}
     }
     if(ok){++retained;out<<"{\"type\":"<<type<<",\"matrix\":[";for(int i=0;i<5;++i)for(int j=0;j<5;++j){if(i||j)out<<',';out<<h[i][j];}out<<"]}\n";}
    }
   }
  }
  if(type)stats<<",\n";stats<<"{\"type\":"<<type<<",\"status\":\""<<(stopped?"UNKNOWN":"COMPLETE")<<"\",\"cases\":"<<cases<<",\"max_case_combinations\":"<<maxcase<<",\"tested\":"<<tested<<",\"retained\":"<<retained<<",\"aggregate_seconds\":"<<elapsed()<<'}';
  std::cout<<type<<" tested="<<tested<<" retained="<<retained<<'\n';
  if(stopped)break;
 }
 stats<<"\n]\n";
}
