#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <stdexcept>

int main() {
  if (std::ifstream("launch.json").good()) throw std::runtime_error("no overwrite or restart");
  std::ofstream("launch.json") << "{\"cases\":625,\"per_case_combinations\":15625,\"seconds\":60,\"scope\":\"integer quotient only\"}\n";
  auto start=std::chrono::steady_clock::now();
  auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
  std::ofstream out("quotients.jsonl");
  long long combinations=0,regular=0,retained=0;int completed=0,expanded=0;bool stop=false;
  const int left[6]={1,1,1,2,2,3},right[6]={2,3,4,3,4,4};
  for(int first=0;first<625;++first) {
    if(elapsed()>=60){stop=true;break;}
    int q[5][5]={};int code=first,sum=0;
    for(int j=1;j<5;++j){q[0][j]=q[j][0]=code%5;sum+=code%5;code/=5;}
    q[0][0]=9-sum;
    int sq=0;for(int k=0;k<5;++k)sq+=q[0][k]*q[0][k];
    if(q[0][0]<0||q[0][0]>2||sq>24){++completed;continue;}
    ++expanded;
    for(int rest=0;rest<15625;++rest) {
      ++combinations;code=rest;
      for(int e=0;e<6;++e){q[left[e]][right[e]]=q[right[e]][left[e]]=code%5;code/=5;}
      bool ok=true;
      for(int i=1;i<5;++i){sum=0;for(int j=0;j<5;++j)if(i!=j)sum+=q[i][j];q[i][i]=9-sum;if(q[i][i]<0||q[i][i]>2)ok=false;}
      if(!ok)continue;++regular;
      for(int i=0;i<5&&ok;++i)for(int j=i;j<5&&ok;++j){
        int value=0;for(int k=0;k<5;++k)value+=q[i][k]*q[k][j];
        if(value>(i==j?24:16))ok=false;
        if(i!=j&&q[i][i]==1&&q[j][j]==1&&q[i][j]>0)ok=false;
      }
      if(!ok)continue;
      out<<'[';for(int i=0;i<5;++i)for(int j=0;j<5;++j){if(i||j)out<<',';out<<q[i][j];}out<<"]\n";++retained;
    }
    ++completed;
    if(out.tellp()>90000000){stop=true;break;}
  }
  out.close();
  std::ofstream result("results.json");
  result<<"{\"status\":\""<<(stop?"UNKNOWN":"COMPLETE")<<"\",\"completed_cases\":"<<completed
    <<",\"unvisited_cases\":"<<625-completed<<",\"expanded_cases\":"<<expanded<<",\"combinations\":"<<combinations
    <<",\"regular_after_first_row_filter\":"<<regular<<",\"retained\":"<<retained<<",\"seconds\":"<<elapsed()
    <<",\"scope\":\"necessary integer quotient cover only, not graph search or exclusion\"}\n";
  std::cout<<"cases="<<completed<<" retained="<<retained<<" seconds="<<elapsed()<<'\n';
}
