#include <array>
#include <cstdint>
#include <functional>
#include <sstream>
#include <vector>
#include <chrono>
using U=uint64_t;
extern "C" const char* high_pairings(const U*g,int cap,double seconds){
 static thread_local std::string result;
 auto deadline=std::chrono::steady_clock::now()+std::chrono::duration<double>(seconds);
 std::array<int,11> colours{};std::vector<std::array<int,11>> answers;
 int nodes=0;bool complete=true;
 auto tick=[&](){if(++nodes>cap || std::chrono::steady_clock::now()>deadline)throw 1;};
 bool mixed[3][11],paired[11][11];
 for(int h=0;h<3;h++)for(int d=0;d<11;d++)mixed[h][d]=!(g[18+h]&(U(1)<<(7+d))) && !(g[18+h]&g[7+d]);
 for(int d=0;d<11;d++)for(int e=0;e<11;e++)paired[d][e]=!(g[7+d]&g[7+e]);
 std::function<void(unsigned,int)> pair=[&](unsigned remaining,int high){
  tick();if(!remaining){answers.push_back(colours);return;}
  int a=__builtin_ctz(remaining);remaining^=1U<<a;
  for(int b=a+1;b<11;b++)if((remaining>>b&1)&&paired[a][b]){
   colours[a]=colours[b]=high;pair(remaining^(1U<<b),high+1);
  }
 };
 std::function<void(int,unsigned)> match=[&](int high,unsigned used){
  tick();if(high==3){pair(2047^used,3);return;}
  for(int d=0;d<11;d++)if(!(used>>d&1)&&mixed[high][d]){colours[d]=high;match(high+1,used|(1U<<d));}
 };
 try{match(0,0);}catch(int){complete=false;}
 std::ostringstream out;out<<"{\"status\":\""<<(complete?"COMPLETE":"UNKNOWN")<<"\",\"nodes\":"<<nodes<<",\"colourings\":[";
 bool first=true;for(auto &c:answers){if(!first)out<<',';first=false;out<<'[';for(int i=0;i<11;i++){if(i)out<<',';out<<c[i];}out<<']';}
 out<<"]}";result=out.str();return result.c_str();
}
