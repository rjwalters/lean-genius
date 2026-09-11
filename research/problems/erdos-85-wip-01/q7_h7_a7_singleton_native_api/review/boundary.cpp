#include "filter.cpp"
#include <climits>
#include <cassert>
#include <limits>
int main(){
 U g[49]={};Checker c(g,INT_MAX,std::numeric_limits<double>::infinity());
 c.nodes=int64_t(INT_MAX)-1;c.tick();assert(c.nodes==INT_MAX);
 bool stopped=false;try{c.tick();}catch(const Limit&){stopped=true;}
 assert(stopped && c.nodes==int64_t(INT_MAX)+1);
 Checker d(g,100000,native_now()-1);stopped=false;
 try{d.tick();}catch(const Limit&){stopped=true;}
 assert(stopped && d.nodes==1);
}
