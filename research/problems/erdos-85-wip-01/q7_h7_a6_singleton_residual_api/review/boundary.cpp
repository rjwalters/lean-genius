#include "filter.cpp"
#include <climits>
#include <limits>
int main(){
 U g[49]{};Checker c(g,INT_MAX,std::numeric_limits<double>::infinity());c.nodes=int64_t(INT_MAX)-1;
 c.tick();if(c.nodes!=INT_MAX)return 1;
 try{c.tick();return 2;}catch(const Limit&){if(c.nodes!=int64_t(INT_MAX)+1)return 3;}
 Checker expired(g,100000,0.0);try{expired.tick();return 4;}catch(const Limit&){}
 return 0;
}
