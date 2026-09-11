#include "filter.cpp"
#include <climits>
#include <limits>
#include <iostream>
int main(){
 U g[49]{};Checker c(g,INT_MAX,std::numeric_limits<double>::infinity());c.nodes=INT_MAX;
 try{c.tick();return 2;}catch(const Limit&){if(c.nodes!=int64_t(INT_MAX)+1)return 3;}
 std::cout<<"PASS counter reaches2147483648 and raisesLimit withoutoverflow\n";
}
