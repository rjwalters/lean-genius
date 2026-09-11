#include "filter.cpp"
#include <cassert>
#include <climits>
#include <limits>
#include <iostream>
int main(){
 U adjacency[49]={};Checker checker(adjacency,INT_MAX,std::numeric_limits<double>::infinity());checker.nodes=INT_MAX;
 bool caught=false;try{checker.tick();}catch(const Limit&){caught=true;}
 assert(caught && checker.nodes==int64_t(INT_MAX)+1);
 std::cout<<"{\"status\":\"PASS\",\"counter_after_tick\":"<<checker.nodes<<",\"limit_exception\":true}\n";
}
