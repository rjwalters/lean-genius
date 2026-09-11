#include "hosts.cpp"
#include <climits>
#include <iostream>
int main(){
 U input[49]{};Search s(input,INT_MAX,60,nullptr);s.nodes=INT_MAX;
 try{s.tick();return 1;}catch(Limit&){if(s.nodes!=int64_t(INT_MAX)+1)return 2;}
 Search expired(input,100000,-1,nullptr);
 try{expired.tick();return 3;}catch(Limit&){if(expired.nodes!=1)return 4;}
 std::cout<<"PASS INT_MAX+1 and expired deadline\n";
}
