#include <array>
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
int main(int argc,char**argv){
 ifstream input(argv[1]);ofstream receipts(argv[2]);
 array<array<int,3>,6> perms;array<int,3> q={0,1,2};int k=0;do{perms[k++]=q;}while(next_permutation(q.begin(),q.end()));
 int eu[10],ev[10],e=0;for(int i=0;i<5;i++)for(int j=i+1;j<5;j++){eu[e]=i;ev[e++]=j;}
 vector<uint64_t> seen((60466176+63)/64);long long total=0;int rows=0;int code,expected;
 auto start=chrono::steady_clock::now();
 while(input>>code>>expected){
  int digits[10],value=code;for(int i=9;i>=0;i--){digits[i]=value%6;value/=6;}if(value)return 2;
  int P[5][5][3]={};for(int i=0;i<10;i++)for(int a=0;a<3;a++){int b=perms[digits[i]][a];P[eu[i]][ev[i]][a]=b;P[ev[i]][eu[i]][b]=a;}
  vector<int> orbit;orbit.reserve(3840);array<int,5> rename={0,1,2,3,4};
  do{for(int swaps=0;swaps<32;swaps++){
   int newP[5][5][3]={};
   // Send each old directed edge to its new positions; do not use producer's gauge lookup.
   for(int i=0;i<10;i++){int u=eu[i],v=ev[i];for(int a=0;a<3;a++){
    int olda=((swaps>>u)&1)&&a?3-a:a;
    int b=P[u][v][olda];if(((swaps>>v)&1)&&b)b=3-b;
    newP[rename[u]][rename[v]][a]=b;newP[rename[v]][rename[u]][b]=a;
   }}
   int transformed=0;for(int i=0;i<10;i++){
    array<int,3> image;for(int a=0;a<3;a++)image[a]=newP[eu[i]][ev[i]][a];
    int z=find(perms.begin(),perms.end(),image)-perms.begin();if(z==6)return 3;transformed=6*transformed+z;
   }
   orbit.push_back(transformed);
  }}while(next_permutation(rename.begin(),rename.end()));
  sort(orbit.begin(),orbit.end());orbit.erase(unique(orbit.begin(),orbit.end()),orbit.end());
  if(orbit.front()!=code || int(orbit.size())!=expected || 3840%expected)return 4;
  for(int v:orbit){uint64_t bit=uint64_t(1)<<(v%64);if(seen[v/64]&bit)return 5;seen[v/64]|=bit;}
  total+=orbit.size();receipts<<code<<" "<<orbit.size()<<"\n";rows++;
  if(chrono::duration<double>(chrono::steady_clock::now()-start).count()>60)return 6;
 }
 cout<<"{\"representatives\":"<<rows<<",\"disjoint_union\":"<<total<<",\"status\":\"COMPLETE\",\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"}\n";
 return rows==1284&&total==4365056?0:7;
}
