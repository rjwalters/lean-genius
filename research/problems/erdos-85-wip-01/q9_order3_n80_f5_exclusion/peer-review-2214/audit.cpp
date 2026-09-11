#include <array>
#include <vector>
#include <iostream>
#include <chrono>
#include <algorithm>
using namespace std;
vector<array<int,5>> W;vector<array<int,15>> B;vector<vector<int>> adj;vector<bool> active;int agree[243][243];long long states=0;bool timed=false;chrono::steady_clock::time_point start;
int centre;vector<int> candidates;vector<pair<int,int>> selected;array<int,15> remainingCapacity;
bool support(int offset,int degree,int norm){
 states++;if((states&4095)==0&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>60){timed=true;return false;}
 if(degree==4)return true;
 for(int pos=offset;pos<(int)candidates.size();pos++){
  int v=candidates[pos];for(int mult=2;mult>=1;mult--){
   if(v==centre&&mult!=2)continue;
   if(degree+mult>4||norm+mult*mult>6)continue;
   bool ok=true;
   for(auto [u,q]:selected)if(q*mult+agree[u][v]>3)ok=false;
   for(int u=0;u<5;u++)if(remainingCapacity[3*u+W[v][u]]<mult)ok=false;
   if(!ok)continue;
   for(int u=0;u<5;u++)remainingCapacity[3*u+W[v][u]]-=mult;
   selected.push_back({v,mult});bool found=support(pos+1,degree+mult,norm+mult*mult);selected.pop_back();
   for(int u=0;u<5;u++)remainingCapacity[3*u+W[v][u]]+=mult;
   if(found||timed)return found;
  }
 }
 return false;
}
int main(){int n;cin>>n;W.resize(n);B.resize(n);adj.resize(n);active.assign(n,true);
for(int i=0;i<n;i++){for(int&v:W[i])cin>>v;for(int&v:B[i])cin>>v;int k;cin>>k;adj[i].resize(k);for(int&v:adj[i])cin>>v;}if(!cin)return 2;
for(int i=0;i<n;i++)for(int j=0;j<n;j++)for(int u=0;u<5;u++)agree[i][j]+=W[i][u]==W[j][u];start=chrono::steady_clock::now();
for(int round=0;;round++){
 vector<int> removed;
 for(int i=n-1;i>=0;i--)if(active[i]){
  centre=i;remainingCapacity=B[i];candidates.clear();for(int v:adj[i])if(active[v])candidates.push_back(v);sort(candidates.rbegin(),candidates.rend());
  bool yes=support(0,0,0);if(timed){cout<<"{\"status\":\"UNKNOWN\"}\n";return 3;}if(!yes)removed.push_back(i);
 }
 cout<<"{\"round\":"<<round<<",\"removed\":[";for(int i=0;i<(int)removed.size();i++)cout<<(i?",":"")<<removed[i];cout<<"]}\n";
 if(removed.empty()){int count=0;for(bool a:active)count+=a;cout<<"{\"status\":\"FIXPOINT\",\"remaining\":"<<count<<",\"states\":"<<states<<"}\n";return count?1:0;}
 for(int i:removed)active[i]=false;
}
}
