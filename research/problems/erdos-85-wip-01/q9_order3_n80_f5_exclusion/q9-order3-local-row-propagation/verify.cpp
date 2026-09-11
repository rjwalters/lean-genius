#include <iostream>
#include <vector>
#include <array>
#include <map>
using namespace std;
int main(){int n;cin>>n;vector<array<int,5>> W(n);vector<array<int,15>> B(n);vector<vector<int>> adj(n);for(int i=0;i<n;++i){for(int&x:W[i])cin>>x;for(int&x:B[i])cin>>x;int m;cin>>m;adj[i].resize(m);for(int&x:adj[i])cin>>x;}vector<bool> alive(n,true);long long tested=0;int removed_total=0;
while(true){vector<int> removed;for(int i=n-1;i>=0;--i)if(alive[i]){vector<int> v;for(int j:adj[i])if(alive[j])v.push_back(j);bool found=false;
for(int a=0;a<(int)v.size()&&!found;++a)for(int b=a;b<(int)v.size()&&!found;++b)for(int c=b;c<(int)v.size()&&!found;++c)for(int d=c;d<(int)v.size()&&!found;++d){map<int,int> q;for(int k:{a,b,c,d})++q[v[k]];if(q.count(i)&&q[i]!=2)continue;int norm=0;for(auto[j,x]:q)norm+=x*x;if(norm>6)continue;++tested;bool ok=true;
for(int u=0;u<5;++u)for(int label=0;label<3;++label){int sum=0;for(auto[j,x]:q)if(W[j][u]==label)sum+=x;if(sum>B[i][3*u+label])ok=false;}
for(auto[j,x]:q)for(auto[k,y]:q)if(j<k){int agree=0;for(int u=0;u<5;++u)agree+=W[j][u]==W[k][u];if(x*y+agree>3)ok=false;}if(ok)found=true;
}if(!found)removed.push_back(i);}
if(removed.empty())break;for(int i:removed)alive[i]=false;removed_total+=removed.size();}
int left=0;for(bool b:alive)left+=b;cout<<"{\"remaining\":"<<left<<",\"removed\":"<<removed_total<<",\"profiles_tested\":"<<tested<<"}\n";return left?1:0;}
