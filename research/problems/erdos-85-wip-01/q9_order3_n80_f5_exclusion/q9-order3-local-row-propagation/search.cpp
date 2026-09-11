#include <iostream>
#include <vector>
#include <array>
#include <chrono>
using namespace std;
vector<array<int,5>> words;vector<array<int,15>> caps;vector<vector<int>> adj;vector<bool> active;long long tested=0;bool timeout=false;chrono::steady_clock::time_point started;
bool valid(int i,array<int,4> row){++tested;if((tested&16383)==0&&chrono::duration<double>(chrono::steady_clock::now()-started).count()>60){timeout=true;return false;}
 auto left=caps[i];for(int j:row)for(int u=0;u<5;++u)if(--left[3*u+words[j][u]]<0)return false;
 for(int k=0;k<4;++k){if(k&&row[k]==row[k-1])continue;for(int l=k+1;l<4;++l){if(row[k]==row[l]||(l&&row[l]==row[l-1]))continue;int a=row[k],b=row[l],qa=0,qb=0,agree=0;for(int j:row){qa+=j==a;qb+=j==b;}for(int u=0;u<5;++u)agree+=words[a][u]==words[b][u];if(qa*qb+agree>3)return false;}}
 return true;}
int main(){int n;cin>>n;words.resize(n);caps.resize(n);adj.resize(n);active.assign(n,true);for(int i=0;i<n;++i){for(int&x:words[i])cin>>x;for(int&x:caps[i])cin>>x;int m;cin>>m;adj[i].resize(m);for(int&x:adj[i])cin>>x;}started=chrono::steady_clock::now();
for(int round=0;;++round){vector<int> removed;for(int i=0;i<n;++i)if(active[i]){vector<int> v;bool diag=false;for(int j:adj[i])if(active[j]){if(j==i)diag=true;else v.push_back(j);}array<int,4> answer={-1,-1,-1,-1};bool found=false;
for(size_t a=0;a<v.size()&&!found&&!timeout;++a)for(size_t b=a+1;b<v.size()&&!found&&!timeout;++b){if(diag){array<int,4> row={i,i,v[a],v[b]};if(valid(i,row)){answer=row;found=true;break;}}
for(int j:v)if(j!=v[a]&&j!=v[b]){array<int,4> row={j,j,v[a],v[b]};if(valid(i,row)){answer=row;found=true;break;}if(timeout)break;}
for(size_t c=b+1;c<v.size()&&!found&&!timeout;++c)for(size_t d=c+1;d<v.size()&&!found&&!timeout;++d){array<int,4> row={v[a],v[b],v[c],v[d]};if(valid(i,row)){answer=row;found=true;}}}
cout<<"{\"round\":"<<round<<",\"word\":"<<i<<",\"status\":\""<<(timeout?"UNKNOWN":found?"SUPPORTED":"REMOVED")<<"\",\"row\":[";for(int k=0;k<4;++k)cout<<(k?",":"")<<answer[k];cout<<"]}\n";if(timeout)return 0;if(!found)removed.push_back(i);}
for(int i:removed)active[i]=false;if(removed.empty()){int count=0;for(bool b:active)count+=b;cout<<"{\"status\":\"FIXPOINT\",\"remaining\":"<<count<<",\"tested\":"<<tested<<"}\n";return 0;}}
}
