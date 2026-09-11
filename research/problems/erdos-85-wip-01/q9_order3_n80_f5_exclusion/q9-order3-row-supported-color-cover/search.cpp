#include <array>
#include <vector>
#include <iostream>
#include <chrono>
using namespace std;
array<array<int,5>,243> words;vector<pair<int,int>> pairs;
int caps[10][3][3],tabs[10][3][3]={},counts[5][3]={};
vector<array<int,4>> profiles[10];int B[243][15];long long rejected_colors;
vector<int> selected,answer;
bool row_support(){for(int i=0;i<10;++i){bool found=false;for(auto row:profiles[i]){int left[15];for(int k=0;k<15;++k)left[k]=B[selected[i]][k];bool ok=true;for(int j:row){for(int u=0;u<5;++u){if(--left[3*u+words[selected[j]][u]]<0){ok=false;break;}}if(!ok)break;}if(ok){found=true;break;}}if(!found)return false;}return true;}long long nodes;bool limited=false,wall=false;
chrono::steady_clock::time_point started;
bool valid(int id){auto w=words[id];for(int u=0;u<5;++u)if(counts[u][w[u]]>=(w[u]?3:4))return false;
for(int k=0;k<10;++k){auto [u,v]=pairs[k];if(tabs[k][w[u]][w[v]]>=caps[k][w[u]][w[v]])return false;}return true;}
void search_colors(const vector<int>& cand){
 if(nodes>=100000){limited=true;return;}++nodes;
 if((nodes&1023)==0&&chrono::duration<double>(chrono::steady_clock::now()-started).count()>60){wall=limited=true;return;}
 int need=10-selected.size();if(!need){if(row_support())answer=selected;else ++rejected_colors;return;}if((int)cand.size()<need)return;
 for(int u=0;u<5;++u)for(int a=0;a<3;++a){int n=counts[u][a];for(int id:cand)n+=words[id][u]==a;if(n<(a?3:4))return;}
 for(size_t pos=0;pos<cand.size();++pos){int id=cand[pos];if(!valid(id))continue;auto w=words[id];
  for(int u=0;u<5;++u)++counts[u][w[u]];for(int k=0;k<10;++k){auto [u,v]=pairs[k];++tabs[k][w[u]][w[v]];}selected.push_back(id);
  vector<int> next;
  for(size_t j=pos+1;j<cand.size();++j){int agree=0;for(int u=0;u<5;++u)agree+=w[u]==words[cand[j]][u];if(agree<=3&&valid(cand[j]))next.push_back(cand[j]);}
  search_colors(next);
  selected.pop_back();for(int u=0;u<5;++u)--counts[u][w[u]];for(int k=0;k<10;++k){auto [u,v]=pairs[k];--tabs[k][w[u]][w[v]];}
  if(limited||!answer.empty())return;
 }
}
int main(){for(int i=0;i<243;++i){int x=i;for(int u=4;u>=0;--u){words[i][u]=x%3;x/=3;}}for(int u=0;u<5;++u)for(int v=u+1;v<5;++v)pairs.push_back({u,v});
for(int i=0;i<10;++i){vector<int> v;for(int j=0;j<10;++j)if(j!=i)v.push_back(j);
for(int a=0;a<9;++a)for(int b=a+1;b<9;++b){profiles[i].push_back({i,i,v[a],v[b]});for(int c=b+1;c<9;++c)for(int d=c+1;d<9;++d)profiles[i].push_back({v[a],v[b],v[c],v[d]});}
for(int j:v)for(int a:v)for(int b:v)if(a<b&&a!=j&&b!=j)profiles[i].push_back({j,j,a,b});if(profiles[i].size()!=414)return 3;}
int n;cin>>n;started=chrono::steady_clock::now();
for(int c=0;c<n;++c){int code,m;cin>>code>>m;vector<int> cand(m);for(int&i:cand)cin>>i;for(int k=0;k<10;++k)for(int a=0;a<3;++a)for(int b=0;b<3;++b)cin>>caps[k][a][b];if(!cin)return 2;
 int perms[6][3]={{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}},M[5][5][3],digits[10],z=code;for(int k=9;k>=0;--k){digits[k]=z%6;z/=6;}for(int k=0;k<10;++k){auto[u,v]=pairs[k];for(int a=0;a<3;++a){int b=perms[digits[k]][a];M[u][v][a]=b;M[v][u][b]=a;}}
for(int id=0;id<243;++id)for(int u=0;u<5;++u)for(int a=0;a<3;++a){int b=3-(words[id][u]!=0&&a==3-words[id][u]);for(int v=0;v<5;++v)if(v!=u)b-=M[v][u][words[id][v]]==a;B[id][3*u+a]=b;}
rejected_colors=0;nodes=0;limited=false;answer.clear();bool unvisited=wall||chrono::duration<double>(chrono::steady_clock::now()-started).count()>60;if(!unvisited)search_colors(cand);
 cout<<"{\"code\":"<<code<<",\"status\":\""<<(unvisited?"UNVISITED":limited?"UNKNOWN":answer.empty()?"COMPLETE_NEGATIVE":"ROW_SUPPORTED_COLORING")<<"\",\"nodes\":"<<nodes<<",\"rejected_colorings\":"<<rejected_colors<<",\"words\":[";for(size_t i=0;i<answer.size();++i)cout<<(i?",":"")<<answer[i];cout<<"]}\n";
}}
