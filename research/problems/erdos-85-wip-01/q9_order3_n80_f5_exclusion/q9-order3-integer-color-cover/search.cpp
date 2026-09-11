#include <array>
#include <vector>
#include <iostream>
#include <chrono>
using namespace std;
array<array<int,5>,243> words;vector<pair<int,int>> pairs;
int caps[10][3][3],tabs[10][3][3]={},counts[5][3]={};
vector<int> selected,answer;long long nodes;bool limited=false,wall=false;
chrono::steady_clock::time_point started;
bool valid(int id){auto w=words[id];for(int u=0;u<5;++u)if(counts[u][w[u]]>=(w[u]?3:4))return false;
for(int k=0;k<10;++k){auto [u,v]=pairs[k];if(tabs[k][w[u]][w[v]]>=caps[k][w[u]][w[v]])return false;}return true;}
void search_colors(const vector<int>& cand){
 if(nodes>=100000){limited=true;return;}++nodes;
 if((nodes&1023)==0&&chrono::duration<double>(chrono::steady_clock::now()-started).count()>60){wall=limited=true;return;}
 int need=10-selected.size();if(!need){answer=selected;return;}if((int)cand.size()<need)return;
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
int n;cin>>n;started=chrono::steady_clock::now();
for(int c=0;c<n;++c){int code,m;cin>>code>>m;vector<int> cand(m);for(int&i:cand)cin>>i;for(int k=0;k<10;++k)for(int a=0;a<3;++a)for(int b=0;b<3;++b)cin>>caps[k][a][b];if(!cin)return 2;
 nodes=0;limited=false;answer.clear();bool unvisited=wall||chrono::duration<double>(chrono::steady_clock::now()-started).count()>60;if(!unvisited)search_colors(cand);
 cout<<"{\"code\":"<<code<<",\"status\":\""<<(unvisited?"UNVISITED":limited?"UNKNOWN":answer.empty()?"COMPLETE_NEGATIVE":"INTEGER_COLORING")<<"\",\"nodes\":"<<nodes<<",\"words\":[";for(size_t i=0;i<answer.size();++i)cout<<(i?",":"")<<answer[i];cout<<"]}\n";
}}
