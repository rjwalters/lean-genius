from pathlib import Path
import itertools,json
p=Path(__file__).resolve().parent;old=p.parent/'q9-order3-permutation-cover'
s=(old/'cover.cpp').read_text().replace('#include <vector>','#include <vector>\n#include <cstdint>')
s=s.replace('bool allowed[1296];','bool allowed[1296]; uint64_t masks[10][1296][4],coord[5][3][4];')
s=s.replace('for(auto [u,v]:edges){','uint64_t support[4]={~0ULL,~0ULL,~0ULL,(1ULL<<51)-1}; int edge_index=0;\n  for(auto [u,v]:edges){',1)
s=s.replace('if(!allowed[key]){++local_prunes;return;}','if(!allowed[key]){++local_prunes;return;}\n   int count=0;for(int b=0;b<4;++b){support[b]&=masks[edge_index][key][b];count+=__builtin_popcountll(support[b]);}\n   ++edge_index;if(count<10){++local_prunes;return;}',1)
s=s.replace('++retained;if(example.empty())','for(int u=0;u<5;++u)for(int a=0;a<3;++a){int count=0;for(int b=0;b<4;++b)count+=__builtin_popcountll(support[b]&coord[u][a][b]);if(count<(a?3:4)){++local_prunes;return;}}\n  ++retained;if(example.empty())',1)
s=s.replace('started=chrono::steady_clock::now();','for(int e=0;e<10;++e)for(int k=0;k<1296;++k)for(int b=0;b<4;++b){cin>>masks[e][k][b];if(!cin)return 3;}\n for(int u=0;u<5;++u)for(int a=0;a<3;++a)for(int b=0;b<4;++b){cin>>coord[u][a][b];if(!cin)return 4;}\n started=chrono::steady_clock::now();')
(p/'cover.cpp').write_text(s)
ps=list(itertools.permutations(range(3)));words=list(itertools.product(range(3),repeat=5));records=json.loads((p.parent/'q9-order3-local-contingency/results.json').read_text())['records'];bounds=[]
for r in records:
 perm=ps[r['direct']];U=[[3-int(a!=0 and perm[3-a]==b)-int(perm[a]!=0 and 3-perm[a]==b)-sum(ps[z][a]==b for z in r['paths']) for b in range(3)] for a in range(3)];bounds.append(U)
with (p/'input.txt').open('w') as f:
 f.write((old/'allowed.txt').read_text())
 for u,v in itertools.combinations(range(5),2):
  for U in bounds:
   bits=[0]*4
   for i,w in enumerate(words):
    if U[w[u]][w[v]]>0:bits[i//64]|=1<<(i%64)
   f.write(' '.join(map(str,bits))+'\n')
 for u in range(5):
  for a in range(3):
   bits=[0]*4
   for i,w in enumerate(words):
    if w[u]==a:bits[i//64]|=1<<(i%64)
   f.write(' '.join(map(str,bits))+'\n')
(p/'launch.json').write_text(json.dumps({'original_wall_cap_seconds':60,'roots':6,'raw_assignments':6**10,'retry':False,'scope':'permutation necessary constraints plus simultaneous color-word support; no chosen coloring or Q'},indent=2)+'\n')
