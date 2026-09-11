from pathlib import Path
import sys,json
p=Path(__file__).resolve().parent;sys.path.insert(0,str(p.parent/'q9-order3-fractional-residual'));from model import model,ps,pairs
m=model(24538199);z=24538199;ds=[0]*10
for i in range(9,-1,-1):ds[i]=z%6;z//=6
P={}
for (u,v),z in zip(pairs,ds):P[u,v]=ps[z];P[v,u]=tuple(ps[z].index(a) for a in range(3))
with (p/'input.txt').open('w') as f:
 f.write(str(len(m['words']))+'\n')
 for i,w in enumerate(m['words']):
  B=[3-int(w[u]!=0 and a==3-w[u])-sum(P[v,u][w[v]]==a for v in range(5) if v!=u) for u in range(5) for a in range(3)]
  adj=[j if i==h else h for h,j in m['edges'] if i in (h,j)]
  f.write(' '.join(map(str,[*w,*B,len(adj),*adj]))+'\n')
(p/'launch.json').write_text(json.dumps({'code':24538199,'original_wall_cap_seconds':60,'scope':'necessary local row support with common-middle bound; fixed point removal','retry':False},indent=2)+'\n')
