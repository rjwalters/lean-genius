"""Refined singleton families and exact weighted-capacity certificates.
Floating LP proposes weights only; all exclusion decisions use integer arithmetic.
"""
import gzip,hashlib,itertools,json,math,sqlite3,time
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
D=Path(__file__).parent;T=Path('/Users/rwalters/lean-genius-h7-a6-f12-triangle-family-sol2-20260915')
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01');S=R/'q7_h7_a6_f12_host/original'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def matching(left,edges):
 if not left:return True
 h=left&-left
 return any(m&h and m&left==m and matching(left^m,edges) for m in edges)
def families(g):
 out={};capacity=[7-g[s].bit_count() for s in range(7,21)]
 for p in range(21,42):
  old=[w for w in range(49) if g[p]>>w&1];demand=7-2*g[p].bit_count();assert demand in [1,3]
  candidates=[s for s in range(7,21) if all(not(g[s]&g[w]) for w in old)];fs=[]
  for singletons in itertools.combinations(candidates,demand):
   if any(g[a]&g[b] for a,b in itertools.combinations(singletons,2)):continue
   used=0
   for s in singletons:used|=g[s]&127
   assert used.bit_count()==demand;left=127^used
   supports=[g[q]&127 for q in range(21,42) if q!=p and not((g[q]&127)&~left) and all(not(g[q]&g[w]) for w in old+list(singletons))]
   if matching(left,supports):fs.append(sum(1<<(s-7) for s in singletons))
  out[p]=fs
 assert sum(capacity)==39
 return out,capacity

def weighted_cut(fs,capacity,seconds):
 for p,rows in fs.items():
  if not rows:return {'kind':'EMPTY_FAMILY','pair_vertex':p},None
 constraints=[]
 for p,rows in fs.items():
  for f in rows:
   row=[-int(f>>s&1) for s in range(14)]+[int(q==p) for q in range(21,42)];constraints.append(row)
 res=linprog(np.array(capacity+[-1]*21,dtype=float),A_ub=np.array(constraints,dtype=float),b_ub=np.zeros(len(constraints)),bounds=[(-1,1)]*14+[(None,None)]*21,method='highs',options={'time_limit':max(.001,seconds)})
 info={'status':int(res.status),'message':str(res.message),'objective':float(res.fun) if res.fun is not None else None}
 if res.x is None:return None,info
 fractions=[Fraction(0) if abs(float(x))<1e-8 else Fraction(float(x)).limit_denominator(1000) for x in res.x[:14]]
 scale=math.lcm(*(f.denominator for f in fractions));weights=[int(f*scale) for f in fractions];div=math.gcd(*weights)
 if div:weights=[x//div for x in weights]
 score=lambda f:sum(w for s,w in enumerate(weights) if f>>s&1)
 lower=sum(min(map(score,rows)) for rows in fs.values());actual=sum(w*c for w,c in zip(weights,capacity))
 if lower>actual:return {'kind':'WEIGHT_CAPACITY','weights':weights,'minimum':lower,'capacity':actual},info
 return None,info

def main():
 assert not (D/'launch.json').exists();db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);st,review=db.execute('select status,resolution from review_requests where id=2711').fetchone();assert st=='resolved' and review.startswith('PASS')
 for base in [T,S]:
  for n,h in read(base/'pins.json').items():assert sha(base/n)==h,n
 cases=read(T/'results.json')['remaining'];assert len(cases)==24;ids={gid for gid,j in cases}
 bases={r['global_index']:[sum(1<<v for v in ns) for ns in r['neighbors']] for r in map(json.loads,gzip.open(S/'inputs.jsonl.gz','rt')) if r['global_index'] in ids};hosts={}
 for name in read(S/'results.json')['shards']:
  for r in map(json.loads,gzip.open(S/name,'rt')):
   if r['global_index'] in ids:hosts[r['global_index']]=r['receipt']['solutions']
 (D/'launch.json').write_text(json.dumps({'seconds':60,'lp_seconds_per_case':2,'cases':24,'source_manifest':sha(T/'pins.json'),'host_manifest':sha(S/'pins.json'),'driver':sha(Path(__file__)),'review2711':review},indent=2)+'\n')
 start=time.monotonic();certs=[];remaining=[];diagnostics=[];unvisited=[]
 for index,(gid,j) in enumerate(cases):
  if time.monotonic()-start>=60:unvisited=cases[index:];break
  g=bases[gid][:]
  for e,m in enumerate(hosts[gid][j],42):
   g[e]|=m
   for v in range(49):
    if m>>v&1:g[v]|=1<<e
  fs,capacity=families(g);cut,info=weighted_cut(fs,capacity,min(2,60-(time.monotonic()-start)))
  diagnostics.append({'global_index':gid,'leaf_index':j,'lp':info,'family_counts':{p:len(rows) for p,rows in fs.items()}})
  if cut:cut.update(global_index=gid,leaf_index=j,families=fs);certs.append(cut)
  else:remaining.append([gid,j])
 out={'status':'COMPLETE_PROBE' if not unvisited else 'CAPPED_PROBE','total':24,'killed':len(certs),'certificates':certs,'remaining':remaining,'unvisited':unvisited,'diagnostics':diagnostics,'seconds':time.monotonic()-start,'scope':'Exact integer weighted capacity or empty necessary family only. LP verdict alone never an exclusion; all survivors explicit.'}
 (D/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['certificates','remaining','unvisited','diagnostics']}));print('remaining',len(remaining),'unvisited',len(unvisited))
if __name__=='__main__':main()
