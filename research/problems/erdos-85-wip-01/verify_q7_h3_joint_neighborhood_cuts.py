"""Fraction-only Farkas certificates rejecting four specified H3 allocations."""
import json
from fractions import Fraction as F
from pathlib import Path

snapshots=json.loads(Path(__file__).with_name('q7_h3_joint_neighborhood_cuts.json').read_text())
assert {(a['profile'],a['class_label']) for a in snapshots}=={(p,k) for p in ['pair','triple'] for k in ['0','8']}
assert len(snapshots)==4
for snapshot in snapshots:
    groups=snapshot['groups'];N=len(groups)
    values=[list(map(F,g['vector'])) for g in groups]
    census=[25,6,6,1,6,1,1,0] if snapshot['profile']=='pair' else [24,7,7,0,7,0,0,1]
    assert [sum(g['count'] for g in groups if g['mask']==m) for m in range(8)]==census
    for g in groups:
        assert all(isinstance(g[k],int) for k in ['t','tau','mask','count'])
        assert 0<=g['mask']<8 and g['t']==g['mask'].bit_count() and g['count']>0
        assert int(g['t']==0)<=g['tau']<=3-g['t']
    assert any(any(v) for v in values)
    # Prescribed vectors are orthogonal to1, each high row, and their conjugates.
    for selector in [-1,0,1,2]:
        for k in range(2):
            assert sum(g['count']*v[k]*(1 if selector==-1 else (g['mask']>>selector)&1) for g,v in zip(groups,values))==0
    assert sum(g['count']*(v[0]**2-29*v[1]**2) for g,v in zip(groups,values))==0
    basic=[[1]*N]+[[(g['mask']>>h)&1 for g in groups] for h in range(3)]+[[v[k] for v in values] for k in range(2)]
    # Variables: C-only, D-only, both, each indexed by group.
    rows=[r+[0]*N+r for r in basic]+[[0]*N+r+r for r in basic]+[[0]*(2*N)+[1]*N]
    capacity_rows=[[int(j%N==i) for j in range(3*N)] for i in range(N)]
    cut=snapshot['cut'];i=cut['group'];assert 0<=i<N
    g=groups[i];aa,bb=values[i]
    rhs=[7-g['t'],1,1,1,(aa+29*bb)/2,(aa+bb)/2]+[6-g['t']]+[1-((g['mask']>>h)&1) for h in range(3)]+[(-3*aa-29*bb)/2,(-aa-3*bb)/2]+[7-2*g['t']-2*g['tau']]
    capacity=[a['count']-int(j==i) for j,a in enumerate(groups)]
    dual=list(map(F,cut['dual']));assert len(dual)==13+N
    assert all(v>=0 for v in dual[13:])
    combined=rows+capacity_rows
    assert all(sum(y*row[j] for y,row in zip(dual,combined))>=0 for j in range(3*N))
    bound=sum(y*b for y,b in zip(dual,rhs+capacity))
    assert bound==F(cut['bound'])==-1
    print('PASS',snapshot['profile'],snapshot['class_label'],'specified allocation impossible: nonnegative left side <= -1')
print('Four prescribed signed/support allocations excluded; no full residual polynomial or profile exclusion.')
