"""Exact Gaussian-integer local lemmas used by the independent paper audit."""
import itertools,json
from pathlib import Path
P=Path(__file__).resolve().parent
units=((1,0),(0,1),(-1,0),(0,-1))
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def times(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def pi_div(a):return (a[0]-a[1])%2==0
def two_div(a):return a[0]%2==a[1]%2==0
tables={}
for k in (1,2,4):
    rows=[]
    for residues in itertools.combinations_with_replacement(range(4),k):
        parity=sum((-1)**t for t in residues)
        value=(sum(units[t][0] for t in residues),sum(units[t][1] for t in residues))
        if k==2:
            assert pi_div(value)
            if parity==0:assert value[0]**2+value[1]**2==2
            else:assert two_div(value)
        if k==4:
            assert pi_div(value)
            if parity==0:assert two_div(value)
        rows.append((residues,parity,value))
    tables[k]=rows
# At i the determinant of X is a unit product minus product of two four-sums.
for p,s in itertools.product(units,repeat=2):
    for _,_,q in tables[4]:
        for _,_,r in tables[4]:
            ps=times(p,s);qr=times(q,r)
            assert not pi_div(add(ps,(-qr[0],-qr[1])))
# Mixed-case contradiction: ±2 times a unit is not divisible by 2*pi.
for u in units:
    first=(2*u[0],2*u[1]);assert not ((first[0]-first[1])%4==0 and two_div(first))
# Same-parity two-set forces balanced four-set by odd-difference count.
for r in range(5):
    if 2*r*(4-r) in (8,10):assert r==2
result={'status':'PASS','two_unit_multisets':len(tables[2]),'four_unit_multisets':len(tables[4]),
        'invertible_X_cases':16*len(tables[4])**2,
        'scope':'exact local Gaussian arithmetic; full case-exhaustion proof in REVIEW.md'}
(P/'arithmetic.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
