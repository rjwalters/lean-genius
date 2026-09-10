#!/usr/bin/env python3
"""Verify a continuous moment measure exactly; never invokes an optimizer."""
from fractions import Fraction as F
import json
from pathlib import Path


def main():
    data=json.loads(Path(__file__).with_name('q7_h7_fifth_moment_measure.json').read_text())
    nodes=list(map(F,data['nodes']));weights=list(map(F,data['weights']))
    assert len(nodes)==len(weights)==7 and all(w>0 for w in weights)
    T,R=data['T'],data['R']
    assert T==10 and R==96
    assert 3<=T<=23 and R>=0 and R%2==0 and (R-3*T-1)%5==0
    bound=18*T-42-4*max(0,(3*T-42+1)//2)
    assert bound==data['R_upper_bound']==138 and R<=bound
    targets=[34,-7,203,6*T-196,1379,R+72*T-2233]
    actual=[sum(w*x**k for x,w in zip(nodes,weights)) for k in range(6)]
    assert actual==targets==list(map(F,data['moments']))
    positive=sum(w for x,w in zip(nodes,weights) if x>0)
    negative=sum(w for x,w in zip(nodes,weights) if x<0)
    assert positive==data['positive_mass']==17 and negative==17
    for x in nodes:
        y=x*x
        # (7-sqrt21)/2 < y < (17+sqrt21)/2, without floating point.
        lo=7-2*y;hi=2*y-17
        assert lo<0 or lo*lo<21
        assert hi<0 or hi*hi<21
    assert any(w.denominator!=1 for w in weights)
    print('PASS: exact seven-atom moment measure, strict intervals, positive mass17, R bound/residue; not an integral spectrum or graph')


if __name__=='__main__':main()
