#!/usr/bin/env python3
"""Small exact C4 edge bounds and local-state DP, not a q7 graph search."""
import itertools
import json
import sympy as sp


def small_extremal(n):
    edges=list(itertools.combinations(range(n),2))
    best=-1; witness=[]; count=0
    for mask in range(1<<len(edges)):
        neighbors=[0]*n
        for k,(u,v) in enumerate(edges):
            if mask>>k&1:
                neighbors[u]|=1<<v;neighbors[v]|=1<<u
        if any((neighbors[u]&neighbors[v]).bit_count()>1 for u,v in edges):
            continue
        count+=1
        if mask.bit_count()>best:
            best=mask.bit_count()
            witness=[list(e) for k,e in enumerate(edges) if mask>>k&1]
    return {'order':n,'max_edges':best,'maximizing_graph_edges':witness,
            'C4free_labeled_graph_count':count}


def main():
    h,T,R=sp.symbols('h T R')
    Q=sp.Matrix([[0,8,h+7],[0,7,h],[1,-1,0]])
    fifth=sp.expand(12691+549*h+72*T+R-sp.trace(Q**5))
    assert fifth==R+72*T+269*h-4116
    moments=[0,sp.Integer(-7),294-13*h,21*h-343+6*T,2058-97*h,fifth]
    coeff=[sp.Integer(1)]
    for j in range(1,6):
        coeff.append(sp.expand(-sum(coeff[j-i]*moments[i] for i in range(1,j+1))/j))
    fifth_coeff={v:sp.factor(coeff[5].subs(h,v)) for v in (5,7)}
    assert sp.expand(5*fifth_coeff[5]+R-828*T-150709)==0
    assert sp.expand(5*fifth_coeff[7]+R-698*T-116991)==0
    ext=[small_extremal(n) for n in range(6)]
    assert [r['max_edges'] for r in ext]==[0,0,1,3,4,6]
    states=[]
    for t in range(4):
        for tau in range(4):
            k=7-2*t-2*tau
            if not 0<=k<=6-t:continue
            m=t+2*tau-1
            assert 0<=m<=5
            states.append({'t':t,'tau':tau,'common_CD_neighbors':k,
                           'remaining_vertices':m,'local_edge_bound':ext[m]['max_edges']})
    profiles=[]
    for h,name,counts in [(5,'T0',[14,20,10,0]),(5,'T1',[13,23,7,1]),
                           (5,'T2',[12,26,4,2]),(7,'T0',[7,14,21,0])]:
        dp={0:0}
        for t,n in enumerate(counts):
            choices=[r for r in states if r['t']==t]
            for _ in range(n):
                nxt={}
                for total,score in dp.items():
                    for row in choices:
                        k=total+row['tau'];value=score+row['local_edge_bound']
                        nxt[k]=max(nxt.get(k,-1),value)
                dp=nxt
        results=[]
        for total,score in sorted(dp.items()):
            if total%3:continue
            T=total//3;Rmax=2*score
            residues=[R for R in range(0,Rmax+1,2) if (R-3*T-(4 if h==5 else 1))%5==0]
            if h==7:
                formula=18*T-42-4*max(0,(3*T-42+1)//2)
                assert Rmax==formula
            results.append({'T':T,'R_upper_bound':Rmax,
                            'even_Newton_residue_min':min(residues) if residues else None,
                            'even_Newton_residue_max':max(residues) if residues else None,
                            'even_Newton_residue_step':10,
                            'even_Newton_residue_count':len(residues)})
        profiles.append({'h':h,'profile':name,'support_counts':counts,
                         'triangle_rows':results})
    assert profiles[2]['triangle_rows'][0]['T']==4
    assert profiles[2]['triangle_rows'][0]['even_Newton_residue_count']==0
    print(json.dumps({'scope':'Small graphs plus necessary local-state relaxation; no q7 realization',
                      'residual_fifth_moment':str(fifth),
                      'fifth_coefficients':{str(h):str(v) for h,v in fifth_coeff.items()},
                      'small_extremal':ext,'local_states':states,'profiles':profiles},indent=2))


if __name__=='__main__':main()
