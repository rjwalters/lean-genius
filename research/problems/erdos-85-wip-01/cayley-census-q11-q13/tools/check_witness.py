#!/usr/bin/env python3
"""Independent SAT-model and adjacency verification; imports no encoder code."""
import argparse,hashlib,json
from pathlib import Path

def check_graph(data,selected,q):
    n=data['order'];t=data['table'];s=set(selected)
    assert len(s)==q and 0 not in s and all(0<a<n for a in s),'selection size/range'
    adj=[sorted(t[x][a] for a in s) for x in range(n)]
    assert all(len(row)==len(set(row))==q for row in adj),'degree'
    for x,row in enumerate(adj):
        assert x not in row,'loop'
        for y in row:assert x in adj[y],'asymmetric adjacency'
    # Every unordered endpoint pair can have at most one intermediate vertex.
    # Enumerate neighbor pairs centered at each vertex, independent of products.
    centers={}
    for middle,row in enumerate(adj):
        for j,a in enumerate(row):
            for b in row[:j]:
                pair=(min(a,b),max(a,b))
                assert pair not in centers,('C4',pair,centers.get(pair),middle)
                centers[pair]=middle
    return adj

def check(group,cnf,log,q):
    data=json.loads(group.read_text());lines=log.read_text().splitlines()
    assert [s for s in lines if s.startswith('s ')]==['s SATISFIABLE'],'not unique SAT status'
    assignment={}
    for line in lines:
        if line.startswith('v '):
            for word in line.split()[1:]:
                lit=int(word)
                if lit:
                    assert abs(lit) not in assignment or assignment[abs(lit)]==(lit>0),'conflicting assignment'
                    assignment[abs(lit)]=lit>0
    pending=[];checked=0;variables=clauses=None
    with cnf.open() as f:
        for line in f:
            if line.startswith('c') or not line.strip():continue
            if line.startswith('p '):
                _,kind,v,c=line.split();assert kind=='cnf';variables=int(v);clauses=int(c);continue
            for word in line.split():
                lit=int(word)
                if lit:pending.append(lit)
                else:
                    assert all(abs(x) in assignment for x in pending),'incomplete model'
                    assert any(assignment[abs(x)]==(x>0) for x in pending),('unsatisfied clause',checked)
                    checked+=1;pending=[]
    assert not pending and checked==clauses and variables is not None,'DIMACS counts'
    assert all(a in assignment for a in range(1,data['order'])),'missing selection'
    selected=[a for a in range(1,data['order']) if assignment[a]]
    adjacency=check_graph(data,selected,q)
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    return {'status':'PASS','small_group_id':data.get('small_group_id'),'order':data['order'],'degree':q,'edges':data['order']*q//2,'cnf_clauses_checked':checked,'selected':selected,'adjacency':adjacency,'group_sha256':sha(group),'cnf_sha256':sha(cnf),'log_sha256':sha(log)}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('group',type=Path);p.add_argument('cnf',type=Path);p.add_argument('log',type=Path);p.add_argument('q',type=int);p.add_argument('output',type=Path);a=p.parse_args()
    result=check(a.group,a.cnf,a.log,a.q);a.output.write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k!='adjacency'})
