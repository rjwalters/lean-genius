"""Independently check a generator handoff's complete cyclic edge partition."""
import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def check(cnf, mapping, generator, n, d, m):
    meta = json.loads(mapping.read_text())
    assert (meta['n'], meta['minimum_degree'], meta['m']) == (n,d,m)
    assert n % m == 0 and m>1
    assert meta['cnf_sha256'] == digest(cnf)
    assert meta['generator_sha256'] == digest(generator)
    translate = lambda v: m*(v//m)+(v+1)%m
    remaining = set(itertools.combinations(range(n),2))
    expected = set()
    while remaining:
        pair = min(remaining)
        orbit = set()
        while pair not in orbit:
            orbit.add(pair)
            pair = tuple(sorted(map(translate,pair)))
        assert orbit <= remaining
        remaining -= orbit
        expected.add(frozenset(orbit))
    actual = []
    variables = []
    for row in meta['orbits']:
        edges = [tuple(e) for e in row['edges']]
        assert len(set(edges)) == len(edges)
        assert all(0<=u<v<n for u,v in edges)
        actual.append(frozenset(edges))
        variables.append(row['var'])
    assert len(actual) == len(set(actual)) and set(actual) == expected
    assert len(variables) == len(set(variables))
    assert all(1<v<=meta['variables'] for v in variables)
    count = 0
    pending = False
    header = None
    with cnf.open() as f:
        for line in f:
            if not line.strip() or line.startswith('c'):
                continue
            if line.startswith('p '):
                assert header is None
                p,fmt,nv,nc = line.split()
                assert fmt=='cnf'
                header = int(nv),int(nc)
            else:
                assert header is not None
                for literal in map(int,line.split()):
                    assert abs(literal)<=header[0]
                    if literal:
                        pending = True
                    else:
                        count += 1
                        pending = False
    assert not pending and header == (meta['variables'],meta['clauses'])
    assert count == meta['clauses']
    return dict(status='PASS',n=n,d=d,m=m,edge_orbits=len(actual),
                orbit_sizes=dict(Counter(map(len,actual))),
                expanded_edges=n*(n-1)//2,variables=header[0],clauses=count,
                cnf_sha256=digest(cnf),map_sha256=digest(mapping),generator_sha256=digest(generator),
                scope='input hashes, DIMACS bounds/count, and complete cyclic edge partition; not encoding semantics or a graph verdict')


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    for name in ['cnf','map','generator','output']:
        parser.add_argument('--'+name,type=Path,required=True)
    for name in ['n','d','m']:
        parser.add_argument('--'+name,type=int,required=True)
    a=parser.parse_args()
    assert not a.output.exists()
    result=check(a.cnf,a.map,a.generator,a.n,a.d,a.m)
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
