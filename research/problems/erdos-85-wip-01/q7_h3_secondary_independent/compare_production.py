#!/usr/bin/env python3
"""Compare the independent census with exact R-loop ASTs from production searches.

Only the top-level secondary graph enumeration loop is executed. The expensive
U enumeration and terminal searches are never executed. Hash the whole source
and extracted loop so this comparison can be audited separately from census.py.
"""
import ast
from collections import Counter
from itertools import combinations, permutations, product
import hashlib
import json
from pathlib import Path
import census

SOURCES = ['verify_q7_h3_triple_m1_r3_singleton_exclusion.py',
           'verify_q7_h3_triple_m1_r4_singleton_exclusion.py',
           'verify_q7_h3_triple_m2_singleton_exclusion.py']


def compare(root):
    result, assignment = census.census()
    independent = {o['representative'] for o in result['orbits']}
    comparisons=[]
    for name in SOURCES:
        path=root/name;raw=path.read_bytes();tree=ast.parse(raw)
        candidates=[node for node in tree.body if isinstance(node,ast.For)
                    and isinstance(node.target,ast.Name) and node.target.id=='m'
                    and isinstance(node.iter,ast.List)
                    and ast.literal_eval(node.iter)==[1,2,3]]
        assert len(candidates)==1
        loop=candidates[0]
        source=ast.get_source_segment(raw.decode(),loop)
        namespace={'combinations':combinations,'permutations':permutations,'product':product,
                   'Counter':Counter,'pairs':census.EDGES,'idx':census.INDEX,'out':{},
                   'print':lambda *a,**kw:None}
        exec(compile(ast.Module(body=[loop],type_ignores=[]),str(path),'exec'),namespace)
        matches=[]
        for m,group in namespace['out'].items():
            for offset,row in enumerate(group['representatives']):
                key=census.encode(row['edges'])
                assert key in assignment
                actual=census.admissible(row['edges'])
                assert actual==(int(m),row['r'])
                matches.append({'m':int(m),'r':row['r'],'source_index':offset,
                                'source_edges':row['edges'],'independent_representative':assignment[key]})
        images=[r['independent_representative'] for r in matches]
        assert len(images)==len(set(images))==len(independent)
        assert set(images)==independent
        comparisons.append({'source':name,'source_sha256':hashlib.sha256(raw).hexdigest(),
                            'loop_sha256':hashlib.sha256(source.encode()).hexdigest(),
                            'loop_first_line':loop.lineno,'loop_last_line':loop.end_lineno,
                            'status':'BIJECTION','matches':matches})
    # The m=3 terminal program explicitly uses this unique secondary graph.
    fixed=[(0,1),(2,3),(4,5),(6,7)]
    assert census.admissible(fixed)==(3,4)
    assert sum(o['m']==3 for o in result['orbits'])==1
    return {'scope':'R-side census joins only; U cases and terminal rejections not rerun',
            'independent_labelled_survivors':result['labelled_survivors'],
            'independent_orbits':len(independent),'comparisons':comparisons,
            'm3_fixed_graph_representative':assignment[census.encode(fixed)]}


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();result=compare(Path(__file__).resolve().parent.parent)
    with args.output.open('x') as out:json.dump(result,out,indent=2);out.write('\n')
    print('Three exact production R generators biject with all 21 independent orbits; unique m3 graph joins.')
