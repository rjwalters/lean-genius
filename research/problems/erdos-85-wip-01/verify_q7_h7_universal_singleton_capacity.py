"""Universal H7 induced-class cuts via exact vertex-subset capacity certificates."""
import json
from itertools import combinations
from pathlib import Path
import verify_q7_h7_three_triangle_empty_classification as classification


def main():
    # Revalidate the entire induced domain and its full S7 orbit partition.
    classification.main()
    root=Path(__file__).parent
    domain=json.loads((root/'q7_h7_three_triangle_empty_classification.json').read_text())
    certificates=json.loads((root/'q7_h7_universal_singleton_capacity.json').read_text())
    expected=[(int(a),r['mask']) for a,d in domain.items() for r in d['orbits']]
    assert [(r['a'],r['mask']) for r in certificates]==expected
    cuts={a:0 for a in range(6,10)}
    for cert in certificates:
        a=cert['a']
        graph=next(r for r in domain[str(a)]['orbits'] if r['mask']==cert['mask'])
        assert cert['edges']==graph['edges']
        adj=[set() for _ in range(7)]
        for u,v in graph['edges']:adj[u].add(v);adj[v].add(u)
        allowed=[(u,v) for u,v in combinations(range(7),2) if not(adj[u]&adj[v])]
        cap=[7-2*len(s) for s in adj]
        assert cert['allowed']==list(map(list,allowed)) and cert['capacity']==cap
        lower=max(0,35-4*a)
        assert cert['lower']==lower
        # Every X edge touching U uses at least one degree unit in U.
        def upper(mask):
            return sum(cap[v] for v in range(7) if mask>>v&1)+sum(
                not(mask>>u&1 or mask>>v&1) for u,v in allowed)
        bound,mask=min((upper(s),s) for s in range(128))
        assert (bound,mask)==(cert['upper_bound'],cert['upper_subset'])
        if cert['excluded']:
            assert bound<lower and cert['witness'] is None
            cuts[a]+=1
        else:
            witness=list(map(tuple,cert['witness']))
            assert len(set(witness))==len(witness)==lower
            assert set(witness)<=set(allowed)
            assert all(sum(v in e for e in witness)<=cap[v] for v in range(7))
    assert cuts=={6:12,7:3,8:0,9:0}
    print('PASS:15 universal induced-class exclusions;28 satisfy this capacity test')
    print('No triangle-count or spectrum premise; no full H7 extension or exclusion claim')

if __name__=='__main__':main()
