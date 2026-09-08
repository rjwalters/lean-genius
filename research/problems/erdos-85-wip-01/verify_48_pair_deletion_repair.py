"""Exclude addition-only degree repair after two deletions in two fixed hosts.

This is not a search over all 46-vertex graphs and does not exclude edge
switching that deletes further surviving edges. NetworkX decodes sparse6;
all graph checks below use explicit sets and paths.
"""
from collections import Counter
from hashlib import sha256
from itertools import combinations
from pathlib import Path

import networkx as nx

HERE = Path(__file__).resolve().parent
DATA = HERE / 'sat49' / 'data'
ARCHIVE_HASH = '7bc1de35449c8eee0133cecf38d6ed9875d7412f4c952aa50157f2beb96484c9'
WITNESS_HASH = 'e07e25f36d2f0bc0e48cb0b036e99d3c78a39f4731581081207716eeb5f2f68b'


def check_host(label, graph):
    assert set(graph)==set(range(48))
    adj=[set(graph[u]) for u in range(48)]
    assert graph.number_of_edges()==168
    assert all(len(row)==7 for row in adj)
    assert all(u not in adj[u] for u in range(48))
    assert all(len(adj[u]&adj[v])<=1 for u,v in combinations(range(48),2))
    checked=0
    deficit_histogram=Counter()
    for x,y in combinations(range(48),2):
        removed={x,y}
        retained=[u for u in range(48) if u not in removed]
        remaining={u:adj[u]-removed for u in retained}
        deficit={u:7-len(remaining[u]) for u in retained if adj[u]&removed}
        assert deficit and sum(deficit.values())==14-2*int(y in adj[x])
        deficit_histogram[sum(deficit.values())]+=1
        # Restoring degree seven by additions alone can only join two
        # deficit vertices. Every such nonedge already closes a 3-path.
        for u,v in combinations(deficit,2):
            if v in remaining[u]:
                continue
            path=next(((a,b) for a in remaining[u]
                       for b in remaining[a]&remaining[v]),None)
            assert path is not None,(label,x,y,u,v)
            a,b=path
            assert len({u,a,b,v})==4
            assert a in remaining[u] and b in remaining[a] and v in remaining[b]
        checked+=1
    assert checked==1128
    print(f'{label}: all {checked} deletions have zero safe deficit-endpoint edges; '
          f'deficit sums {dict(sorted(deficit_histogram.items()))} PASS')


def main():
    archive=(DATA/'c4_n48e168.maybe.s6').read_bytes()
    assert sha256(archive).hexdigest()==ARCHIVE_HASH
    lines=archive.splitlines()
    assert len(lines)==10
    witness_bytes=(DATA/'boza48_witness.s6').read_bytes()
    assert sha256(witness_bytes).hexdigest()==WITNESS_HASH
    witness=witness_bytes.splitlines()
    assert len(witness)==1
    check_host('Boza48',nx.from_sparse6_bytes(witness[0]))
    check_host('Afzaly-McKay archive #9',nx.from_sparse6_bytes(lines[9]))
    print('Only these two hosts and addition-only repairs are excluded.')


if __name__=='__main__':
    main()
