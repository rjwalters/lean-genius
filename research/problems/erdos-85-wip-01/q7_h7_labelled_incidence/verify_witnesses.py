"""Check saved partial graphs without importing the search implementation."""
import itertools
import json
from pathlib import Path

data=json.loads(Path(__file__).with_name('pilot-1.json').read_text())
checked=0
for row in data['results']:
    if row['status']!='PARTIAL_WITNESS':
        assert row['status']=='UNKNOWN_AT_CAP'
        continue
    listed=row['witness']['partial_edges'];edges={tuple(e) for e in listed}
    assert len(edges)==len(listed) and all(0<=u<v<49 for u,v in edges)
    A=[[int(tuple(sorted((i,j))) in edges) if i!=j else 0 for j in range(49)] for i in range(49)]
    assert [sum(A[i]) for i in range(7)]==[8]*7
    assert [sum(A[i]) for i in range(7,14)]==[7]*7
    assert all(sum(A[i][k]*A[j][k] for k in range(49))<=1 for i,j in itertools.combinations(range(49),2))
    for color in range(7):
        assert {v for v in range(14,28) if A[color][v]}=={14+2*color,15+2*color}
    for i,pair in enumerate(itertools.combinations(range(7),2)):
        assert {c for c in range(7) if A[c][28+i]}==set(pair)
    assert {(u-7,v-7) for u,v in edges if 7<=u<v<14}=={tuple(e) for e in row['empty_edges']}
    assert all(sum(A[v][i] for i in range(7,14))<=2 for v in range(14,28))
    assert all(sum(A[v][i] for i in range(7,14))<=1 for v in range(28,49))
    checked+=1
assert checked==26
print('PASS:26 saved C4-free partial graphs;2 unknown cases; no complete graph or exclusion')
