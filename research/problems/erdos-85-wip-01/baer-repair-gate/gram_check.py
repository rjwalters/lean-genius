from collections import Counter
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
import json,runpy

root=Path(__file__).parent
with redirect_stdout(StringIO()):
    seed=runpy.run_path(str(root/'check.py'))
q=seed['q']; r=seed['p']; V=seed['V']; S=seed['S']
H=seed['H']; adj=seed['adj']; T=seed['T']
owner={v:next(iter(adj[v]&S)) for v in V}
groups={s:{v for v in V if owner[v]==s} for s in sorted(S)}
assert len(groups)==q+r+1 and set(map(len,groups.values()))=={q-r}
L={v:H[v]|({v} if v in T else set()) for v in V}
bits={v:sum(1<<u for u in L[v]) for v in V}
for v in V:
    assert len(L[v])==q
    for w in V:
        expected=q if v==w else int(owner[v]!=owner[w])
        assert (bits[v]&bits[w]).bit_count()==expected
R={s:{t:len(L[next(iter(groups[s]))]&groups[t]) for t in groups} for s in groups}
assert all(len(L[v]&groups[t])==R[s][t] for s in groups for v in groups[s] for t in groups)
assert all(R[s][t]==R[t][s] and R[s][t] in [0,1] for s in groups for t in groups)
assert all(sum(R[s].values())==q for s in groups)
assert all(sum(R[s][u]*R[u][t] for u in groups)==r*int(s==t)+q-r for s in groups for t in groups)
out={'PASS':True,'q':q,'group_count':len(groups),'group_size':q-r,
     'restored_loop_count':len(T),'quotient_diagonal_histogram':dict(Counter(R[s][s] for s in groups)),
     'identity':'L²=qI+J-K; R²=rI+(q-r)J',
     'scope':'dictionary check only; uniform impossibility proved in GRAM_GATE.md'}
(root/'gram-verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
