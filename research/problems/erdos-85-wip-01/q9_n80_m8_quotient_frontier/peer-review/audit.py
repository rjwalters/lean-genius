from pathlib import Path
import collections, gzip, hashlib, itertools, json, math
src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/q9-n80-m8-quotient')
pins=json.loads((src/'pins.json').read_text())
for f,h in pins.items(): assert hashlib.sha256((src/f).read_bytes()).hexdigest()==h
launch=json.loads((src/'launch.json').read_text())
assert launch['source_sha256']==pins['cover.cpp'] and launch['binary_sha256']==pins['cover']
assert launch['caps']==dict(nodes_per_root=100000,seconds=60,artifact_bytes=20000000)
roots=[]; profiles=0
for a in range(3):
    for row in itertools.combinations_with_replacement(range(4),9):
        if a+sum(row)!=9 or a*a+sum(x*x for x in row)>15: continue
        roots.append([a]+list(row))
        mult=math.factorial(9)
        for n in collections.Counter(row).values(): mult//=math.factorial(n)
        profiles+=mult
assert len(roots)==13 and profiles==7846
raw=gzip.decompress((src/'receipts.jsonl.gz').read_bytes())
assert raw==(src/'receipts.jsonl').read_bytes()
records=[json.loads(s) for s in raw.splitlines()]
counts=collections.Counter(); receipts=[]; unique=set()
for rec in records:
    if 'matrix' not in rec:
        if 'case' in rec: receipts.append(rec)
        continue
    q=rec['matrix']; r=rec['root']; assert q[0]==roots[r]
    assert len(q)==10 and all(len(row)==10 and sum(row)==9 for row in q)
    assert all(type(q[i][j]) is int and 0<=q[i][j]<=(2 if i==j else 3) and q[i][j]==q[j][i]
               for i in range(10) for j in range(10))
    sq=[[sum(q[i][k]*q[k][j] for k in range(10)) for j in range(10)] for i in range(10)]
    assert all(sq[i][j]<=(15 if i==j else 8) for i in range(10) for j in range(10))
    # A positive internal-degree-two edge forces unequal colours: solve the
    # resulting equations over F2 by exhaustive 10-bit assignment.
    edges=[(i,j) for i in range(10) for j in range(i) if q[i][i]==q[j][j]==2 and q[i][j]]
    assert any(all(((mask>>i)^(mask>>j))&1 for i,j in edges) for mask in range(1024))
    for i in range(10):
        assert all(not(q[i][i]==q[j][j]==1 and q[i][j]) for j in range(10) if i!=j)
        if (9-q[i][i])%2:
            assert any(q[i][j] and sq[i][j]!=8 for j in range(10) if i!=j)
    key=tuple(tuple(row) for row in q); assert key not in unique; unique.add(key)
    counts[r]+=1
expected=json.loads((src/'results.json').read_text())
assert receipts==expected['cases'] and records[-1]==expected['summary']
assert [r['case'] for r in receipts]==list(range(13))
assert all(r['status']=='UNKNOWN' and r['reason']=='nodes' and r['nodes']==100000
           and r['retained']==counts[r['case']] for r in receipts)
assert sum(counts.values())==24
out=dict(status='PASS_RETAINED_ONLY',pins_verified=len(pins),profiles=profiles,roots=len(roots),
         retained_checked=24,complete=0,unknown=13,unvisited_roots=0,capped_domains_replayed=False)
Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
