"""One bounded downstream pair-host pass on the completed F13 high cover."""
import collections
import gzip
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sqlite3
import time

P = Path(__file__).parent
ROOT = Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
API = ROOT/'q7_h7_monotone_host_api/original'
db = sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
premises = {}
import argparse
parser=argparse.ArgumentParser();parser.add_argument('--source-review',type=int,required=True);args=parser.parse_args()
for rid in (2116,2123,args.source_review):
    r = db.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone()
    assert r and r[0]=='resolved' and r[1].startswith('PASS'), (rid,r)
    premises[rid] = r
for name,h in json.loads((P/'high-pins.json').read_text()).items():
    assert hashlib.sha256((P/name).read_bytes()).hexdigest()==h
api_pins = json.loads((API/'pins.json').read_text())
for name,h in api_pins.items():
    assert hashlib.sha256((API/name).read_bytes()).hexdigest()==h
launch = json.loads((P/'high-launch.json').read_text())
SOURCE = Path(launch['source_path'])
for name,h in launch['source_pins'].items():
    assert hashlib.sha256((SOURCE/name).read_bytes()).hexdigest()==h
cover = json.loads((SOURCE/'results.json').read_text())
from highs import inputs
cover,cases=inputs()
highs = json.loads((P/'high-results.json').read_text())
edges={(si,sj):es for si,sj,es in cases}
assert len(edges)==14124 and len(highs['results'])==14124
assert all(r['status']=='COMPLETE' for r in highs['results'])
total = sum(len(r['pairings']) for r in highs['results'])
assert total==360172
spec = importlib.util.spec_from_file_location('accepted_host_api',API/'api.py')
api = importlib.util.module_from_spec(spec)
spec.loader.exec_module(api)
out = P/'hosts'
out.mkdir(exist_ok=True)

def fixed_high(row, pairing):
    rep = cover['representatives'][row['source_index']]
    assert rep['F_index']==13
    adj = [set() for _ in range(49)]
    def add(u,v): adj[u].add(v);adj[v].add(u)
    def ren(u): return u+42 if u<7 else u
    for u,v in rep['F_edges']+edges[(row['source_index'],row['singleton_index'])]: add(ren(u),ren(v))
    for s,hs in enumerate(rep['singleton_hosts'],7):
        for e in hs: add(s,42+e)
    for p,(u,v) in enumerate(itertools.combinations(range(7),2),21): add(p,u);add(p,v)
    for h,d in enumerate(pairing): add(h,14+h);add(h,7+d)
    return adj

# Validate every input before the sole launch; no search is performed here.
checked = 0
for row in highs['results']:
    for pairing in row['pairings']:
        adj = fixed_high(row,pairing)
        assert all(len(adj[v])==8 for v in range(7))
        assert all(len(adj[v])<=7 for v in range(7,49))
        assert all(u not in adj[u] for u in range(49))
        assert all(u in adj[v] for u in range(49) for v in adj[u])
        assert all(len(adj[u]&adj[v])<=1 for u in range(49) for v in range(u))
        checked += 1
assert checked==total
with (out/'launch.json').open('x') as f:
    json.dump({'total':total,'max_nodes':100000,'aggregate_seconds':600,'shard_byte_cap':50000000,
               'artifact_byte_cap':1000000000,'input_graphs_checked':checked,
               'premises':premises,'api_path':str(API),'api_pins':api_pins,
               'high_results_sha256':hashlib.sha256((P/'high-results.json').read_bytes()).hexdigest(),
               'runner_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},f,indent=2)
start = time.monotonic()
deadline = start+600
counts = collections.Counter()
visited = nodes = negative = prunes = 0
leaves = partial_leaves = 0
unknown = []
shards = []
stream = None
size = 0
allsize = 0
stop = None
discarded_at_cap = 0
for row in highs['results']:
    if stop: break
    si,sj = row['source_index'],row['singleton_index']
    for pi,pairing in enumerate(row['pairings']):
        remaining=deadline-time.monotonic()
        if remaining<=0: stop='AGGREGATE_CAP';break
        adj=fixed_high(row,pairing)
        receipt=api.enumerate_hosts(adj,max_nodes=100000,seconds=remaining)
        assert receipt['status'] in ('COMPLETE','UNKNOWN')
        record={'case_index':row['case_index'],'pairing_index':pi,'source_index':si,'singleton_index':sj,'receipt':receipt}
        blob=gzip.compress((json.dumps(record,separators=(',',':'))+'\n').encode(),mtime=0)
        assert len(blob)<50000000
        if allsize+len(blob)>1000000000:
            stop='ARTIFACT_CAP';discarded_at_cap=1;break
        if stream is None or size+len(blob)>50000000:
            if stream: stream.close()
            name=f'receipts-{len(shards):03d}.jsonl.gz'
            shards.append(name);stream=(out/name).open('xb');size=0
        stream.write(blob);size+=len(blob);allsize+=len(blob)
        visited+=1;counts[receipt['status']]+=1;nodes+=receipt['nodes'];prunes+=len(receipt['prunes'])
        if receipt['status']=='UNKNOWN':
            unknown.append([row['case_index'],pi])
            partial_leaves+=len(receipt['solutions'])
        else:
            negative+=not receipt['solutions']
            leaves+=len(receipt['solutions'])
        if allsize>=1000000000: stop='ARTIFACT_CAP';break
if stream: stream.close()
result={'total':total,'visited':visited,'unvisited':total-visited,'counts':dict(counts),
        'negative_high_graphs':negative,'surviving_host_leaves_complete':leaves,
        'host_leaves_unknown_cases':partial_leaves,'pruned_prefixes':prunes,'artifact_bytes':allsize,
        'nodes':nodes,'unknown_high_graphs':unknown,'receipt_shards':shards,'seconds':time.monotonic()-start,'stop':stop,
        'computed_but_not_saved_at_artifact_cap':discarded_at_cap,
        'scope':'Necessary pair-host cover; no residual-edge or whole-root exclusion.'}
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='unknown_high_graphs'},indent=2))
