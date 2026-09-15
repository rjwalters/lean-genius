"""Bounded downstream F0 hosts using the byte-pinned accepted API."""
import collections
import gzip
import hashlib
import importlib.util
import itertools
import json
import sqlite3
import time
from pathlib import Path
from highs import ROOT, OUT, SOURCE, inputs, graph

API = ROOT / 'q7_h7_monotone_host_api/original'

def given_high(g, pairing):
    a = [set() for _ in range(49)]
    ren = lambda v: v+42 if v < 7 else v
    def add(u, v):
        a[u].add(v)
        a[v].add(u)
    for u in range(21):
        for v in g[u]:
            if u < v:
                add(ren(u), ren(v))
    for v, (i,j) in enumerate(itertools.combinations(range(7), 2), 21):
        add(v, i)
        add(v, j)
    for h,d in enumerate(pairing):
        add(h, 14+h)
        add(h, 7+d)
    return [sorted(ns) for ns in a]

def run():
    db = sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro', uri=True)
    db.row_factory = sqlite3.Row
    reviews = []
    for rid in [2116, 2123, 2654]:
        r = dict(db.execute('select * from review_requests where id=?', (rid,)).fetchone())
        assert r['status'] == 'resolved' and r['resolution'].startswith('PASS')
        reviews.append(r)
    for root, pinfile in [(API,'pins.json'), (OUT,'high-pins.json')]:
        for name,h in json.loads((root/pinfile).read_text()).items():
            assert hashlib.sha256((root/name).read_bytes()).hexdigest() == h
    launch_high = json.loads((OUT/'high-launch.json').read_text())
    for name,h in launch_high['source_pins'].items():
        assert hashlib.sha256((SOURCE/name).read_bytes()).hexdigest() == h
    spec = importlib.util.spec_from_file_location('accepted_hosts', API/'api.py')
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    cover, cases = inputs()
    high = json.loads((OUT/'high-results.json').read_text())
    assert all(r['status']=='COMPLETE' for r in high['results'])
    assert high['summary']['unvisited'] == 0
    total = sum(len(r['pairings']) for r in high['results'])
    assert total == 18408
    launch = dict(total=total, aggregate_seconds=60, per_graph_nodes=100000,
                  shard_bytes=50000000, total_artifact_cap=150000000,
                  reviews=reviews, api_pins=json.loads((API/'pins.json').read_text()),
                  driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    with (OUT/'host-launch.json').open('x') as f:
        json.dump(launch,f,indent=2)
    start = time.monotonic()
    deadline = start+60
    counts = collections.Counter()
    visited = negative = leaves = prunes = nodes = size = allsize = 0
    shards = []
    unknown = []
    stream = None
    stop = None
    for r in high['results']:
        if stop:
            break
        case = cases[r['case_index']]
        assert (r['source_index'],r['singleton_index']) == case[:2]
        base = graph(cover,case)
        for pi,pairing in enumerate(r['pairings']):
            remaining = deadline-time.monotonic()
            if remaining <= 0:
                stop='AGGREGATE_CAP'
                break
            receipt = api.enumerate_hosts(given_high(base,pairing),max_nodes=100000,seconds=remaining)
            assert receipt['status'] in ['COMPLETE','UNKNOWN']
            record = dict(case_index=r['case_index'],pairing_index=pi,
                          source_index=r['source_index'],singleton_index=r['singleton_index'],receipt=receipt)
            blob=gzip.compress((json.dumps(record,separators=(',',':'))+'\n').encode(),mtime=0)
            assert len(blob)<50000000
            if stream is None or size+len(blob)>50000000:
                if stream:
                    stream.close()
                name=f'hosts-{len(shards):03d}.jsonl.gz'
                shards.append(name)
                stream=(OUT/name).open('xb')
                size=0
            stream.write(blob)
            size+=len(blob)
            allsize+=len(blob)
            visited+=1
            counts[receipt['status']]+=1
            nodes+=receipt['nodes']
            if receipt['status']=='UNKNOWN':
                unknown.append([r['case_index'],pi])
            else:
                negative+=not receipt['solutions']
                leaves+=len(receipt['solutions'])
                prunes+=len(receipt['prunes'])
            if allsize>=150000000:
                stop='ARTIFACT_CAP'
                break
    if stream:
        stream.close()
    result=dict(total=total,visited=visited,unvisited=total-visited,counts=dict(counts),
                negative_high_graphs=negative,surviving_leaves=leaves,pruned_prefixes=prunes,
                nodes=nodes,unknown=unknown,stop=stop,shards=shards,
                artifact_bytes=allsize,seconds=time.monotonic()-start)
    (OUT/'host-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))

if __name__=='__main__':
    run()
