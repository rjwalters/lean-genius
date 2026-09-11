"""Single pass on independently accepted singleton-shortcut survivors."""
import argparse,array,collections,ctypes,gzip,hashlib,importlib.util,json,pathlib,sqlite3,time
P=pathlib.Path(__file__).parent
A=pathlib.Path('/tmp/erdos85-sol1-h7-projection-extension')
S=pathlib.Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h7-projection-singleton-shortcut-pass')
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--source-review',type=int,required=True);args=ap.parse_args()
    assert not (P/'launch.json').exists() and not (P/'results.json').exists(), 'No overwrite or retry'
    db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);db.row_factory=sqlite3.Row
    reviews=[]
    for rid in [2110,2111,args.source_review]:
        r=dict(db.execute('select * from review_requests where id=?',(rid,)).fetchone())
        assert r['status']=='resolved' and r['resolution'].startswith('PASS'),r
        reviews.append(r)
    assert str(S) in str(reviews[-1]['refs']), 'Source review must address the shortcut pass'
    for root in [A,S,pathlib.Path('/tmp/erdos85-sol1-h7-singleton-complete-native-api')]:
        for f,h in json.loads((root/'pins.json').read_text()).items():assert hashlib.sha256((root/f).read_bytes()).hexdigest()==h
    accepted=pathlib.Path('/tmp/erdos85-sol1-h7-singleton-complete-native-api/filter.cpp')
    assert (P/'filter.cpp').read_bytes()==accepted.read_bytes()
    data=json.loads(gzip.decompress((A/'results.json.gz').read_bytes()))
    source=json.loads((A/'source-results.json').read_text());comp=json.loads((A/'source-completion-results.json').read_text())
    edges={(r['source_index'],j):es for r in comp['results'] for j,es in enumerate(r['solutions'])}
    previous=json.loads((S/'results.json').read_text());survivors=json.loads((S/'survivors.json').read_text())
    expected=[[r['case_index'],i] for r in previous['results'] for i,c in enumerate(r['certificates']) if c=='.']
    assert survivors==expected and len(survivors)==previous['summary']['survivors']
    # Prior UNKNOWN/unvisited domains remain outside this survivor pass.
    groups=collections.defaultdict(list)
    for ci,ai in survivors:groups[ci].append(ai)
    spec=importlib.util.spec_from_file_location('extension',A/'run.py');ext=importlib.util.module_from_spec(spec);spec.loader.exec_module(ext)
    lib=ctypes.CDLL(str(P/'batch.dylib'));lib.batch_check.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.POINTER(ctypes.c_uint32),ctypes.c_int,ctypes.c_int,ctypes.c_double];lib.batch_check.restype=ctypes.c_char_p
    (P/'premises.json').write_text(json.dumps(reviews,indent=2)+'\n')
    (P/'input-survivors.json').write_bytes((S/'survivors.json').read_bytes())
    (P/'source-pins.json').write_bytes((S/'pins.json').read_bytes())
    (P/'launch.json').write_text(json.dumps(dict(total=len(survivors),max_nodes=100000,seconds=60,source_unknown=previous['summary']['unvisited']))+'\n')
    counts=collections.Counter();visited=nodes=0;retained=[];start=time.monotonic();deadline=start+60
    with gzip.open(P/'receipts.jsonl.gz','wt') as output:
        for ci,indices in groups.items():
            if time.monotonic()>deadline:break
            r=data['results'][ci];g=ext.base(source['representatives'][r['source_index']],edges[r['source_index'],r['singleton_index']],source['F_edges'])
            base=(ctypes.c_uint64*21)(*(sum(1<<v for v in ns) for ns in g))
            flat=array.array('I',(v for ai in indices for chunk in r['solutions'][ai] for v in chunk));assert flat.itemsize==4
            raw=lib.batch_check(base,(ctypes.c_uint32*len(flat)).from_buffer(flat),len(indices),100000,deadline)
            receipts=json.loads(raw);assert len(receipts)<=len(indices)
            for ai,receipt in zip(indices,receipts):
                assert receipt['status'] in ['INFEASIBLE_ROW','INFEASIBLE_ARC','ARC_FEASIBLE','UNKNOWN'],receipt
                output.write(json.dumps(dict(case_index=ci,assignment_index=ai,receipt=receipt),separators=(',',':'))+'\n')
                visited+=1;nodes+=receipt['nodes'];counts[receipt['status']]+=1
                if receipt['status'] in ['ARC_FEASIBLE','UNKNOWN']:retained.append([ci,ai,receipt['status']])
    result=dict(total=len(survivors),visited=visited,unvisited=len(survivors)-visited,counts=dict(counts),nodes=nodes,seconds=time.monotonic()-start,prior_unvisited=previous['summary']['unvisited'],retained=retained)
    (P/'results.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k!='retained'})
if __name__=='__main__':main()
