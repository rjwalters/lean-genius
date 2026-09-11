"""One high-pairing pass, with projection and algorithm acceptance guards."""
import ctypes,gzip,hashlib,json,pathlib,sqlite3,time
P=pathlib.Path(__file__).parent
S=pathlib.Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/h7-a6-empty-singleton-projection')
A=pathlib.Path('/tmp/erdos85-sol1-h7-a6-high-api')
def main():
 assert not (P/'high-launch.json').exists() and not (P/'high-results.json').exists(), 'No overwrite or retry'
 db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);db.row_factory=sqlite3.Row;premises=[]
 for rid in [2118,2119]:
  r=dict(db.execute('select * from review_requests where id=?',(rid,)).fetchone());assert r['status']=='resolved' and r['resolution'].startswith('PASS'),r;premises.append(r)
 for root in [S,A]:
  for f,h in json.loads((root/'pins.json').read_text()).items():assert hashlib.sha256((root/f).read_bytes()).hexdigest()==h
 for f in ['cover-results.json','completion-results.json','pins.json']:(P/('source-'+f)).write_bytes((S/f).read_bytes())
 cover=json.loads((S/'cover-results.json').read_text());comp=json.loads((S/'completion-results.json').read_text());assert comp['status']=='COMPLETE' and comp['unvisited']==0
 cases=[(i,j,r,es) for i,r in enumerate(comp['results']) for j,es in enumerate(r['solutions'])];assert len(cases)==3284
 lib=ctypes.CDLL(str(A/'high.dylib'));lib.high_pairings.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.c_int,ctypes.c_double];lib.high_pairings.restype=ctypes.c_char_p
 (P/'high-premises.json').write_text(json.dumps(premises,indent=2)+'\n')
 (P/'high-launch.json').write_text(json.dumps(dict(cases=3284,seconds=60,max_nodes_per_ES_graph=100000,compressed_artifact_stop_bytes=90000000))+'\n')
 start=time.monotonic();visited=total=nodes=unknown=empty=0;artifact_stop=False
 with open(P/'high-colourings.jsonl.gz','wb') as raw:
  with gzip.GzipFile(fileobj=raw,mode='wb',mtime=0) as stream:
   for i,j,r,edges in cases:
    if time.monotonic()-start>60:break
    F=cover['cases'][r['F_index']];X=F['representatives'][r['X_index']];g=[0]*21
    for a,b in F['F_edges']+edges:g[a]|=1<<b;g[b]|=1<<a
    for s,hs in enumerate(X['singleton_hosts'],7):
     for e in hs:g[s]|=1<<e;g[e]|=1<<s
    answer=json.loads(lib.high_pairings((ctypes.c_uint64*21)(*g),100000,60-(time.monotonic()-start)))
    answer.update(completion_index=i,singleton_index=j,F_index=r['F_index'],X_index=r['X_index'])
    stream.write((json.dumps(answer,separators=(',',':'))+'\n').encode());stream.flush()
    visited+=1;total+=len(answer['colourings']);nodes+=answer['nodes'];unknown+=answer['status']=='UNKNOWN';empty+=answer['status']=='COMPLETE' and not answer['colourings']
    if raw.tell()>90000000:artifact_stop=True;break
 summary=dict(total_cases=3284,visited=visited,unvisited=3284-visited,unknown=unknown,complete=visited-unknown,empty=empty,colourings=total,nodes=nodes,seconds=time.monotonic()-start,artifact_stop=artifact_stop)
 (P/'high-results.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary)
if __name__=='__main__':main()
