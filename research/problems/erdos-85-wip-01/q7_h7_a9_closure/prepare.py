import pathlib,json,gzip,hashlib,shutil
P=pathlib.Path(__file__).parent;S=pathlib.Path('/Users/rwalters/lean-genius-q7-outside-first-20260910');T=pathlib.Path('/tmp');origins={}
def read(path):
 raw=path.read_bytes();origins[str(path)]=hashlib.sha256(raw).hexdigest();return json.loads(gzip.decompress(raw) if path.suffix=='.gz' else raw)
def write(name,data):(P/name).write_text(json.dumps(data,indent=2)+'\n')
def gh(adj):return hashlib.sha256(json.dumps([sorted(ns) for ns in adj],separators=(',',':')).encode()).hexdigest()
profiles=read(T/'erdos85-sol1-h7-profile-partitions/remaining-results.json')['results'];write('profiles.json',[r for r in profiles if (r['twins_adjacent'],r['profile_index']) in [(True,6),(False,14)]])
write('seeds.json',read(T/'erdos85-sol1-h7-high0-cover/results.json'));write('normalization.json',read(T/'erdos85-sol1-h7-max-high-cover/results.json'))
local=read(T/'erdos85-sol1-h7-crossed14-local/results.json');arc=read(S/'h7-crossed14-arc/results.json.gz');lookup={r['source_index']:r for r in arc['results']};assert len(lookup)==448
neg=read(T/'erdos85-sol1-h7-crossed14-local/independent-negatives.json');ni={r['assignment_index'] for r in neg['results']};assert len(ni)==32 and all(r['c4_free_rows']==0 for r in neg['results'])
rows=[]
for i,r in enumerate(local['results']):
 if r['status']=='INFEASIBLE':assert r['assignment_index'] in ni and i not in lookup;endpoint='LOCAL'
 else:assert r['status']=='LOCAL_FEASIBLE' and lookup[i]['status']=='INFEASIBLE_ARC';endpoint='ARC'
 rows.append({'assignment_index':r['assignment_index'],'endpoint':endpoint,'graph_sha256':gh(r['adjacency']) if 'adjacency' in r else None,'vertex':r.get('vertex')})
write('crossed14-endpoints.json',rows)
twin=read(S/'h7-twin6-arc/results.json.gz');assert twin['summary']['unvisited']==0;rows=[]
for r in twin['results']:
 assert r['status'] in ['INFEASIBLE_LOCAL','INFEASIBLE_ARC']
 rows.append({'assignment_index':r['assignment_index'],'endpoint':'LOCAL' if r['status']=='INFEASIBLE_LOCAL' else 'ARC','graph_sha256':gh(r['adjacency']) if 'adjacency' in r else None,'vertex':r.get('vertex')})
write('twin6-endpoints.json',rows)
write('crossed14-census.json',read(T/'erdos85-sol1-h7-crossed14-census-review/results.json'));write('twin6-census.json',read(pathlib.Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/twin6-census-review/results.json')))
write('origins.json',origins);print('Prepared3120endpoint projections with exact input graph hashes')
