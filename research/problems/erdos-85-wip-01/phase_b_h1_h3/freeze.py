import csv,hashlib,json,re,collections,subprocess
from pathlib import Path
p=Path(__file__).parent
repo=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration')
def sha(f):
 h=hashlib.sha256()
 with f.open('rb') as s:
  for b in iter(lambda:s.read(1048576),b''):h.update(b)
 return h.hexdigest()
snapshot=json.loads((p/'h1-refresh-summary.json').read_text());source=Path(snapshot['source']);assert sha(source)==snapshot['source_sha256']
rows=list(csv.DictReader(source.open(),delimiter='\t'));assert len({r['tag'] for r in rows})==13351
objects=json.loads((p/'h1-object-list.json').read_text());present={Path(x['Key']).name.split('.')[0]:x for x in objects if x['Key'].endswith('.compact.lrat.gz') and x['Size']>0}
prior={r['tag'] for r in rows if r['certificate_ledger_valid']=='1' and r['tag'] in present}
fresh=json.loads((p/'h1-fresh-ledgers.json').read_text());new={}
for item in fresh:
 raw=item['raw'];assert hashlib.sha256(raw.encode()).hexdigest()==item['sha256']
 fields=raw.split();tag=Path(item['key']).stem;assert fields[1]==tag
 pairs=[x.split('=',1) for x in fields if '=' in x];assert len(dict(pairs))==len(pairs);a=dict(pairs)
 if 'UNSAT' not in fields:continue
 assert a.get('rc')=='20' and a.get('trim')=='VERIFIED' and a.get('compact')=='ok'
 assert a.get('upload') in {'uploaded','uploaded-v4-multipart-rescue'}
 assert all(re.fullmatch('[0-9a-f]{64}',a.get(k,'')) and a[k]!=hashlib.sha256(b'').hexdigest() for k in ['cnf_sha256','raw_lrat_sha256','compact_lrat_sha256','compact_gz_sha256'])
 assert int(a['raw_lrat_bytes'])>0 and int(a['compact_bytes'])>0 and tag in present
 new[tag]=item['key']
assert not prior.intersection(new)
remaining=[r for r in rows if r['tag'] not in prior|new.keys()]
compact=repo/'proofs/Proofs/Certificates/h1_orbit_inventory.compact';pairs=[(c,j) for c in range(8) for j in range(c+1,8) if j!=(c^1)];tables={}
for line in compact.read_text().splitlines():
 vals=list(map(int,line.split()));table={pair:v for pair,v in zip(pairs,vals[1:],strict=True) if v}
 tag=hashlib.sha1(json.dumps(sorted(table.items())).encode()).hexdigest()[:16];assert tag not in tables;tables[tag]=vals
for r in remaining:
 assert tables[r['tag']][0]==int(r['profile'])
 r['table_values']=tables[r['tag']][1:];r['cnf_path']=None;r['cnf_sha256']=None;r['materialization_status']='not yet inventoried';r['id']='h1_'+r['tag']
(p/'h1-frozen-candidates.json').write_text(json.dumps({'schema':'erdos85-phase-b-h1-candidates-v1','snapshot':snapshot['timestamp'],'scope':'Conservative unscreened producer remainder, not a complete fresh validation of prior screened certificates. No solver launch manifest until CNFs are materialized and bound.','count':len(remaining),'profile_counts':dict(collections.Counter(r['profile'] for r in remaining)),'source_sha256':sha(source),'compact_inventory_sha256':sha(compact),'rows':remaining},indent=2)+'\n')
generator=repo/'research/problems/erdos-85-wip-01/sat49/generate_small_high_canonical_cnfs.py';commit=subprocess.check_output(['git','log','-1','--format=%H','--',str(generator)],cwd=repo,text=True).strip()
h3=[]
for t in range(2):
 f=Path('/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/small-high-canonical-audit')/f'h3_t{t}.base.cnf'
 h3.append({'id':f'h3_t{t}_canonical','sector':'H3','cnf_path':str(f),'cnf_sha256':sha(f),'bytes':f.stat().st_size,'variables':29500,'clauses':1328183,'generator_path':str(generator),'generator_sha256':sha(generator),'generator_commit':commit,'regenerated_this_pass':False,'cross_check':True,'cap_seconds':None})
(p/'h3-inputs.json').write_text(json.dumps({'schema':'erdos85-phase-b-input-inventory-v1','scope':'Two canonical support-profile roots. Existing file hashes and clause counts checked against retained generation manifest; current source inspected but no regeneration this pass. Caps pending host plan.','instances':h3},indent=2)+'\n')
print({'remaining':len(remaining),'fresh_screened':len(new),'profile_counts':dict(collections.Counter(r['profile'] for r in remaining))})
