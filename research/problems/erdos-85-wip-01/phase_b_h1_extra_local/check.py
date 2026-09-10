"""Recheck the extra local H1 evidence; no generator, solver or proof replay."""
import argparse,hashlib,json,re
from pathlib import Path

def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()

def main():
 ap=argparse.ArgumentParser();ap.add_argument('frozen_manifest',type=Path);a=ap.parse_args();p=Path(__file__).parent
 r=json.loads((p/'extra-local-result.json').read_text());audit=json.loads((p/'extra-local-audit.json').read_text());n=r['materialization_receipt'];tag=audit['tag'];raw=a.frozen_manifest.read_bytes()
 assert hashlib.sha256(raw).hexdigest()==n['manifest_sha256']==audit['manifest_sha256']
 rows=[x for x in json.loads(raw)['rows'] if x['tag']==tag];assert len(rows)==1;row=rows[0]
 assert r['tag']==n['tag']==tag and n['id']==row['id']=='h1_'+tag
 assert n['profile']==int(row['profile'])==audit['profile']==1
 assert n['status']=='materialized' and n['emit']['returncode']==n['check']['returncode']==0 and n['container_absent'] is True
 assert r['status']=='BYTE_MATCH' and r['canonical_sha256']==n['cnf_sha256']==audit['canonical_sha256']
 matches=[b for b in r['baselines'] if b['sha256']==n['cnf_sha256']];assert len(matches)==1
 cnf=Path(matches[0]['path']);assert sha(cnf)==n['cnf_sha256'];assert cnf.stat().st_size==n['cnf_bytes']==r['canonical_bytes']
 for name,record in audit['metadata'].items():
  b=Path(name).read_bytes();assert hashlib.sha256(b).hexdigest()==record['sha256'];assert b.decode()==record['raw']
 parent=cnf.parent.parent;lines=[x.split('\t') for x in audit['metadata'][str(parent/'manifest.tsv')]['raw'].splitlines()];lines=[x for x in lines if x[0]==tag];assert len(lines)==1
 assert int(lines[0][1])==n['profile'] and list(map(int,lines[0][3].split()))==row['table_values']
 pairs=[(i,j) for i in range(8) for j in range(i+1,8) if j!=(i^1)]
 sparse=[(pair,v) for pair,v in zip(pairs,row['table_values'],strict=True) if v]
 assert hashlib.sha1(json.dumps(sparse).encode()).hexdigest()[:16]==tag
 verdict=audit['metadata'][str(cnf.with_suffix('.verdict'))]['raw']
 assert verdict.split()==[tag,'UNSAT','214.0s','drat:VERIFIED','mode:MONO','arm:v2','lean-exact:MATCH','profile:1']
 log=audit['metadata'][str(cnf.parent/(tag+'.drat-trim.log'))]['raw'];assert [s for s in log.splitlines() if s.startswith('s ')]==['s VERIFIED']
 m=re.search(r'formula with (\d+) variables and (\d+) clauses',log);assert (int(m[1]),int(m[2]))==(n['variables'],n['clauses'])==(audit['variables'],audit['clauses'])
 print(json.dumps({'tag':tag,'status':'HISTORICAL_EVIDENCE_RECHECKED','cnf_sha256':n['cnf_sha256'],'proof_replayed':False,'overlay_changed':False}))
if __name__=='__main__':main()
