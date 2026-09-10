"""Read-only independent audit of native/historical comparison receipts; no solving."""
import argparse, collections, hashlib, json
from pathlib import Path

def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''): h.update(b)
 return h.hexdigest()

def main():
 ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path);ap.add_argument('manifest',type=Path);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 p=a.directory; raw=a.manifest.read_bytes(); mh=hashlib.sha256(raw).hexdigest(); rows={r['tag']:r for r in json.loads(raw)['rows']}
 jobs=json.loads((p/'remote-candidate-paths.json').read_text()); expected={j['tag']:set(j['paths']) for j in jobs}
 result_raw=(p/'full-results.json').read_bytes(); d=json.loads(result_raw); results=d['results']; tags=[r['tag'] for r in results]
 assert len(tags)==len(set(tags)); assert set(tags)<=set(expected)
 pairs=[(i,j) for i in range(8) for j in range(i+1,8) if j != (i^1)]
 output=[]
 for r in results:
  tag=r['tag']; row=rows[tag]; receipt=r['materialization_receipt']; table=[[list(pair),v] for pair,v in zip(pairs,row['table_values']) if v]
  assert hashlib.sha1(json.dumps([(tuple(k),v) for k,v in table]).encode()).hexdigest()[:16]==tag
  assert receipt['manifest_sha256']==mh and receipt['profile']==int(row['profile'])
  assert json.loads((p/'work'/tag/'table.json').read_text())==table
  assert sha(p/'work'/tag/'table.json')==receipt['table_sha256']
  assert json.loads((p/'work'/tag/'receipt.json').read_text())==receipt
  assert receipt['status']=='materialized' and receipt['container_absent'] is True
  assert receipt['emit']['returncode']==receipt['check']['returncode']==0
  assert receipt['cnf_sha256']==r['canonical_sha256'] and receipt['cnf_bytes']==r['canonical_bytes']
  assert set(b['path'] for b in r['baselines'])==expected[tag]
  matches=[]
  for b in r['baselines']:
   cnf=Path(b['path']); h=sha(cnf); assert h==b['sha256']; assert cnf.stat().st_size==b['bytes']
   vp=Path(b['verdict_path']); rawv=vp.read_text() if vp.exists() else '';assert rawv==b['verdict']
   fields=rawv.split(); valid=bool(fields and fields[0]==tag and {'UNSAT','drat:VERIFIED','arm:v2'}<=set(fields) and 'table:' in rawv and sorted(json.loads(rawv.split('table:',1)[1]))==table)
   assert valid==b['verified_verdict_and_table']
   if h==r['canonical_sha256']:
    mode=next((t[5:] for t in fields if t.startswith('mode:')),None)
    matches.append({'path':str(cnf),'verified_verdict_and_table':valid,'mode':mode,'verdict_sha256':hashlib.sha256(rawv.encode()).hexdigest() if rawv else None,'proof_files':b['proof_paths']})
  assert len(matches)==r['byte_matching_baselines']
  verified=[b for b in matches if b['verified_verdict_and_table']]
  assert len(verified)==r['matching_verified_baselines']
  assert r['status']==('BYTE_MATCH' if matches else 'DIFFERENT')
  output.append({'tag':tag,'profile':int(row['profile']),'canonical_sha256':r['canonical_sha256'],'matches':matches,'paired_verified':bool(verified),'verified_modes':sorted({b['mode'] or 'UNSPECIFIED' for b in verified})})
 summary={'expected':len(expected),'audited':len(output),'all_expected_present':set(tags)==set(expected),'byte_matches':sum(bool(x['matches']) for x in output),'paired_verified':sum(x['paired_verified'] for x in output),'without_paired_verified':[x['tag'] for x in output if not x['paired_verified']],'verified_mode_sets':dict(collections.Counter(','.join(x['verified_modes']) or 'NONE' for x in output)),'manifest_sha256':mh,'comparison_results_sha256':hashlib.sha256(result_raw).hexdigest(),'solver_launched':False,'proof_replay_performed':False,'automatic_exclusions':0,'scope':'Input bytes rehashed; recorded historical verdict and table independently re-read. Proof file paths and sizes are historical metadata only. MONO and CUBE25 are distinct; no proof validity or cube-cover claim.','results':output}
 a.output.write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k!='results'},indent=2))
if __name__=='__main__': main()
