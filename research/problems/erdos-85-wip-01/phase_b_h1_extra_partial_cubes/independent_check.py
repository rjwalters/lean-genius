import pathlib,json,hashlib,re
P=pathlib.Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01');D=P/'phase_b_h1_extra_partial_cubes'
def sha(raw):return hashlib.sha256(raw).hexdigest()
pins=json.loads((D/'RECEIPT.json').read_text())['files']
for f,h in pins.items():assert sha((D/f).read_bytes())==h,f
mr=(P/'phase_b_h1_h3/h1-frozen-candidates.json').read_bytes();rows={r['tag']:r for r in json.loads(mr)['rows']}
records=json.loads((D/'results.json').read_text())['results'];native=json.loads((D/'native-results.json').read_text())['results'];assert len(records)==58 and len(native)==6
pairs=[(i,j) for i in range(8) for j in range(i+1,8) if i//2!=j//2];checks=[]
for entry in native:
 tag=entry['tag'];receipt=entry['native_receipt'];row=rows[tag]
 assert receipt['manifest_sha256']==sha(mr) and receipt['id']==row['id'] and receipt['tag']==tag and receipt['profile']==int(row['profile'])
 assert receipt['status']=='materialized' and receipt['container_absent'] is True and receipt['emit']['returncode']==receipt['check']['returncode']==0
 assert receipt['cnf_bytes']==receipt['emit']['stdout_bytes'] and receipt['expected_historical_sha256'] is None
 for name,key in [('materialize_h1_verdict_input.py','runner_sha256'),('materialize_verdict_input.py','validator_sha256')]:assert sha((P/'sat49'/name).read_bytes())==receipt[key]
 folder=pathlib.Path(receipt['receipt_path']).parent;raw=(folder/'table.json').read_bytes();assert sha(raw)==receipt['table_sha256']
 assert json.loads(raw)==[[list(pair),v] for pair,v in zip(pairs,row['table_values']) if v]
 assert (folder/'check.log').read_text().strip()==f"MATCH ({receipt['clauses']} clauses, top {receipt['variables']})"
 group=[r for r in records if r['tag']==tag];assert len(group)==entry['retained_cubes']<25
 assert all(not v for k,v in row.items() if k.endswith('cnf_sha256'))
 for r in group:
  data=pathlib.Path(r['cube_path']).read_bytes();assert sha(data)==r['cube_sha256'] and len(data)==r['cube_bytes']
  lines=data.splitlines(keepends=True);header=lines[0].split();n,m=map(int,header[2:]);assert n==receipt['variables'] and m==receipt['clauses']+2 and len(lines)==m+1
  assert all(re.fullmatch(rb'-?[1-9][0-9]* 0\n',line) for line in lines[-2:])
  units=[int(line.split()[0]) for line in lines[-2:]];assert units==r['removed_trailing_units'] and all(abs(u)<=n for u in units)
  h=hashlib.sha256(f'p cnf {n} {m-2}\n'.encode())
  for line in lines[1:-2]:h.update(line)
  assert h.hexdigest()==receipt['cnf_sha256']==r['derived_base_sha256']
  assert r['base_matches'] is None
 checks.append(dict(tag=tag,inputs_rehashed=len(group),native_table_and_receipt=True))
for f,h in pins.items():assert sha((D/f).read_bytes())==h
result=dict(review=2021,status='PASS',source_pins=pins,checks=checks,scope='All58 cube inputs rehashed/reconstructed; six native receipts/table/check logs joined. No proof bytes read or solver launched; no closure/eligibility claim')
pathlib.Path('review-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(checks,indent=2))
