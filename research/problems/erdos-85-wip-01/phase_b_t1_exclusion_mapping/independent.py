from pathlib import Path
import json,re,itertools,hashlib
repo=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration');root=repo/'research/problems/erdos-85-wip-01';I=json.loads((root/'phase_b_survivors_20260910.json').read_text());H=json.loads((root/'phase_b_h5_h7/h5-inventory.json').read_text());B=H['bases']['h5_t1'];raw=Path(B['base']).read_bytes();assert hashlib.sha256(raw).hexdigest()==B['base_sha256']
lean=(repo/'proofs/Proofs/Erdos85OrderFortyNineFiveHighCanonicalMasks.lean').read_text();m=re.search(r'def orderFortyNineFiveHighT1Masks : Array Nat :=\s*#\[([^]]+)\]',lean);masks=[int(x.strip()) for x in m.group(1).split(',')];assert len(masks)==49
lines=raw.splitlines();body=[l for l in lines if l.strip() and l.split()[0] not in (b'c',b'p')];assert len(body)==1328618
units=[int(l.split()[0]) for l in body[:230]];assert all(l.split()[-1]==b'0' and len(l.split())==2 for l in body[:230]);expected=set()
var=0
for u in range(49):
 for v in range(u+1,49):
  var+=1
  if u<5:expected.add(var if masks[v]>>u&1 else -var)
assert len(expected)==230 and set(units)==expected and len(set(map(abs,units)))==230
header=b'p cnf 29632 1328618\n';assert raw.count(header)==1
changed=raw.replace(header,b'p cnf 29632 1328620\n',1);index={r['id']:r for r in I['cases']};assert len(index)==len(I['cases']);mapped=[]
for k,r in enumerate(H['jobs']):
 if r['cell']!='h5_t1':continue
 assert r['units']==[B['left'][r['left_index']],B['right'][r['right_index']]]
 full=changed+b''.join(str(lit).encode()+b' 0\n' for lit in r['units']);digest=hashlib.sha256(full).hexdigest();x=index[r['id']]
 assert digest==r['cnf_sha256']==x['cnf_sha256'] and len(full)==r['cnf_bytes'] and x['source_index']==k and x['sector']=='H5'
 mapped.append(r['id'])
assert len(mapped)==len(set(mapped))==43 and set(mapped)=={r['id'] for r in I['cases'] if r['id'].startswith('h5_t1.')}
result=dict(mapped_count=43,fixed_support_literals=230,base_clause_count=len(body),ids=mapped,mask_source='Lean literal definition, independently parsed',scope='Exact input identity only; no CNF-to-graph theorem, solver verdict, kernel exclusion, or queue change')
Path('independent-result.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k!='ids'})
