import pathlib,json,itertools,hashlib
B=pathlib.Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01');P=B/'q7_h5_t2_chain_audit'
for f,h in json.loads((P/'pins.json').read_text()).items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h
report=json.loads((P/'results.json').read_text())
for f,h in report['source_pins'].items():assert hashlib.sha256((B/f).read_bytes()).hexdigest()==h
masks=[7,25,10,18,12,20];pairs=list(itertools.combinations(range(6),2));valid=[]
for code in range(32768):
 adj=[set() for _ in range(6)]
 for i,(u,v) in enumerate(pairs):
  if code>>i&1:adj[u].add(v);adj[v].add(u)
 if any((masks[u]&masks[v]).bit_count()+len(adj[u]&adj[v])>1 for u,v in pairs):continue
 good=True
 for u in range(6):
  supports=[masks[v] for v in adj[u]]
  if any(a&b for a,b in itertools.combinations(supports,2)):good=False;break
  weight=sum(m.bit_count() for m in supports)
  if weight>5 or masks[u].bit_count()+len(adj[u])>7 or 2-masks[u].bit_count()+weight-len(adj[u])<0:good=False;break
 if good:valid.append(code)
trans=[]
for p in itertools.permutations(range(5)):
 renamed=[sum(1<<p[c] for c in range(5) if m>>c&1) for m in masks]
 if set(renamed)!=set(masks):continue
 hp=[masks.index(m) for m in renamed];trans.append([pairs.index(tuple(sorted((hp[u],hp[v])))) for u,v in pairs])
canon={min(sum(1<<tr[i] for i in range(15) if n>>i&1) for tr in trans) for n in valid}
assert len(valid)==report['labelled']==52 and sorted(canon)==report['canonical_cores'] and len(trans)==8
left=set(canon)
for stage in report['stages']:
 assert sorted(left)==stage['before'];review=json.loads((B/stage['review_file']).read_text());assert review['id']==stage['review'] and review['status']=='resolved' and review['resolution'].startswith('PASS')
 removed=set(stage['excluded']);assert len(removed)==len(stage['excluded']) and removed<=left;left-=removed;assert sorted(left)==stage['after']
assert left=={44} and report['remaining']==[44]
out=dict(status='PASS',independent_method='Algebraic heavy-pair common-neighbour counts and disjoint neighbour supports, then all support automorphisms',labelled=52,canonical=13,automorphisms=8,source_files=len(report['source_pins']),remaining=[44],scope='Census and exact reviewed reduction cover only; no new exclusion')
print(out);pathlib.Path(__file__).with_name('result.json').write_text(json.dumps(out,indent=2)+'\n')
