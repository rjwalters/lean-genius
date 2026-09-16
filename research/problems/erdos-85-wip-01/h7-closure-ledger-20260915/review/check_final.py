from pathlib import Path
import json,re,hashlib,sqlite3,itertools,collections
P=Path(__file__).parent
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
doc=R/'H7_CLOSURE_20260915.md'; raw=doc.read_bytes(); text=raw.decode()
m=R/'h7-frontier-map-20260915/overlay-a6f14-20260915/author/results.json'; rows=json.loads(m.read_text())['rows']; byid={r['id']:r for r in rows}
db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
seen=set();reviews={};links=[]
for line in text.splitlines():
 if not line.startswith('| `cube_'):continue
 cells=[v.strip() for v in line.split('|')[1:-1]];rid=cells[0].strip('`');assert rid not in seen;seen.add(rid);r=byid[rid];assert int(cells[1])==r['mask']
 refs=[int(n) for n in re.findall(r'\b\d{4}\b',cells[3])]
 if r['review_id'] is not None:assert r['review_id'] in refs,(rid,r['review_id'])
 else:assert 'pending' in cells[3]
 for n in refs:
  st,res=db.execute('select status,resolution from review_requests where id=?',(n,)).fetchone();assert st=='resolved' and res.startswith('PASS'),(rid,n,st);reviews[n]=res
 for link in re.findall(r'\]\(([^)]+)\)',cells[4]):assert (R/link).exists(),link;links.append(link)
assert seen==set(byid) and len(seen)==28
assert sum([395763,1253,89,100,5,1,23])==397234
assert sum([1757882,75027,445699])==2278608
assert 'paper plus computation, no Lean, no global claim' in text
assert 'not an independent exhaustive S-enumeration replay' in text
# Verify prose figures against archived reviewed results, not only arithmetic.
read=lambda n:json.loads((R/n).read_text())
capacity=read('q7_h7_universal_singleton_capacity.json');inventory=read('phase_b_h5_h7/h7-inventory.json')['mapping']
assert len(capacity)==len(inventory)==43
cap={(r['a'],r['mask']):r for r in capacity};assert len(cap)==43
survivors=[];pairs=list(itertools.combinations(range(7),2))
for item in inventory:
 c=cap[item['edge_count'],item['classification_mask']];perm=item['parent_to_classification_permutation']
 assert sorted(perm)==list(range(7))
 image={tuple(sorted((perm[u],perm[v]))) for k,(u,v) in enumerate(pairs) if item['mask']>>k&1}
 assert image==set(map(tuple,c['edges']))
 assert item['capacity_excluded']==c['excluded']
 if c['excluded']:assert c['upper_bound']<c['lower']
 else:survivors.append(item)
assert len(survivors)==28 and len(capacity)-len(survivors)==15
assert {r['id'] for r in survivors}==set(byid)
assert dict(collections.Counter(r['edge_count'] for r in survivors))=={6:7,7:12,8:7,9:2}
f12=read('q7_h7_a6_f12_closure/author/composition.json')
assert [p['negative_count'] for p in f12['parts']]==[395763,1253,89,100,5,1,23]
assert f12['total_host_leaves']==f12['covered']==397234 and f12['remaining']==0
f14=read('q7_h7_a6_f14_closure/review/COMPOSITION_REVIEW.json')
assert f14['counts']==[1757882,75027,445699] and f14['total']==2278608
cert=read('q7_h7_a6_f14_closure/review/REVIEW.json')
assert cert['negative']==445699 and cert['retained']==0 and cert['unvisited']==0
assert cert['tree_nodes']==1987996 and cert['tree_branches']==3812002
assert cert['counts']=={'INFEASIBLE_PROJECTION':175232,'EMPTY_FAMILY':270467}
locator=read('q7_h7_a6_f14_closure/author/receipt-locations.json')['files']['receipts-000.jsonl.gz']
assert locator['sha256'] in text and format(locator['bytes'],',') in text
external=Path(locator['path']);assert external.stat().st_size==locator['bytes'] and hashlib.sha256(external.read_bytes()).hexdigest()==locator['sha256']
for link in re.findall(r'\]\(([^)]+)\)',text):assert (R/link).exists(),link
for n in [1573,1574,1663,2091,2118,2122,2125,2123,2133,2120,2126,2116,2683,2111,2117,2666,2669,2107,2110,2114,2652,2715,2718,2719]:
 st,res=db.execute('select status,resolution from review_requests where id=?',(n,)).fetchone();assert st=='resolved' and res.startswith('PASS'),n;reviews[n]=res
assert '770b562433' in text and '045b96ac51' in text and '68ddf41f6a' in text
out={'status':'PASS_FINAL_LEDGER_IDENTITIES_REFERENCES_AND_ARCHIVED_COUNTS','document_sha256':hashlib.sha256(raw).hexdigest(),'map_sha256':hashlib.sha256(m.read_bytes()).hexdigest(),'rows':len(seen),'accepted_reviews':sorted(reviews),'archive_links':len(links),'scope':'Consolidated evidence-ledger audit, inheriting accepted computational proof scopes; no Lean/global proof.'}
(P/'FINAL_CHECK.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
