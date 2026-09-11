import json, hashlib
from pathlib import Path
base=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-order24-last-action')
out=Path(__file__).parent
checked={}
def pins(p):
 for name,expected in json.loads(p.read_text()).items():
  f=Path(name); f=f if f.is_absolute() else p.parent/f
  actual=hashlib.sha256(f.read_bytes()).hexdigest()
  assert actual==expected,(str(f),actual,expected)
  checked[str(f)]=actual
pins(base/'pins.json');pins(base/'input-pins.json')
for name in json.loads((base/'input-pins.json').read_text()):
 if name.endswith('/pins.json'):pins(Path(name))
reviews=json.loads((out/'premises.json').read_text())
assert len(reviews)==6 and all(r['status']=='resolved' and r['resolution'].startswith('PASS') for r in reviews)
d=json.loads((base.parent/'n78-s4-character/results.json').read_text())
cover={
 (3,3,4,8,12,24,24):2380,
 (4,4,4,6,12,24,24):2392,
 (4,4,4,6,6,6,24,24):2392,
 (4,6,6,6,8,24,24):2395,
 (4,6,8,12,12,12,24):2397,
 (4,6,6,6,8,12,12,24):2397}
rows=[];left=[]
for i,s in enumerate(d['solutions']):
 chars=[d['characters'][j]['values'] for j in s['indices']]
 assert [c[0] for c in chars]==s['sizes']
 assert [sum(c[j] for c in chars) for j in range(5)]==s['fixed_counts']
 r=cover.get(tuple(s['sizes']))
 rows.append({'index':i,'sizes':s['sizes'],'exclusion_review':r})
 if r is None:left.append(s)
assert len(rows)==9 and len(left)==1
s=left[0]
assert s['indices']==[2,2,2,7,7,7,8] and s['fixed_counts']==[78,6,0,6,6]
for h in d['characters'][2]['subgroups']:
 assert len(h)==4 and len(set(h)&set(d['classes'][4]))==2 and len(set(h)&set(d['classes'][3]))==1
for h in d['characters'][7]['subgroups']:
 assert len(h)==2 and len(set(h)&set(d['classes'][1]))==1
assert d['characters'][8]['subgroups']==[[0]]
result={'status':'PASS','checked_files':checked,'cover':rows,'remaining':s,'scope':'Necessary full order24 reduction only; last S4 action remains open.'}
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','hashes':len(checked),'covered':8,'remaining':1}))
