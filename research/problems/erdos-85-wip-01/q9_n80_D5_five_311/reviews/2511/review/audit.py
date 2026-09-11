from pathlib import Path
import json,hashlib,sqlite3,time
p=Path(__file__).parent;b=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3');src=b/'residual-ten-D5-five-311-composition';read=lambda f:json.loads(f.read_text());start=time.monotonic();hashes={}
def pins(path):
 for n,h in read(path).items():
  f=Path(n);f=f if f.is_absolute() else path.parent/f
  assert hashlib.sha256(f.read_bytes()).hexdigest()==h,str(f)
  hashes[str(f)]=h
  if f.name=='input-pins.json':pins(f)
pins(src/'pins.json');refs=read(src/'reviews.json');c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row;fresh=[]
for old in refs:
 r=dict(c.execute('select * from review_requests where id=?',(old['id'],)).fetchone());assert r['status']=='resolved' and r['resolution'].startswith('PASS');assert r['resolution']==old['resolution'];fresh.append(r)
 for f in old['refs']:pins(Path(f))
source=read(src/'source-hashes.json')
for f,h in source.items():assert hashes[f]==h

def data(n):return read(b/('residual-ten-D5-five-311-'+n)/'results.json')
def rows(n):return data(n)['records']
def keys(rs):
 k={r['root'] for r in rs};assert len(k)==len(rs);return k
negative=lambda r:r['status']=='EXACT_FARKAS_CONTRADICTION'
links=[]
for left,right in [('low-edge-allocation','common-neighbor-cuts'),('common-neighbor-cuts','low-involution'),('low-orbit-capacity','center-domains')]:
 a=rows(left);bb=rows(right);survivors=[r for r in a if not negative(r)];assert keys(survivors)==keys(bb)
 links.append({'from':left,'to':right,'input':len(a),'negative':len(a)-len(survivors),'retained':len(bb),'retained_statuses':sorted({r['status'] for r in survivors})})
assert keys(rows('low-involution'))==keys(rows('low-orbit-capacity'))
for dom,cover,nextdom in [('center-domains','center-cover','center-cross-domains'),('center-cross-domains','center-cross-cover','full-center-configurations')]:
 a=rows(cover);assert data(cover)['status']=='COMPLETE';assert all(r['status']=='COMPLETE' for r in a);assert keys(rows(dom))==keys(a)
 positive=[r for r in a if r['witness'] is not None];assert keys(positive)==keys(rows(nextdom));links.append({'from':cover,'to':nextdom,'input':len(a),'retained':len(positive)})
a=data('full-center-configurations');bb=data('centered-propagation');assert a['status']==bb['status']=='COMPLETE';assert keys(a['records'])==keys(bb['records']);assert len(a['records'])==29
expected=[(r['root'],h['high_assignment'],i) for r in a['records'] for h in r['configs'] for i,_ in enumerate(h['survivors'])]
actual=[(r['root'],h['high_assignment'],h['center_config']) for r in bb['records'] for h in r['records']]
assert len(expected)==len(set(expected))==len(actual)==len(set(actual))==706 and set(expected)==set(actual)
assert all(r['status']=='COMPLETE' for r in a['records']+bb['records']);assert all(h['status']=='NEGATIVE' for r in bb['records'] for h in r['records'])
assert sum(bool(r['configs']) and any(h['survivors'] for h in r['configs']) for r in a['records'])==13
seconds=time.monotonic()-start;assert seconds<30
out={'status':'COMPLETE','original_cap_seconds':30,'seconds':seconds,'hashes':hashes,'fresh_reviews':fresh,'links':links,'final_configurations':706,'negative':706,'scope':'D5,s5 composition only'}
(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':'COMPLETE','seconds':seconds,'hashes':len(hashes),'source_hashes':len(source),'fresh_reviews':len(fresh),'links':links,'final_negative':706}))
