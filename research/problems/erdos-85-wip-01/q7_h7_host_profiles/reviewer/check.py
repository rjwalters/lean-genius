import pathlib,json,hashlib,collections,math
P=pathlib.Path('/tmp/erdos85-sol1-h7-host-profiles')
for f,h in json.loads((P/'pins.json').read_text()).items():assert hashlib.sha256((P/f).read_bytes()).hexdigest()==h
report=json.loads((P/'results.json').read_text())
for f,h in report['source_pins'].items():assert hashlib.sha256(pathlib.Path(f).read_bytes()).hexdigest()==h
profiles=[]
def compose(prefix,left):
 if len(prefix)==8:
  if left==0:profiles.append(tuple(prefix))
  return
 for d in range(min(left,2 if len(prefix)<2 else 1)+1):compose(prefix+[d],left-d)
compose([],3);assert len(profiles)==70
audits=[]
for row in report['results']:
 twin=row['twins_adjacent']
 def signature(x):
  if twin:return (tuple(sorted(x[:2])),tuple(sorted([x[2]+x[3],x[4]+x[5],x[6]+x[7]])))
  return (tuple(sorted([(x[0],x[2]),(x[1],x[3])])),tuple(sorted([x[4]+x[5],x[6]+x[7]])))
 classes=collections.Counter(map(signature,profiles));assert len(classes)==(7 if twin else 15)
 upper=[3,3,2,2,2,2,2,2] if twin else [2,2,3,3,2,2,2,2]
 delta=[1]*8 if twin else [0,0,2,2,1,1,1,1]
 assert sum(upper)==18 and sum(delta)==8
 assert row['stabilizer_size']==(2*(2**3)*math.factorial(3) if twin else 2*(2**2)*math.factorial(2))
 represented=set()
 for rep in row['representatives']:
  x=tuple(rep['defects']);assert x in profiles;s=signature(x);assert s not in represented;represented.add(s)
  assert classes[s]==rep['orbit_size']
  assert rep['pair_counts']==[upper[i]-x[i] for i in range(8)]
  assert rep['empty_counts']==[upper[i]-x[i]-delta[i] for i in range(8)]
  assert sum(rep['pair_counts'])==15 and sum(rep['empty_counts'])==7
 assert represented==set(classes)
 audits.append(dict(twins_adjacent=twin,profiles=len(profiles),orbits=len(classes),orbit_sizes=sorted(classes.values())))
out=dict(status='PASS',method='Bounded compositions and explicit wreath-product invariants, without permutation canonicalization: unordered S defects and P-pair defect sums; crossed S/P arm pairs and remaining pair sums',audits=audits,scope='Complete necessary count-profile quotient only; no profile realizability or exclusion')
print(out);pathlib.Path(__file__).with_name('REVIEW2068.json').write_text(json.dumps(out,indent=2)+'\n')
