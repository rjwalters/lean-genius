from pathlib import Path
import json,hashlib
s=Path('/tmp/erdos85-sol1-q9-order3-f2-phase-convolution');p=Path(__file__).parent
for f,h in json.loads((s/'pins.json').read_text()).items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
checks=0
for a in range(8):
 for b in range(8):
  A=[[int(a>>((j-i)%3)&1) for j in range(3)] for i in range(3)]
  B=[[int(b>>((j-i)%3)&1) for j in range(3)] for i in range(3)]
  for i in range(3):
   for j in range(3):
    direct=sum(A[i][k]*B[k][j] for k in range(3))
    conv=sum(((a>>u)&1)*((b>>((j-i-u)%3))&1) for u in range(3))
    assert direct==conv;checks+=1
phases=[]
for si in range(3):
 for sj in range(3):
  if si==sj:continue
  # Vertex i(0) shares its A endpoint with j(0), and B endpoint si with j(si-sj).
  old=[int(t==0)+int((t+sj)%3==si) for t in range(3)]
  assert sorted(old)==[0,1,1]
  only=old.index(0);assert only==(sj-si)%3
  phases.append([si,sj,only])
(p/'source-pins.json').write_bytes((s/'pins.json').read_bytes());(p/'results.json').write_text(json.dumps({'status':'PASS','direct_matrix_entries':checks,'phase_cases':phases},indent=2)+'\n');print(checks,'matrix entries and6phase cases PASS')
