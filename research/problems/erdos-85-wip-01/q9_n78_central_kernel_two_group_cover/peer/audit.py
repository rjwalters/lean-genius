from pathlib import Path
import itertools as I,json,hashlib,sqlite3,time
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/n78-central-kernel-two-group-cover')
read=lambda f:json.loads(f.read_text());checks={}
for manifest in [src/'pins.json',src/'input-pins.json']:
 for name,h in read(manifest).items():
  f=manifest.parent/name;assert hashlib.sha256(f.read_bytes()).hexdigest()==h;checks[str(f)]=h
con=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);con.row_factory=sqlite3.Row
premise=dict(con.execute('select id,status,resolution from review_requests where id=2430').fetchone());assert premise['status']=='resolved' and premise['resolution'].startswith('PASS')
author=read(src/'results.json');assert author['status']=='COMPLETE';expected={(tuple(m['square_bits']),tuple(m['commutator_bits'])):m for m in author['models']};assert len(expected)==len(author['models'])==24
start=time.monotonic();records=[];retained=set();status='INCOMPLETE'
try:
 for a in I.product(range(2),repeat=3):
  for b in I.product(range(2),repeat=3):
   if time.monotonic()-start>30:raise TimeoutError
   comm={(1,0):b[0],(2,0):b[1],(2,1):b[2]}
   def product(x,y):
    word=[i for i in range(3) if (x//2)>>i&1]+[i for i in range(3) if (y//2)>>i&1];central=(x&1)^(y&1)
    # Bubble-sort generator words, recording commutator factors at every swap.
    for end in range(len(word)-1,0,-1):
     for j in range(end):
      if word[j]>word[j+1]:
       central^=comm[word[j],word[j+1]];word[j],word[j+1]=word[j+1],word[j]
    vector=0
    for i in range(3):
     n=word.count(i);central^=a[i]*(n//2);vector|=(n%2)<<i
    return 2*vector+central
   M=[[product(x,y) for y in range(16)] for x in range(16)]
   assert all(M[0][x]==M[x][0]==x for x in range(16))
   assert all(M[M[x][y]][z]==M[x][M[y][z]] for x,y,z in I.product(range(16),repeat=3))
   good=M[14][14]==0 and any(M[14][x]!=M[x][14] for x in range(16))
   records.append({'square_bits':a,'commutator_bits':b,'retained':good})
   if not good:continue
   retained.add((a,b));saved=expected[a,b];assert M==saved['multiplication']
   inverse=[next(y for y in range(16) if M[x][y]==M[y][x]==0) for x in range(16)]
   assert inverse==saved['inverse']
   conjugates={M[M[g][14]][inverse[g]] for g in range(16)};assert conjugates=={14,15}
   cosets=[];remaining=set(range(16))
   while remaining:
    g=min(remaining);c=sorted({g,M[g][14]});assert len(c)==2;cosets.append(c);remaining-=set(c)
   assert cosets==saved['cosets']
   moves=[[next(i for i,c in enumerate(cosets) if M[g][orbit[0]] in c) for orbit in cosets] for g in range(16)]
   assert moves==saved['X_action']
   S=[[2*i+(bit^((g//2)>>i&1)) for i in range(3) for bit in range(2)] for g in range(16)]
   assert S==saved['S_action'] and saved['stabilizer']==[0,14]
   assert all(moves[M[x][y]][v]==moves[x][moves[y][v]] for x,y,v in I.product(range(16),range(16),range(8)))
   assert all(S[M[x][y]][v]==S[x][S[y][v]] for x,y,v in I.product(range(16),range(16),range(6)))
   assert sum(moves[14][v]==v for v in range(8))==4
 assert retained==set(expected)
 status='COMPLETE'
except TimeoutError:pass
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'hashes':checks,'premise':premise,'records':records,'retained_count':len(retained)}
(p/'results.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'status':status,'seconds':r['seconds'],'hashes':len(checks),'parameter_choices':len(records),'retained':len(retained)}))
