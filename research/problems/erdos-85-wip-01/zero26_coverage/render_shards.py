from pathlib import Path
import json,hashlib
p=Path(__file__).parent;t=json.loads((p/'tree.json').read_text())
def render(x):
 if x[0]=='branch':return '.branch ['+','.join(map(render,x[1]))+']'
 assert x[0]!='leaf'
 return '.cut (.'+x[0]+' '+' '.join(map(str,x[1:]))+')'
def fs(S):return '{'+','.join(map(str,S))+'}' if S else '∅'
manifest=[]
for x in t['subtrees']:
 n='Zero26Shard'+str(x['index']);s='import Zero26Data\nnamespace '+n+'\nopen Erdos85 Zero26\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 50000000\n'
 s+='def prefixRows : Fin 8 → Finset (Fin 15) := !['+','.join(map(fs,x['prefix_columns']+[[]]*6))+']\n'
 s+='def cert : FiniteRowCoverCertificate ThreeHighColumnCut (Fin 0) := '+render(x['tree'])+'\n'
 s+='''theorem checked : finiteRowCoverCheck domains
    (fun k columns reason => threeHighColumnCutCheck U R [(2,3),(4,5),(6,7)] threeHighColumnScore k
      (threeHighCrossOfColumns columns) reason)
    (fun columns entry => decide (∀ i j, threeHighCrossOfColumns columns i j = table entry i j))
    6 2 prefixRows cert = true := by decide
'''
 s+='end '+n+'\n#print axioms '+n+'.checked\n';f=p/(n+'.lean');assert not f.exists();f.write_text(s);manifest.append({'name':n,'index':x['index'],'nodes':x['nodes'],'sha256':hashlib.sha256(f.read_bytes()).hexdigest()})
(p/'shards_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
