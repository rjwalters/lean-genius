from pathlib import Path
import json,hashlib
p=Path(__file__).parent
t=json.loads((p/'tree.json').read_text())
lookup={x['original_index']:x['ordered_index'] for x in json.loads((p/'ordered_leaves.json').read_text())['entries']}
def render(x):
 kind=x[0]
 if kind=='branch':return '.branch ['+','.join(map(render,x[1]))+']'
 if kind=='leaf':return '.leaf '+str(lookup[x[1]])
 return '.cut (.'+kind+' '+' '.join(map(str,x[1:]))+')'
def fs(xs):return '{'+','.join(map(str,xs))+'}' if xs else '∅'
template=(p/'LeafPilot.lean').read_text()
manifest=[]
for subtree in t['subtrees']:
 i=subtree['index']
 if i in (16,31):continue
 name=f'CoverageShard{i}'
 head=template[:template.index('def prefixRows')].replace('ColumnCoverageLeafPilot',name)
 tail=template[template.index('\ntheorem checked'):].replace('ColumnCoverageLeafPilot',name)
 src=head+'def prefixRows : Fin 8 → Finset (Fin 15) := !['+','.join(map(fs,subtree['prefix_columns']+[[]]*6))+']\n'
 src+='def cert : FiniteRowCoverCertificate ThreeHighColumnCut (Fin 140) := '+render(subtree['tree'])+'\n'+tail
 f=p/(name+'.lean');assert not f.exists();f.write_text(src)
 manifest.append({'name':name,'index':i,'nodes':subtree['nodes'],'sha256':hashlib.sha256(f.read_bytes()).hexdigest()})
(p/'shards_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Rendered',len(manifest),'remaining shards')
