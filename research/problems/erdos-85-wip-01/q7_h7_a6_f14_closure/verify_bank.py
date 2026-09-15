"""Verify a mixed local/external evidence archive without rerunning research."""
import argparse,hashlib,json
from pathlib import Path

def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()

def check(root,external_root=None):
 manifest=json.loads((root/'BANK_PINS.json').read_text())
 if manifest['schema']!='bank-pins-v2':raise ValueError('Unsupported manifest schema')
 seen=set()
 for kind in ['local','external']:
  for name,record in manifest[kind].items():
   relative=Path(name)
   if relative.is_absolute() or '..' in relative.parts or name in seen:raise ValueError('Invalid archive path: '+name)
   seen.add(name)
   if kind=='local':path=root/relative
   elif external_root is None:path=Path(record['path'])
   else:path=external_root/Path(record['path']).name
   if path.stat().st_size!=record['bytes'] or digest(path)!=record['sha256']:raise ValueError('Hash/size mismatch: '+str(path))
 # Bind the original author manifest to the union, including external files.
 for label in ['author','review']:
  original=json.loads((root/label/'pins.json').read_text())
  for name,sha in original.items():
   key=label+'/'+name
   bound=manifest['local'].get(key,manifest['external'].get(key))
   if bound is None or bound['sha256']!=sha:raise ValueError('Original manifest mismatch: '+key)
 return {'status':'PASS_LOCAL_EXTERNAL_BYTES_AND_ORIGINAL_MANIFESTS','local_payloads':len(manifest['local']),'external_payloads':len(manifest['external'])}

if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
 parser.add_argument('--external-root',type=Path,help='Directory containing relocated external receipt files')
 args=parser.parse_args();print(json.dumps(check(args.root,args.external_root),indent=2))
