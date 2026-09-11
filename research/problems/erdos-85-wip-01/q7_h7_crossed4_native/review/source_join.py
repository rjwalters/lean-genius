from pathlib import Path
import json,hashlib
p=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/h7-crossed4-native');q=Path(__file__).parent
j=json.loads((p/'source-join.json').read_text());s=Path(j['original_source']);assert hashlib.sha256(s.read_bytes()).hexdigest()==j['original_sha256'];sel={k:j[k] for k in ['twins_adjacent','profile_index']};r=next(r for r in json.loads(s.read_text())['results'] if all(r[k]==v for k,v in sel.items()));assert json.loads((p/'profile-source.json').read_text())=={'results':[r]}
assert r['status']=='COMPLETE' and len(r['assignments'])==3780
out={'status':'PASS','original_sha256':j['original_sha256'],'selection':sel,'exact_selected_record':True};(q/'source-results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
