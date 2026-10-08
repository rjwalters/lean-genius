"""Check that the preflight is the exact planned composition with explicit premises."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent
cell=(ROOT.parent/'h3_native_parts_20261008/source-review/Proofs/Erdos85H3TripleCompletionCell.lean').read_text()
spec=json.loads((ROOT/'SOURCE.json').read_text())
assert hashlib.sha256(cell.encode()).hexdigest()==spec['production_cell_sha256']
assert re.findall(r'^import (.+)$',cell,re.M)==[f'Proofs.Erdos85H3TripleCompletionPart{r:03d}' for r in range(384)]
body=cell[cell.index('/- Planned composition;'):]
body=body.replace('/- Planned composition; uncompiled until all 384 native premises are available. -/','/- Conditional assembly preflight: all 384 native results are explicit hypotheses. -/')
body=body.replace('namespace Erdos85.H3TripleCompletion','namespace Erdos85.H3TripleCompletion.AssemblyPreflight')
body=body.replace('end Erdos85.H3TripleCompletion','end Erdos85.H3TripleCompletion.AssemblyPreflight')
body=body.replace('#print axioms Erdos85.H3TripleCompletion.','#print axioms Erdos85.H3TripleCompletion.AssemblyPreflight.')
params='\n'.join(f'    (triplePart_384_{r:03d} : triplePart 384 {r} = true)' for r in range(384))
args=' '.join(f'triplePart_384_{r:03d}' for r in range(384))
for theorem in ('tripleParts_384_all','threeHighCanonicalRepresentativeExcluded_one','orderFortyNineTripleCellExcluded_three_one'):
 body=body.replace('theorem '+theorem+' :','theorem '+theorem+'\n'+params+' :')
body=body.replace('(by omega) tripleParts_384_all','(by omega) (tripleParts_384_all '+args+')')
expected='import Proofs.Erdos85H3TripleCompletionSplit\n\n'+body
actual=(ROOT/'H3AssemblyPreflight.lean').read_text()
assert actual==expected
assert hashlib.sha256(actual.encode()).hexdigest()==spec['preflight_source_sha256']
assert 'native_decide' not in actual and 'sorry' not in actual
assert not re.search(r'^\s*axiom\s',actual,re.M)
print('EXACT_CONDITIONAL_TRANSFORMATION_PASS: 384 cases, explicit hypotheses, unchanged bridge applications.')
