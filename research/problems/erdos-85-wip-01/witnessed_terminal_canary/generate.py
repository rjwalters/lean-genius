"""Generate explicit reasons; Lean checks every reason against its actual candidate list."""
from pathlib import Path
import argparse
import json
import re

root = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--shapes', type=Path, default=root / 'shapes.jsonl')
args = parser.parse_args()
shapes = [json.loads(line) for line in args.shapes.read_text().splitlines()]
assert list(map(len, shapes)) == [536, 536, 536]
source = (root.parent / 'terminal_canary' / 'Certificate.lean').read_text()
rows = json.loads('[' + re.search(r'def adjRows.*?!\[(.*?)\]', source).group(1) + ']')
raw = re.search(r'def D :.*?:= !(\[.*\])', source).group(1)
domains = json.loads(raw.replace('{', '[').replace('}', ']'))
reasons = []
for k, candidates in enumerate(shapes):
    entries = []
    for triple in candidates:
        if triple in domains[k]:
            entries.append('.kept')
        else:
            witness = next((a, b, c) for a in triple for b in triple if a != b
                           for c in range(24) if rows[a] >> c & 1 and rows[b] >> c & 1)
            entries.append('.conflict ' + ' '.join(map(str, witness)))
    reasons.append('[' + ','.join(entries) + ']')
source = source.replace('import Proofs.Erdos85ThreeHighSelectedSeparatedCertificate',
                        'import Proofs.Erdos85ThreeHighWitnessedTripleCover')
source = source.replace('theorem initial_cover_checked',
    'def reasons : Fin 3 → List ThreeHighTripleCoverReason := ![' + ','.join(reasons) + ']\n\ntheorem initial_cover_checked', 1)
old = '!threeHighTripleNoCommonNeighbor B S || decide (S ∈ D k))) = true := by decide'
new = '!threeHighTripleNoCommonNeighbor B S || decide (S ∈ D k))) = true := by\n  exact threeHighWitnessedTripleCoverCheck_sound B D reasons (by decide)'
assert old in source
source = source.replace(old, new, 1)
args.output.write_text(source)
