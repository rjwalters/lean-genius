"""Exact integer sign obstruction; enumerates 120 shift triples, not graphs."""
from itertools import combinations
from math import gcd
from pathlib import Path
import json

units = [k for k in range(1,11) if gcd(k,21)==1]
records = []
for shifts in combinations(range(1,11),3):
    obstructions = []
    for k in units:
        folded = [min(k*a % 21, 21-(k*a % 21)) for a in shifts]
        sums = [folded[i]+folded[j] for i,j in combinations(range(3),2)]
        signs = [1 if x<=10 else -1 for x in sums]
        if len(set(signs))>1:
            obstructions.append(dict(k=k,folded=folded,pair_sums=sums,signs=signs))
    assert obstructions, shifts
    records.append(dict(shifts=shifts,obstruction=obstructions[0]))
assert len(records)==120
result = dict(status='PASS',units_up_to_sign=units,triples=120,survivors=0,records=records,
              scope='integer Fourier sign certificate only; requires the accompanying paper reduction')
(Path(__file__).parent/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: all120 triples have a certified primitive-character sign obstruction')
