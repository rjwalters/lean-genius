from pathlib import Path
import hashlib
import json

S = Path('/Users/rwalters/lean-genius-q9-known-values-20260911')
P = Path(__file__).parent
pins = json.loads((S/'payload-pins.json').read_text())
for f, h in pins.items():
    assert hashlib.sha256((S/f).read_bytes()).hexdigest() == h
# Hand-substituted theorem/inequality bounds; no import of the producer's code.
intervals = [(73,73),(74,74),(75,75),(75,76),(77,77),(78,79),
             (79,79),(80,81),(81,82),(82,83),(83,84),(85,85),
             (85,86),(87,87),(88,88),(89,89),(90,90),(91,91),(92,92)]
ramsey = dict(zip(range(64,83), intervals))
src = json.loads((S/'table-results.json').read_text())
assert src['ramsey_bounds'] == {str(n): list(v) for n,v in ramsey.items()}
audit = []
for row in src['rows']:
    N = row['N']
    lower = max(N-n+1 for n,(lo,hi) in ramsey.items() if lo>N and n<N)
    upper = min(N-n for n,(lo,hi) in ramsey.items() if hi<=N and n<N)
    assert row['audited_f'] == [lower,upper]
    lb,ub = row['lower_bridge'], row['upper_bridge']
    assert lb['n'] == N-lb['d'] and lb['d']+1 == lower
    assert ub['n'] == N-ub['d'] and ub['d'] == upper
    assert ramsey[lb['n']][0] == lb['r_lower'] > N
    assert ramsey[ub['n']][1] == ub['r_upper'] <= N
    reported = dict(ramsey)
    reported.update({67:(76,76),73:(83,83),74:(84,84),76:(86,86)})
    rl = max(N-n+1 for n,(lo,hi) in reported.items() if lo>N and n<N)
    ru = min(N-n for n,(lo,hi) in reported.items() if hi<=N and n<N)
    assert row['reported_f'] == [rl,ru]
    audit.append({'N':N,'audited_f':[lower,upper], 'reported_f':[rl,ru]})
assert [x['N'] for x in audit] == list(range(73,92))
(P/'input-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
result = {'status':'PASS','rows':audit,'scope':'independent arithmetic and bridge checks; literature proofs remain external premises'}
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS all 19 threshold rows, 38 bridge witnesses, and reported/traced distinctions')
