from pathlib import Path
import json,collections
p=Path(__file__).resolve().parent;x=json.loads((p/'ledger.json').read_text());m=json.loads((p/'manifest.json').read_text());runs={tuple(r['small_group_id']):r for r in x['runs']}
lines=['# Cayley census at q=11 and q=13 — 2026-09-13','',f"Campaign status: **{x['status']}**. Board40; local Kissat {x['solver_version']}, seed0, proof logging OFF. Ten-minute cap per group,24-hour campaign limit, stop at first target SAT. No hand pruning and no retries.",'','One instance per SmallGroup:52 groups of order48,52 of order80,47 of order120 and57 of order168. Inverse-closed connection sets have exact sizes7,9,11 and13 respectively. Group tables came from the pinned GAP image `'+m['image']+'`.','', 'The [Cayley criterion review](cayley-lemma-review.json) establishes the mathematical equivalence used by the encoding. The [table audit](group-table-audit.json) checks all208 finite-group tables; the [sampled encoding audit](encoding-audit.json) is nonexhaustive. Software fixtures are separate from graph controls.','']
for n,q in [(48,7),(80,9),(120,11),(168,13)]:
 counts=collections.Counter(r['status'] for r in x['runs'] if r['small_group_id'][0]==n)
 lines += [f'## Order {n}, degree {q}','',', '.join(f'{v} {k}' for k,v in sorted(counts.items())) or 'Not launched.','','| SmallGroup | Structure | Verdict | Wall seconds |','|---|---|---|---:|']
 for item in m['groups']:
  if item['small_group_id'][0]!=n:continue
  key=tuple(item['small_group_id']);r=runs.get(key,{});wall=r.get('wall_seconds');lines.append(f"| {key[0]},{key[1]} | {item['structure'].replace('|','/')} | {r.get('status','NOT_LAUNCHED')} | {wall:.6f} |" if wall is not None else f"| {key[0]},{key[1]} | {item['structure'].replace('|','/')} | {r.get('status','NOT_LAUNCHED')} | — |")
 lines+=['']
lines+=['## Control witnesses','']
for r in x['runs']:
 if r.get('sat_observed'):
  n,i=r['small_group_id'];lines.append(f'- SmallGroup({n},{i}): [adjacency and connection set](runs/{n}-{i}/graph.json), [author check](runs/{n}-{i}/graph-check.json). Independent review receipts are required separately.')
lines+=['','## Verdict','']
if x['status']=='ALL_ATTEMPTS_TERMINAL':
 target=[r for r in x['runs'] if r['small_group_id'][0] in [120,168]]
 if all(r['status']=='UNSAT' for r in target) and len(target)==104:lines+=['All104 target instances returned UNSAT. No degree11 Cayley witness at order120 or degree13 Cayley witness at order168 was found in this complete SmallGroups census according to proof-OFF Kissat reports. These reports are not independently checked UNSAT certificates, and the Cayley-class result is not unrestricted nonexistence. Control and terminal-artifact acceptance must accompany this result.']
 else:lines+=['See the per-group outcomes; UNKNOWN or ERROR does not exclude a group. No unrestricted nonexistence conclusion follows.']
else:lines+=['IN PROGRESS: the target census is not yet complete. No unrestricted existence or nonexistence conclusion is drawn.']
lines+=['','## Verification and literature','', 'Both controls passed independent artifact checks: [order48 witness](independent-reviews/48-26.json) and [all52 order80 UNSAT reports](independent-reviews/order80-negative.json). The [order120 audit](independent-reviews/order120-target.json) binds its47 terminal outcomes. The [complete encoding review](ENCODING_REVIEW.md) and [constraint replay](full-encoding-audit.json) cover every production input; these are separate from solver verdicts.','', 'The [literature check](LITERATURE_CHECK_20260913.md) confirms the119/167 exclusions and records what the traced sources do and do not establish for120/168. It does not certify a globally current open-problem status. Independent runner and final report reviews remain pending.','']
(p/'CAYLEY_CENSUS_Q11_Q13_20260913.md').write_text('\n'.join(lines))
