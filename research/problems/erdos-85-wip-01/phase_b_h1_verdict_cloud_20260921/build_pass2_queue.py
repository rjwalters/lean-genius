#!/usr/bin/env python3
"""Build the pass-2 queue: every pass-1 UNKNOWN row (Kissat cap hit) from the synced cloud
ledgers plus the Mac pilot, after pass 1 is complete. Writes queue-pass2.ids and
pass-pass2.json (read by controller.py --pass pass2). Board goal #45. SINGLE-SEAT."""
import hashlib, json, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
STRIPE = Path('/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49')
ledgers = sorted((STRIPE / 'h1-verdict-cloud-20260921/ledger').glob('*.json'))
latest = {}
for path in ledgers:  # later attempts override earlier ones (attempt epoch is in the name)
    row = json.loads(path.read_text())
    latest.setdefault(row['id'], []).append((path.name, row['status']))
pilot = json.loads((STRIPE / 'h1-verdict-pilot-20260921-claude/results.json').read_text())
if pilot['status'] != 'complete':
    sys.exit(f"pilot not complete: {pilot['status']}")
statuses = {case: sorted(v)[-1][1] for case, v in latest.items()}
statuses.update({r['id']: r['status'] for r in pilot['results']})
queue1 = (HERE / 'queue-1137.ids').read_text().split()
missing = [c for c in queue1 if c not in statuses]
if missing or len(pilot['results']) != 24:
    sys.exit(f"pass 1 incomplete: {len(missing)} cloud rows without a ledger, pilot rows {len(pilot['results'])}")
bad = sorted(c for c, s in statuses.items() if s not in ('UNSAT_CROSSCHECKED', 'UNKNOWN'))
if bad:
    sys.exit(f"pass 1 has non-UNSAT/UNKNOWN rows, resolve first: {bad}")
queue = sorted(c for c, s in statuses.items() if s == 'UNKNOWN')
raw = ''.join(c + '\n' for c in queue).encode()
(HERE / 'queue-pass2.ids').write_bytes(raw)
commit = sys.argv[1] if len(sys.argv) > 1 else 'FILL-AFTER-COMMIT'
spec = {"queue": "queue-pass2.ids", "queue_sha256": hashlib.sha256(raw).hexdigest(),
        "config": "research/problems/erdos-85-wip-01/phase_b_h1_verdict_cloud_20260921/config.longcap.json",
        "config_commit": commit, "direct": True,
        "source": {"cloud_rows": len(latest), "pilot_rows": len(pilot['results']),
                   "unsat_crosschecked": sum(s == 'UNSAT_CROSSCHECKED' for s in statuses.values()),
                   "unknown": len(queue)}}
(HERE / 'pass-pass2.json').write_text(json.dumps(spec, indent=1) + '\n')
print(json.dumps(spec))
