#!/usr/bin/env python3
"""Build the pass-3 queue: every pass-2 row whose latest attempt is UNKNOWN or ERROR, after
pass 2 is complete (every pass-2 queue ID has a ledger). Board goal #46. SINGLE-SEAT."""
import hashlib, json, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
LEDGER = Path('/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-verdict-cloud-20260921/pass2/ledger')
latest = {}
for path in sorted(LEDGER.glob('*.json')):
    row = json.loads(path.read_text())
    latest.setdefault(row['id'], []).append((row.get('archive_key', ''), row['status']))
status = {case: sorted(v)[-1][1] for case, v in latest.items()}
queue2 = (HERE / 'queue-pass2.ids').read_text().split()
missing = [c for c in queue2 if c not in status]
if missing:
    sys.exit(f"pass 2 incomplete: {len(missing)} rows without a ledger")
bad = sorted(c for c, s in status.items() if s not in ('UNSAT_CROSSCHECKED', 'UNKNOWN', 'ERROR'))
if bad:
    sys.exit(f"pass 2 has SAT/DISAGREEMENT rows, resolve first: {bad}")
queue = sorted(c for c, s in status.items() if s in ('UNKNOWN', 'ERROR'))
raw = ''.join(c + '\n' for c in queue).encode()
(HERE / 'queue-pass3.ids').write_bytes(raw)
commit = next((a for a in sys.argv[1:] if not a.startswith('--')), 'FILL-AFTER-COMMIT')
spec = {"queue": "queue-pass3.ids", "queue_sha256": hashlib.sha256(raw).hexdigest(),
        "config": "research/problems/erdos-85-wip-01/phase_b_h1_verdict_cloud_20260921/config.pass3.json",
        "config_commit": commit, "direct": True, "lifetime": 216000,
        "source": {"pass2_rows": len(status), "unsat_crosschecked": sum(s == 'UNSAT_CROSSCHECKED' for s in status.values()),
                   "unknown": sum(s == 'UNKNOWN' for s in status.values()),
                   "error_reruns": sorted(c for c, s in status.items() if s == 'ERROR')}}
(HERE / 'pass-pass3.json').write_text(json.dumps(spec, indent=1) + '\n')
print(json.dumps(spec))
