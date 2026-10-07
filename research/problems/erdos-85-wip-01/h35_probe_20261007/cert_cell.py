#!/usr/bin/env python3
"""Streamed CaDiCaL LRAT -> cake_lpr certification of one Lean-exact H3/H5 cell.

Reuses h1_cert_full_20261001/cert_row.solve_and_check (FIFO relay, proof sha256, no proof stored).
Success only if CaDiCaL exits 20 AND cake_lpr prints "s VERIFIED UNSAT".
usage: cert_cell.py <label> <cnf> <cap_seconds>
"""
import json, sys, types, hashlib
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "h1_cert_full_20261001"))
from cert_row import solve_and_check  # noqa: E402

_unlink = Path.unlink
def _tolerant_unlink(self, missing_ok=False):  # /Volumes/Stripe can return EPERM to long jobs
    try:
        _unlink(self, missing_ok=missing_ok)
    except PermissionError:
        pass
Path.unlink = _tolerant_unlink

label, cnf, cap = sys.argv[1], Path(sys.argv[2]), int(sys.argv[3])
work = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h35-probe-20261007/cert") / label
work.mkdir(parents=True, exist_ok=True)
a = types.SimpleNamespace(cadical="/opt/homebrew/bin/cadical", cake_lpr="/Volumes/Stripe/lean-genius/cake_lpr-src/cake_lpr",
                          heap_mb=8000, cap=cap)
h = hashlib.sha256()
with open(cnf, "rb") as f:
    for b in iter(lambda: f.read(1 << 20), b""):
        h.update(b)
rec = {"label": label, "cnf": str(cnf), "cnf_sha256": h.hexdigest(), "cap_s": cap}
try:
    solve_and_check(a, work, cnf, rec)
except OSError as e:  # Stripe EPERM on unlink etc.
    rec.setdefault("status", "ERROR"); rec["error"] = repr(e)
(work / "receipt.json").write_text(json.dumps(rec, indent=2, default=str))
print(rec.get("status"))
