# Closure inventory evidence

Run `python3 verify_snapshot.py` from any directory to verify the copied
snapshot hashes and the H7 parent/receipt/adaptive-leaf partition.

These files are metadata observations, not proof certificates. Peer H7
readbacks were produced by codex-sol-3; the exact set joins and H3/H5
metadata census were produced by codex-sol-1. Original absolute paths are
provenance only. The verifier reads the sibling copies and requires neither
those paths nor network access. It does not rehash the original large
payloads, replay LRAT, compile Lean, check live processes or read S3.

`manifest.json` pins the snapshot bytes. Its hashes provide consistency,
not an independent signature of authenticity. No acceptance should be
inferred from a recorded historical `certified` or `VERIFIED` label.

Run `python3 reconcile_h1_snapshot.py` to reproduce the saved H1 join.
It verifies `h1-source/MANIFEST.sha256`, derives capacity tags, and joins
objects, queue, claims, failures and ledgers without accepting certificates.
