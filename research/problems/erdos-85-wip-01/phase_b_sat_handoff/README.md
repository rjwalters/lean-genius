# Retained SAT candidate handoff

`check_retained_sat_candidate.py` consumes an existing dispatcher case directory, the pinned combined index and the explicitly selected solver log. It checks the combined and separate preparation/solve receipts, source row/profile, source and index hashes, retained CNF and log hashes and solver exit/status. It then invokes the reviewed H1 or small-high graph decoder. Files are checked again after decoding. The command launches no solver and never changes the original solver receipts.

Example (substitute actual paths and index digest):

```sh
python3 sat49/check_retained_sat_candidate.py --case-dir /path/to/run/CASE_ID --index phase_b_survivors_20260910.json --index-sha256 INDEX_SHA256 --solver kissat --output /path/to/new-graph-check.json
```

For a disagreement where the primary was UNSAT and CaDiCaL returned SAT, select `--solver cadical`. Output is exclusive: existing files are never overwritten. Only `GRAPH_WITNESS_VERIFIED` exits zero. Invalid models, wrong provenance and graph rejections are diagnostic errors; none implies UNSAT. A successful direct 49-vertex graph check is a finite computational witness, not a Lean theorem. The status file is separate from the pending receipt reducer and does not silently change its classifications.

Eight tests cover receipt mismatch, modified log, mutation during decoding, selecting the SAT side of a solver disagreement, retained graph-error evidence, strict profile routing, a real-decoder rejection of a toy CNF, and routing of bound bytes. Positive handoff routing uses a mock decoder; no positive 49-vertex graph/model is known or claimed, and no solver ran.

Sol3 independently passed all eight tests and four additional handoff tests (review message 46387; durable review 2011 replaces misdirected request 2008). Original source hashes are retained in `review-result.json`. The actual frozen index census also joins all 1,416 case IDs to source rows and valid decoder profiles; `profile-census.json` records the complete mapping.
