# a7 F2 (cube_F7_t2): complete high cover + COMPLETE necessary host cover — 2026-09-15

Banked by claude from codex-sol-2's frozen package `/Users/rwalters/lean-genius-h7-f2-sol2-20260915`
(the 14 files pinned in `author/host-pins.json` plus that pin file, verbatim; every byte re-checked at copy).
The unpinned `residual.py` / `verify_residual.py` prepared for a later residual pass are NOT part of
this archive.

Status: **F2 remains OPEN.** This archive supplies (1) a complete necessary high cover of the
COMPLETE F2 slice of accepted projection 2116 — 48 host bases, 3,944 E/S graphs, 1,496 with no
admissible high pairing, 2,448 with 24,136 pairings in total, independently reviewed PASS as
review 2655 (exhaustive 7! enumeration by codex-sol-1) — and (2) ONE host pass over all 24,136
fixed-high graphs with the byte-identical accepted host API (review 2123), which COMPLETED in
37.03 s under its 60 s aggregate / 100,000-node caps: 24,136 COMPLETE, 0 UNKNOWN, 0 unvisited;
16 inputs admit no host extension, the rest retain 785,408 host leaves; 8,742,728 singleton-star
prunes. Independently reviewed PASS as review 2657 (shard recount, pins, API/source identity,
adapter equality on all 24,136 inputs, verifier tie-out). This is a necessary pair-host cover:
no residual-edge or whole-root exclusion, no SAT solver, no proof replay, no Lean theorem, no H7
or Erdős 85 claim. Unlike F0 the host cover is complete, so a bounded residual pass over the
785,408 leaves is a well-defined next step (proposed by sol-2 at room 51230, gated on a
pre-launch post).

Source identity: the producer read `q7_h7_a7_noncycle_singleton_projection/author/{results.json,
completion-results.json}` from a working tree at erdos85/integration revision
7658415fb4670181d20aa229150fef781356ae55; both sha256 pins in `author/high-launch.json` match
that revision's committed bytes (re-checked at banking). Host API pins in `author/hosts/launch.json`
are identical to `q7_h7_monotone_host_api/original/pins.json`. The verifier
(`author/verify_hosts.py`) rebuilds each input with its own code from the 21-vertex base and
uses the 2124-accepted F9 `cover_reference.py` + `verify.dylib`; at review 2657 the producer's
`fixed_high` and the verifier's `given_high` were shown to agree on all 24,136 inputs.

Layout: `author/` = sol-2's pinned package (receipts in `author/hosts/` as two gzip shards,
50.0 MB and 15.5 MB); `review/` = squad review records 2655 (codex-sol-1) and 2657 (claude)
exported from the room database; `BANK_PINS.json` = sha256 of every file here.
