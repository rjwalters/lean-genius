# a7 F0 (cube_F7_t0): complete high cover + capped host pass — 2026-09-15

Banked by claude from codex-sol-1's frozen package `/Users/rwalters/lean-genius-h7-f0-sol1-20260915`
(author files verbatim under `author/`, every byte matching `author/pins.json`).

Status: **F0 remains OPEN.** This archive supplies (1) a complete necessary high cover of the
COMPLETE F0 slice of accepted projection 2116 — 48 host bases, 2,020 E/S graphs, 452 with no
admissible high pairing, 1,568 with 18,408 pairings in total, independently reviewed PASS as
review 2654 (exhaustive 7! enumeration) — and (2) ONE bounded host pass over those 18,408
fixed-high graphs with the byte-identical accepted host API (review 2123): 60 s aggregate wall,
100,000 counted nodes per input, frozen at the cap with 17,063 COMPLETE / 1,137 UNKNOWN /
208 unvisited; 60 completed inputs admit no host extension, the other completed inputs retain
717,283 leaves; 12,390,933 singleton-star prunes. Independently reviewed PASS as review 2656
(shard recount, frontier, cap audit, verifier tie-out). No F0 root exclusion, no residual pass,
no SAT solver, no proof replay, no Lean theorem, no H7 or Erdős 85 claim.

Source identity: the producer read `q7_h7_a7_noncycle_singleton_projection/author/{results.json,
completion-results.json}` from a working tree at erdos85/integration revision
7658415fb4670181d20aa229150fef781356ae55; both sha256 pins in `author/high-launch.json` match
that revision's committed bytes (re-checked at banking). The host API pins in
`author/host-launch.json` are identical to `q7_h7_monotone_host_api/original/pins.json`.

Reading (sol-1, room 51228): the F0 cap shows the missing link is simultaneous residual
adjacency consistency across singleton pairs and pair-pairs, not individual singleton-star
feasibility; repeating this host census on the unchanged domain is not useful.

Notes recorded at review 2656 (non-blocking): UNKNOWN receipts carry no reason field, so the
1,137 UNKNOWN mix per-input node-cap hits with time-remaining cuts near the aggregate deadline;
the verifier (`author/verify_hosts.py`, using the 2124-accepted F9 `cover_reference.py` +
`verify.dylib`) shares `given_high()` with the producer for input construction, which is
covered by `author/host-input-verification.json` and review 2654.

Layout: `author/` = sol-1's package (18 pinned files + `pins.json`; receipts in two gzip shards
of 50.0 MB and 29.9 MB, 717,283 survivors, exact frontier); `review/` = squad review records
2654 (codex-sol-2) and 2656 (claude) exported from the room database; `BANK_PINS.json` =
sha256 of every file here.
