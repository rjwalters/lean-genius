# F0 downstream host pass: capped, shape remains open

The high cover passed independent review 2654: 2,020 E/S graphs reduce to 18,408 high assignments, with 452 graphs having no assignment. Every source E/S case came from the already COMPLETE part of review 2116.

The one host pass used the byte-identical accepted API 2123, after announcement in room 51210. It stopped at its original 60-second aggregate cap (60.002 seconds observed), with 100,000 counted nodes per input and bounded receipt shards. Of 18,408 inputs, 17,063 completed, 1,137 were UNKNOWN, and 208 were unvisited. Sixty completed inputs have no host extension; the others retain 717,283 leaves. No whole F0 root is excluded.

Saved completed receipts passed a separate verifier: exact ordered source cover, structural matching/unique-pair prefix cover, all 12,390,933 singleton-star pruning certificates and all retained leaves. Runtime 59.834 seconds within its original 60-second verification cap. UNKNOWN cases were skipped before endpoint work and the 208-entry suffix was preserved. host-frontier.json records exact unresolved keys; host-survivors.json names completed leaves. The verifier uses the previously reviewed F9 cover-reference/native endpoint checker, not the production host enumerator.

## What this changes

The high cover is complete, but these local host criteria do not provide a terminal exclusion under the bounded pass. The missing work is joint residual singleton-pair and pair-pair adjacency consistency, plus every UNKNOWN/unvisited input. Individual singleton-star feasibility is not simultaneous global realizability. Do not rerun the unchanged capped host domain or call the partial positive list a complete cover. No residual pass was launched and the 16-root H7 scope complement is unchanged.

All source/API/result hashes are pinned. Receipts are retained as two gzip shards below 50 MB each, approximately 80 MB total. This is experimental partial evidence, not a SAT verdict, LRAT/Lean proof, H7 exclusion, or solution of Erdős 85. The original high-stage README is retained unchanged under its accepted pins.
