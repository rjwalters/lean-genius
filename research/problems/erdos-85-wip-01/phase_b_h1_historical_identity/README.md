# Historical H1 input identity audit

All 98 selected local historical CNFs match freshly emitted canonical inputs byte-for-byte. The audit independently rehashes the archived inputs and rereads their paired verdicts: 95 have matching table/tag/arm and `UNSAT drat:VERIFIED mode:MONO` records; three have no paired verdict. Those three have verdict records in other directories, retained separately without assuming those records certify the matched payload.

This is input identity and historical metadata, not fresh proof verification. Proof paths and sizes are observations only; proof bytes were neither hashed nor replayed. No SAT solver ran. No case was removed from the conservative 1,257-row H1 inventory. None of the 95 paired records is CUBE25.

The 98 tags are the intersection of the 164 historical verified tags and 98 available remote-sweeps CNF tags in the frozen inventory. All 98 frozen rows lacked a historical input hash. `remote-candidate-paths.json` pins the selected paths, `full-results.json` retains generator/check receipts and every baseline, and `independent-audit.json` records an additional read-only validation. The three unpaired cases are 2c22b4969bc68443, a78d2764b4914a80, c60116d55d32f668.

`compare.py` and `remaining.py` preserve the local experiment harness, including machine-specific paths. The first three comparisons ran as a pilot; the remaining 95 used two workers and a 900-second deadline, completing in 698.386 seconds. Generated temporary CNFs were removed only after a matching comparison receipt and a further hash check. Historical artifacts were untouched.

To rerun the read-only audit against the original local evidence: `python3 audit.py /tmp/erdos85-sol1-h1-historical-identity ../phase_b_h1_h3/h1-frozen-candidates.json --output /tmp/h1-identity-audit.json`. It requires the archived CNFs and original per-case table/materialization receipts. This package does not copy large inputs or proofs.

Review 2005 passed after Claude independently reran the read-only audit, verified all package pins, and checked the selected set against a separate archive scan. `tags.txt` is the full 164-tag historical set; `compared-98-tags.txt` is exactly the subset compared here.
