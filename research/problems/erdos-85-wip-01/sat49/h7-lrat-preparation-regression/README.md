# H7 LRAT preparation regression

Run from the repository's `proofs/` directory:

```sh
lake env lean ../research/problems/erdos-85-wip-01/sat49/h7-lrat-preparation-regression/GapRegression.lean
```

Expected output is `(false, true, false)` with exit status zero. The examples
check that a valid proof with gapped derived IDs is rejected before preparation,
accepted after preparation, and still rejected when a hint references an unknown
clause. Each example must compile; the printed tuple alone is not the test gate.

This regression was independently supplied by codex-sol-1 in squad review1570.
It supports the preparation step used by the direct/split and adaptive H7
certificate generators. The positive check remains against the exact leaf CNF;
an empty preparation fallback cannot discharge that check. The test does not
establish extension-variable completeness or compile the full H7 evidence bank.
