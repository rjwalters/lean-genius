# Clause-boundary mismatch in H1 input validation

Found by codex-sol-1 on2026-09-10 before Phase B solver launch. Both the legacy native comparator and the initial streaming validator accepted a changed H1 CNF containing an injected empty clause. This could turn a solver UNSAT result into an invalid exclusion of the intended graph case.

The minimal file is:

```
p cnf 2 2
1
2 0 0
```

The legacy Lean parser treats each line as a clause and truncates at its first zero, yielding `[1]` and `[2]`. Standard DIMACS clause boundaries are zero tokens, yielding `[1,2]` and `[]`. The header and total number of clause terminators are unchanged. Thus checking the header/count against the legacy MATCH output does not close this mismatch.

The production reproduction changes only two zero terminators in the12,454,143-byte canonical pilot for tag003597af8a184e9f/profile2. The pinned native emitter/checker4bd9604c returned0 and `MATCH (610424 clauses, top 40944)` in6.15s for mutated SHA25634f83ef71a42907b595e02480ede29824206c55a88c67f65c2a8d7e0172bbc67. The initial validator source5117b82a also accepted it. Original SHA25663ba3e99aa19f2ad56784f704afee5569808af699cd88d31a8ca54634e2e6f69 is unchanged. The mutated input is intrinsically UNSAT because of the empty clause; no SAT solver was launched to establish this fact.

Required repair: enforce exactly one clause per data line, exactly one zero terminator at the end of that line, no internal zeros, and valid bounded literals. Preserve header/count agreement and actual byte hashes. This restriction matches the canonical emitter format. Do not combine a general DIMACS streaming parser with this line-based comparator.

The accepted-validator source is retained as historical reproduction evidence, not runnable production code. Small scripts and receipts are retained here; the production CNFs remain only in the private pilot directory. The named reproduction container was checked absent after completion.

## Fix verified

The materializer owner applied strict ASCII-space, one-clause-per-line framing. Independent verification of validator SHA2568dcbf61099353fc8e664274efbe71f927020ed0f2f22a115404757fd02861940 passed seven unit tests, rejected both counterexamples and accepted the unchanged canonical pilot. `fixed-validator-verification.json` retains this result. This verifies the demonstrated defect is repaired in the working validator; it is not a claim about other materialization or solver obligations.
