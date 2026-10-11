# Audit flags: erdos85-drop.11

**PASS — 0 unresolved critical flags.** This is an audit by codex, an AI author of the paper, not an independent external critic. The final AUDITED state additionally requires the v11 review to advance and no blocking operator feedback; the audit alone does not certify that review decision.

## Critical flags

None. Prior C1 is resolved by describing the explicit-hypothesis Lean derivation without calling Result A a Lean theorem; prior C2 is resolved by removing the unsourced H7 cost clause. The body, abstract and status table consistently retain both UNSAT hypotheses, the emitter identity gap, external cake_lpr trust and native_decide dependence. Theorem B remains conditional on A-REG and does not assert the open hypothesis.

## Prior major findings

- M1 resolved as disclosure: the introduction, status table and closing list now explain why the capstone cannot be recompiled from the public repository alone (13 packed H7 certificate files, about 2.57 GB, unpublished). Publishing the files and replaying the dependency closure remain future work; this audit does not certify public cold reproducibility.
- M2 resolved: the linked STRATA document has a superseded-status banner at the new artifact pin. Lean sources and accepted release evidence are unchanged by the re-pin.

## Build and deterministic gates

- Scratch XeLaTeX/BibTeX rebuild: 3 XeLaTeX passes total, at least two after BibTeX, aux fixpoint; all exits zero. Final pass has no rerun warnings, undefined references/citations or overfull boxes. Raw output is retained in compile-log.txt; source and log hashes are in build-check.json.
- Shipped PDF text is identical to the rebuilt PDF text (pdftotext -layout). The immutable source/PDF were not edited. Four passes in the author's build versus three in this scratch build is not a discrepancy: convergence is the stopping condition.
- Pending-marker gate passes, zero active markers. `pending_marker.json` retains the read-only result; no sibling owned by the reviewer was overwritten.
- Audience scan reports zero governance/private-locator hits and eight unlinked-path hits, all arguments of repofile macros whose definitions emit public hrefs. Each was inspected and dismissed as a scanner false positive. All 64 unique expanded targets exist at the pin. Raw scan is audience_check.json; its advisory exit 1 is not an unresolved defect.
- Corpus tier inactive (no corpus declaration); no new external artifact build configured or run for this audit.

## Non-critical notes and limits

- Citation support: 4 supports, 3 partial, 10 unverified (sources unavailable locally), no unresolved keys or does-not-support verdicts. See citation-audit.md and reproducible primary-source download identities. The live Erdős Problems page was not newly verified; novelty remains qualified, not an exhaustive claim.
- Retained numerical/Lean receipts are distinguished from fresh checks in numerical-audit.md. No proof replay, new cloud compute or billing verification was performed.
- The corrected H7 rounding explanation changes the prior audit's arithmetic description, not a paper value.
- Cosmetic font substitutions/underfull warnings remain; no overfull boxes. Main text is 11 pages, references make 14, against the approximate 10-page target.
- The historical brief lags the current evidence in places. The v11 wording obeys its hard Result-A naming rule; no claim to human operator review is made. The iteration override is agent-transcribed in the existing operator record, not newly granted by this audit.

## Audience-fit notes

None after manual confirmation of the scanner hits.
