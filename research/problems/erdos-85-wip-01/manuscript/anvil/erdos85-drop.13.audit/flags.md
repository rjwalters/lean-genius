# Audit flags: erdos85-drop.13

**Verdict: PASS. 0 critical flags, 0 major findings.** Both v12 blockers are resolved: C1 (the commit named in Availability) and M1 (independent re-audit not recorded at the pin). Auditor: Claude (Opus 5.5) acting as the paper-audit critic. Claude models are listed AI authors of the paper, so this is not an independent external audit. No Lean build, `lake` invocation, SAT replay or cloud compute was run.

**Thread state.** There is no `erdos85-drop.13.review/` sibling. v13 is a direct edit made after the v12 review (41/44, advance). The audit gate passes for v13. Whether the thread is `AUDITED` depends on the orchestrator treating v13 as `READY`, which needs either a v13 review that advances or an explicit carry-forward of the v12 review for these narrow edits.

## Resolution of the v12 findings

- **v12 C1 (commit identifier): RESOLVED.** L32–L34 define `\repocommit` = `2029149d7e42b74036ff0e1e82af6d33c2e32748` and build `\repobase` from it. L274 prints `\repocommitshort` = `2029149d7e42`, the first 12 characters of the full hash. All 70 distinct link targets exist at the pin. All 82 GitHub blob URIs in the compiled PDF carry the full pin hash. `git ls-remote` shows the pin as the head of `origin/erdos85/release-assembly-20261011`. The pin contains `release_cold_build_20261011/{ACCEPTED,FAILURE,README}.md` and `release_thirdparty_rebuild_20261012/ACCEPTED.md`. The pin is one commit on top of the v12 pin `fa2b41268df` and changes only six record and script files, with no Lean source change.
- **v12 M1 (independent re-audit): RESOLVED.** `release_cold_build_20261011/ACCEPTED.md` at the pin records "Independent re-audit (Codex, squad review #2749, PASS, 2026-10-12)": it reran `audit.py` (893 sources, exact 601/607/604, same RUN.json sha256), rehashed the archive, checked full coverage of the 2,692-file manifest, and confirmed that release-assembly `proofs/` is byte-identical to execution commit `afa46bc5078`. This was cross-checked against the primary record with a read-only query of the room DB. `review_requests` row 2749 has requester `claude`, was claimed and resolved by `codex` at 2026-10-12T14:34:05Z, and its PASS resolution has the same numbers and hashes. L113 now says the audit was "repeated independently by a second AI author", which is accurate. The public raw file at the pin contains the paragraph (HTTP 200).

## Hard scope rules

Satisfied. Result A is never called an unconditional Lean theorem. L89 says "Result A is not an unconditional theorem of Lean". L68, L80, L113 and Table 2 (L222, L227, L228) keep both UNSAT hypotheses (H1; H7 with t=0), the external cake_lpr checks that are not admitted into Lean, the emitter identity gap, and the dependence on native_decide (598 axioms beyond the standard three). Nothing is claimed about Erdős Problem 85 itself. L68 says "one drop is compatible with either answer", L89 says "Nothing is claimed about Erdős Problem 85 itself", and Theorem B stays conditional on A-REG (L70, L84, L248). `scope_lint.py erdos85-drop.13/main.tex` passes (38 numbers, 46 Lean names), and also passes with `--proofs` pointed at the pin's `proofs/Proofs`.

## Critical flags (block advancement to AUDITED)

None.

## Major findings

None.

## Build and deterministic gates

- **Build:** run in a scratch copy; the manuscript was untouched. The sequence was xelatex, bibtex, then xelatex until the fixpoint. Pass 1 and pass 3 emitted `Label(s) may have changed`, and pass 2 emitted the natbib citation rerun. Pass 4 emitted no rerun warning, and `.aux` was byte-identical across passes 3, 4 and 5. Pass 5 was a confirmation pass. All 6 invocations exited 0. The log shows 0 undefined citations or references, 0 overfull boxes, 3 underfull boxes and 28 font-shape substitution warnings (Menlo small caps and semibold; cosmetic). The output is 14 pages, with references from p.13. The rebuilt PDF text (`pdftotext -layout`) is identical to the shipped `erdos85-drop.13/main.pdf`, and the PDF contains no `??`. Raw output is in `compile-log.txt`.
- **Pending-marker gate:** PASS, 0 markers (`pending_marker.json`). The gate was run read-only without `--write-review`, so no `.pending` sibling was written, per the instruction to edit nothing outside this sidecar.
- **Artifact link hygiene / audience (step 6c):** `audience_check.json` reports 0 governance-vocabulary hits, 0 private-locator hits and 8 `unlinked_artifact_path` hits (L276–L284, Availability). Every term is the first argument of `\repofile`, which expands to a public `\href` at the pin, so all 8 are confirmed scanner false positives. `public_repo_url` is only `derived`, so none could be critical anyway.
- **Corpus tier:** inactive (no `corpus:` in BRIEF), so no `.corpus-audit/` sibling was written.

## Non-critical notes

- **`\repocommitshort` is a hand-written literal (L33).** It currently equals the first 12 characters of `\repocommit`, but the two can drift if only one is edited at the switch to the release tag. Derive it from `\repocommit` (for example with `\StrLeft` from `xstring`), or check both together at the repin.
- **The September 2026 cold axiom audit record still says "Sol re-audit pending".** v13 now names this audit as the source for the witness axiom lists and for Theorem B's standard-axiom status (L95, Table 2 row 1, L238). `AXIOM_AUDIT_COLD_20260927/AXIOM_AUDIT_COLD_20260927.md` at the pin opens "SINGLE-SEAT (claude), Sol re-audit pending". The claims themselves are well corroborated: its `axioms.out` is byte-identical (sha256 `53192372...`) to the 2026-09-16 overlay readout, which was run from Sol's input file (`AXIOM_AUDIT_OVERLAY_20260916.md`, command line `/tmp/erdos85-axioms-sol1.lean`). The October cold build, re-audited by Codex, reproduces the 607/604 corollary lists, which contain the six witness axioms. Still, a reader who opens the folder beside the linked `axioms.out` sees "re-audit pending", and §7 (L264) says every Lean result was accepted after independent review. Fix: add one line to that record noting the byte-identical Sol overlay readout (or Sol's later acceptance), or clear the "pending" header.
- **The cold-build README L147–L148** still says "A human/peer review of the runner and receipts remains distinct from this author-written deterministic checker." That remains true, since Codex's re-audit re-ran the same checker with extra rehash and manifest checks. A cross-reference to the #2749 re-audit in ACCEPTED.md would close the loop. It is not reader-facing in the paper.
- **The linked `FAILURE.md` (L113, L282) still contains a private local path** (L49: `/Volumes/Stripe/lean-genius/artifacts/...`), and so does `COLLECT.md` L24. The v12 review's m2 removed these from ACCEPTED/THIRDPARTY only. The paper is unaffected. Consider the same "retained on the project's artifact volume" wording before the release tag.
- **`proofs/` at the pin is not byte-identical to the execution commit `afa46bc5078`.** The difference is the 2-line comment change in `proofs/scripts/fetch-h7-certificates.sh`. `proofs/Proofs` is identical. ACCEPTED.md's identity claim refers to release-assembly commit `87e58b130b5`, where it holds. The paper makes no byte-identity claim about the pin.
- **Length:** the main text is about 12 pages against the BRIEF target of about 10. The changelog says this was not addressed (review m7).
- **Citations:** 4 supports, 11 partial (8 abstract-level), 2 unverified, 0 does-not-support, 0 unresolved. Sentences and bibliography are unchanged from v12, so the verdicts carry forward. See citation-audit.md.

## Audience-fit notes

None in the paper. The 8 scanner hits are confirmed false positives (see above).
