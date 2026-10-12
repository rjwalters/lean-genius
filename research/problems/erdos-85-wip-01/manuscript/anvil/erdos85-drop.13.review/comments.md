# Comments — erdos85-drop.13

Comments are keyed to rendered section headings, with `main.tex` line numbers in brackets. Paths, Lean names and records were checked at the pin `2029149d7e42b74036ff0e1e82af6d33c2e32748` (`\repocommit`).

## blocker

None.

## major

None.

## minor

- **m1 — Main-text length (D9).** This is v12 m7, unchanged.
  - References start on p. 13 of 14, so the main text runs about 12 pages. R-SIMPLE's target is about 10.
  - The changelog openly defers it: "Not addressed in this pass".
  - Fix, if a page matters: collapse the three rebuild sentences of §2.2 [L113] into one and leave the attempt history to `ACCEPTED.md`/`FAILURE.md`.

- **m2 — Linked rebuild records: partial cleanup.** These are records outside the paper text and outside the rubric. The paper itself has 0 governance and 0 private-locator hits.
  - The v13 changelog row for v12 m2 says "README drops operator wording". At the pin, the retry-authorization sentence is gone, but `release_cold_build_20261011/README.md` (linked at L282) still says "Execution requires the exact plan SHA256 and separate spending authorization" and "the approximate 10-hour budget".
  - `FAILURE.md` now has the superseded banner, which resolves the contradiction. Its body still gives the local archive path `/Volumes/Stripe/lean-genius/artifacts/erdos85-cold-build-20261011/run-output.tar.gz` (line 49 of that file).
  - The new `ACCEPTED.md` text cites "squad review #2749", a pointer into the private room database, which R-AUD's spirit excludes from reader-facing material.
  - The account number was removed from `ACCEPTED.md`/`THIRDPARTY.md`, but it is still in raw evidence, `release_thirdparty_rebuild_20261012/evidence/fetch-job/job.log` (an STS ARN). That file is not linked from the paper.
  - Fix (optional, before the tag): trim the two README clauses and the local path, and replace "squad review #2749" with "(independent re-audit by Codex, PASS, 2026-10-12)". None of these affect a claim in the paper.

## nit

- **n1 — Table 2 [L219].** The table says "September 2026 cold audit" where the prose says "September 2026 cold axiom audit" (L95, L238). Use one name.
- **n2 — BRIEF (not the paper).** The "Current evidence update (2026-10-11, v12 preparation)" paragraph ends "final review/audit remain outstanding" and describes "the editable v12 draft". Add a dated line for the third-party-path rebuild, the Codex re-audit and the v13 pin when the thread closes.
- **n3 — Version-dir bookkeeping.** `erdos85-drop.13/_progress.json` carries no score history. This sidecar carries it, as v12's did.

## v12 findings re-checked (changelog table)

| v12 finding | v13 status | Evidence |
|---|---|---|
| Audit C1 / review M1: Availability named `92ff6248033c` | **Resolved** | L32–L34 define `\repocommit` = `2029149d7e42b74036ff0e1e82af6d33c2e32748`, `\repocommitshort` = `2029149d7e42`, and `\repobase` built from `\repocommit`. L274 prints `\texttt{\repocommitshort}`, and the PDF shows "at commit 2029149d7e42". All 70 PDF link URIs use the full hash and resolve (`git cat-file -e`). Both `ACCEPTED.md` files and `FAILURE.md` exist at the pin. The pin is on `origin`. |
| Audit M1 / review m4: independent check of cold-build acceptance | **Resolved** | `ACCEPTED.md` at the pin: "Independent re-audit (Codex, squad review #2749, PASS, 2026-10-12): reran `audit.py` on the retained bundle (893 sources, exact 601/607/604, same RUN.json sha256), rehashed the archive …". The squad DB `review_requests` row 2749 is resolved by codex with "PASS for requested evidence re-audit". The paper at L113 says the audit was "repeated independently by a second AI author", which is now consistent with §7 Reviews [L264]. |
| Review m1: fetch-script comment "any AWS credentials work" | **Resolved** | The pinned `proofs/scripts/fetch-h7-certificates.sh` reads "authenticated AWS credentials are needed (tested so far only with credentials of the bucket owner's account)". |
| Review m2: FAILURE.md read as current; private path and account in records | **Mostly resolved** | The banner was added. The local path and account number were removed from both `ACCEPTED.md` files and `THIRDPARTY.md`, and the retry-authorization sentence was removed from the README. Residue is listed under m2 above. |
| Review m3: replay notes in "Open in Lean" | **Resolved** | Table 2 L225 and L228. |
| Review m5: labels rendered without spaces | **Resolved** | Single-token labels at L134, L193 and L282. The PDF text has no "campaigntotals", "censusreceipts", "bankreceipts" or "cold-buildrecipe". |
| Review m6: "cold rebuild"/"cold audit" ambiguous | **Resolved** | L95, L219 and L238 name the September 2026 audit, and `AXIOM_AUDIT_COLD_20260927/axioms.out` at the pin lists the witness and Theorem B axioms as stated. |
| Audit minor: "second cold rebuild" was the third attempt | **Resolved** | "A further cold rebuild" [L113]. |
| Audit minor: output bundle publication status | **Resolved** | "retained outside the repository and is not published" [L282]. |
| Nits: date; rerun warning | **Resolved** | `\date{12 October 2026}`. `compile-log.txt` has no "Rerun" or "may have changed" line. |
| Review m7: length | **Not addressed (declared)** | See m1. |

## Hard scope rules (re-checked on v13)

- Result A is never called an unconditional Lean theorem. "Result A is not an unconditional theorem of Lean" [L89], and the Abstract says "Lean thus derives the upper side from two explicit unsatisfiability hypotheses, which the external checks support but which are not admitted into Lean". The hypotheses are H1 and H7 with t=0, cake_lpr is outside the kernel, and the 598 `native_decide` axioms are disclosed.
- "Nothing is claimed about Erdős Problem 85 itself" [L89]. "one drop is compatible with either answer" (Abstract).
- "$\AREG$ is not asserted" [L89]. Theorem B is an implication only.
- The v13 edits introduce no new claim. "repeated independently by a second AI author" describes a reproducibility audit, not a change in formal status.

**No critical flag.**

## Procedural notes

- sidecar: staged and committed through `python -m anvil.lib.sidecar cleanup/stage/commit` (issue #645 CLI shim), run from the main checkout as `PYTHONPATH=.anvil .anvil/.venv/bin/python -m ...` with absolute paths. The worktree has no `.anvil/`.
- numeric-consistency: automated, 375 numbers, 1 claim, 0 findings, pass. Run without `--write-review`.
- pending-marker: 0 markers, pass. Run without `--write-review`.
- audience-check: 0 governance hits, 0 private-locator hits, and 8 `unlinked_artifact_path` hits (Availability, L276–L284). All 8 are `\repofile` arguments, so they are scanner false positives; every target exists at the pin. Run without `--write-review`.
- render-gate (`anvil.lib.render_gate.gate.gate` on the version-dir PDF and compile log): pass, 14 pages, 0 overfull boxes, 0 placeholders.
- evidence-drift: no snapshot recorded (direct edit), no drift.
- evidence-check: run on the staged `scoring.md`; see `_meta.json`.
- No `lake build` or other Lean compilation was run.
