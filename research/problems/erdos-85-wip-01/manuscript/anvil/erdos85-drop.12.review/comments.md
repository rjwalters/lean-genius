# Comments — erdos85-drop.12

Keyed to rendered section headings, with `main.tex` line numbers in brackets. The thread is single-file, with no `\input` children. Paths, Lean names and records were checked at the `\repobase` pin `fa2b41268df024128ed4738b3bb500637cf1ec12`.

## blocker

None.

## major

- **M1 — §8 Availability [L272]: the paper names the wrong snapshot commit.**
  - Excerpt: "The source code, receipts and tooling linked here are in the Lean Genius repository (\url{…}) at commit \texttt{92ff6248033c}".
  - `\repobase` (L32) points every link at `fa2b41268df024128ed4738b3bb500637cf1ec12`. `92ff6248033c` is an earlier ancestor, 8 commits back and about 2,750 files behind in the research tree.
  - At `92ff6248033c` three records the paper cites do not exist (checked with `git cat-file -e`): `release_cold_build_20261011/ACCEPTED.md`, `release_cold_build_20261011/FAILURE.md` and `release_thirdparty_rebuild_20261012/ACCEPTED.md`.
  - The links resolve, but a reader who checks out the commit the text names gets a tree without the rebuild evidence that §2.2, §2.3 and Table 2 rely on.
  - The stale hash came from the changelog's "initial artifact pin" and was never updated on repin.
  - Fix: replace `92ff6248033c` with the `\repobase` commit (`fa2b41268df`, or whatever the final pin or tag is). Better, derive the printed hash from the same macro so the two cannot drift again.

## minor

- **m1 — §8 [L280] and pinned `proofs/scripts/fetch-h7-certificates.sh`: the linked script's comment disagrees with the paper.**
  - The paper says the script "requires the AWS CLI and authenticated credentials for Requester Pays access" and "has been exercised end to end only with credentials of the bucket owner's account".
  - At the pin `fa2b41268df`, the script's header still says "the requester pays the transfer, so any AWS credentials work". That is the untested claim the paper carefully avoids.
  - The corrected comment, and `proofs/Proofs/Certificates/strata-lrat.README.md`, exist only on the paper branch head (`2fb3abe6abc`), after the pin.
  - Fix: repin to a release-assembly commit that contains the corrected comment. Better still, run the fetch once from a separate AWS account before the tag, which removes the limitation instead of disclosing it.

- **m2 — Linked rebuild records carry superseded instructions and process language.**
  - These are links from the paper, not the paper's own text: R-AUD is met in the paper (0 governance and 0 private-locator hits).
  - `release_cold_build_20261011/FAILURE.md` ends: "The manuscript must not claim a completed cold project rebuild." It also says "Any future execution must have a newly generated, reviewed plan and separate spending authorization." The paper links it next to `ACCEPTED.md` and now does claim a completed rebuild, correctly, on the strength of attempt 2. A reader following the link sees an instruction that contradicts the text.
  - `release_cold_build_20261011/README.md`, linked as "cold-build recipe", says "the approximate 10-hour budget" and "the operator separately authorized retries until a pass".
  - Attempt-2 `ACCEPTED.md` has a private `/Volumes/Stripe/...` archive path and the sentence "Capture was run by Claude because Codex's session was inactive at terminal time; independent re-audit of the bundle is open for Codex".
  - The third-party `ACCEPTED.md` gives the bucket-owner AWS account number.
  - Fix: before the tag, add a dated banner to `FAILURE.md` ("Superseded by ACCEPTED.md (attempt 2); this record is retained as the failure receipt"), as was done for the STRATA receipt in v11. Trim the budget/authorization clauses from the README. Decide whether the account number and local path should stay in public receipts.

- **m3 — Table 2 [L223, L226]: the "Open in Lean" column still mixes in reproducibility notes (v11 m3, mostly fixed).**
  - The H7 $t\ge1$ row reads "nothing; not standard-axiom-only; replayed in the cold rebuild". The upper-side row reads "the two hypotheses; reproduced by the cold rebuild of all 893 modules".
  - "Replayed" and "reproduced" describe how a row was checked, not what remains open.
  - Fix: move both replay clauses to the "How it is checked" column, or drop them, since §2.2 and the post-table paragraph already say this.

- **m4 — §2.2 [L111] vs §7 [L262]: independent review of the rebuild.**
  - §7 says "Every Lean result and certificate collection in this paper was accepted only after another AI author independently reviewed it".
  - The attempt-2 `ACCEPTED.md` says the "independent re-audit of the bundle is open for Codex", and the v12 changelog row says "Awaiting Codex review and final audit". The third-party rebuild's byte-identical objects are strong corroboration, but they are not the independent review §7 describes.
  - The rebuild reproduces Lean results that had already been accepted; it is not a new Lean result. So the tension is small, but a careful reader will notice it.
  - Fix: complete the Codex re-audit of the attempt-2 bundle (or of the third-party bundle) before the tag. Otherwise, add to §2.2: "the audit of the retained output is automated; an independent re-audit is pending".

- **m5 — Typesetting: four link labels lose their spaces in the PDF (D7).**
  - `\repofile{…}{campaign totals}` [L132], `{census receipts}` and `{bank receipts}` [L191], and `{cold-build recipe}` [L280] render as "campaigntotals", "censusreceipts", "bankreceipts" and "cold-buildrecipe" (confirmed with `pdftotext`).
  - The cause: `\repofile` sets its label with the url-style `\lean` command, which drops spaces.
  - Fix: use a single-token label (e.g. `campaign_totals.json`, as in v11), or add a prose-label variant such as `\newcommand{\repolink}[2]{\href{\repobase/#1}{#2}}`.

- **m6 — §2.1 [L93] and §5 [L236]: "a cold rebuild" and "the cold audit" are now ambiguous.**
  - The paper now reports two kinds of cold build: the September 2026 axiom audit (`AXIOM_AUDIT_COLD_20260927`, the source of the witness and Theorem B axiom lists) and the October 893-module rebuilds (§2.2).
  - "A cold rebuild from source (pinned Lean 4.31.0 image, fresh build volume)" (§2.1) and "was compiled in the cold audit" (§5) read naturally as the §2.2 rebuild. As far as the records show, Theorem B's modules are not in the 893-module capstone closure.
  - Fix: write "the September 2026 cold axiom audit (\repofile{…/AXIOM_AUDIT_COLD_20260927/axioms.out}{axioms.out})" at both places.

- **m7 — Main-text length (D9).** The references now start on p. 13 after about 12 lines (v11: p. 12 after about 44). The main text is about 12 pages, against R-SIMPLE's ~10.
  - The m4 trim of the H7 paragraph was more than offset by the rebuild and fetch prose in §2.2 and §8.
  - Fix, if a page matters: in §2.2, collapse the three rebuild sentences into one and leave the attempt history to `ACCEPTED.md`/`FAILURE.md`, e.g. "Two cold rebuilds of the 893-module closure from the published files, the second fetching them with the download script, compiled every module, produced byte-identical objects and printed exactly these axiom lists (…); an earlier attempt failed in the runner (…)".

## nit

- **n1 — Title block [L58]: `\date{11 October 2026}`.** The paper reports a rebuild accepted on 12 October 2026. Update the date, or set it at tagging.
- **n2 — Compile log.** `compile-log.txt` ends its recorded pass with "Label(s) may have changed. Rerun to get cross-references right." All rendered cross-references are correct (Sections 2.2–8, Tables 1–2, 0 `??`), but run one more pass before the tag so the log reaches the fixpoint the changelog describes.
- **n3 — Version-dir bookkeeping (not the paper).** `erdos85-drop.12/_progress.json` says "links pinned to release assembly 87e58b130b5", and `changelog.md` still describes the "initial artifact pin" `92ff6248033c`. The paper pins `fa2b41268df`. Reconcile these when the final pin is set.

## v11 findings re-checked

- v11 m1 (H7 vs. hexagon precedent): resolved at L153.
- v11 m2 (publication filed under "fully independent audit"): resolved. The files are published, and L232 separates the formal gaps from reproducibility.
- v11 m3 (Table 2 column category): mostly resolved; see m3 above.
- v11 m4 (dense H7 paragraph / length): the H7 paragraph is resolved; total length got worse (m7).
- v11 n1 ("now superseded"): resolved (L147, L262).
- v11 n2 (\$225 qualifier and links): resolved at L191, though the link labels render without spaces (m5).
- v11 n3 ("previously settled"): resolved ("previously known", L85).
- v11 n4 (operator-ceiling clause in the H7 README): resolved at the pin. Similar language now appears in the new rebuild records (m2).
- v11 n5 (H5 table count): resolved.
- Release precondition (publish the 13 files and rebuild): done. The files are published with Requester Pays access, and two accepted rebuilds exist, the second with byte-identical objects.
- BRIEF advisory (stale `claim`): resolved. The frontmatter `claim` and the 2026-10-11 evidence update match the paper.

## Procedural notes

- sidecar: staged and committed through `python -m anvil.lib.sidecar cleanup/stage/commit` (issue #645 CLI shim), invoked from the main checkout as `PYTHONPATH=.anvil .anvil/.venv/bin/python -m ...` with absolute paths; `uv run` was not used. The worktree has no `.anvil/`, so the main checkout's installed copy was used.
- numeric-consistency: automated, 376 numbers, 1 claim, 0 findings. Run without `--write-review`, so no `erdos85-drop.12.numeric/` sidecar was written, in keeping with the caller's write-only-the-review-sibling instruction.
- pending-marker: automated, 0 markers, pass. No sidecar was written (same reason).
- audience-check: automated. 0 governance and 0 private-locator hits. The 9 `unlinked_artifact_path` hits (§8, L274–L282) are `\repofile` arguments the scanner does not expand; all 70 distinct targets exist at the pin. No sidecar was written (same reason).
- render-gate: pass on `erdos85-drop.12/main.pdf` and `erdos85-drop.12/compile-log.txt`: 14 pages, 0 overfull boxes, 0 placeholders. There is no `.12.audit/` yet, so the version-dir compile log was used.
- evidence-check: `anvil.lib.evidence_check` on the staged `scoring.md`: 9 dimensions, 0 findings, pass.
- evidence-drift: NO-SNAPSHOT (direct edit), treated as clean.
- No `lake build` or other Lean compilation was run. Pin contents were read with `git show`, `git cat-file -e` and `git grep` at `fa2b41268df`.
