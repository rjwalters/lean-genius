# Audit flags for erdos85-drop.9

**Inputs.**

- `erdos85-drop/BRIEF.md` through amendments R-H3 and R-TITLE (2026-10-07).
- `erdos85-drop/refs/**` (42 entries), especially `H3_EVIDENCE_AUDIT_20261007.md` and `Q7_H3_PROFILE_EXCLUSION_20260910.md`.
- The v9 review `erdos85-drop.9.review/` (39/44, advance, 0 critical) and the deterministic siblings `.9.numeric`, `.9.pending`, `.9.audience`.
- `erdos85-drop.9/main.tex` as edited by the operator after the review (title per R-TITLE; review fixes M1 and m1 applied).
- Public branch content via `git ls-tree`/`git show`: `origin/erdos85/integration` = `4fee7764397`, `origin/erdos85/paper-v6` = `13400a4c890`; the certpilot working tree (branch `erdos85/paper-v6`, uncommitted edits present).
- Lean source under `proofs/Proofs/` (grep only; never built).
- A fresh `xelatex` + `bibtex` + `xelatex`×3 compile of a scratch copy.

**Verdict: AUDITED.** 0 critical flags; pending gate passes; the reviewer's `advance: true` stands. The version directory and all sibling directories were left untouched.

## Critical flags (block advancement to AUDITED)

None.

- **Citations.** 16/16 keys resolve; 0 `??`/`[?]`/`(?)` at the fixpoint; 0 `does-not-support` (6 partial, 10 unverified, source not on disk).
- **Numbers.** 0 mismatches, 0 untraced. The new H3 counts (3,337; 972; 3,600) match `Q7_H3_PROFILE_EXCLUSION_20260910.md`; the H1 totals were recomputed from the per-row receipts.
- **Build.** Clean at the `.aux` fixpoint (4 xelatex passes).
- **Unlinked artifact paths.** None qualify. `public_repo_url` is not declared (`audience_check`: `derived`), and the 6 hits (L254–L259) are all `\repofile` arguments the scanner does not expand.
- **BRIEF scope rules: held.**
  - Result A is never called a theorem/proof/"decided" ("The result is not a Lean theorem", L66; "Result A is not a theorem of Lean", L87).
  - cake_lpr placed outside Lean ("a HOL4 theorem about its compiled binary, not a Lean kernel check", L187).
  - Nothing claimed about Erdős 85 itself ("one drop is compatible with either answer", L66).
  - A-REG "a hypothesis with a stated rival" (L68, L228).
  - Both H1 open items appear in the abstract, §1 L87, §3.4 L187, Table 2 and L214.
  - **R-H3:** every H3 statement now matches `H3_EVIDENCE_AUDIT_20261007.md`. "Certificate-checked" is scoped to H1 (abstract, §1) and H7 $t\ge1$ (Result A) only; H3 is explicitly "not certificate-checked" (L110). No sentence names an H3 checker (R-V8 §5 request withdrawn by R-H3).
  - **Review M1 applied:** abstract L66 and Result A L78 now read "reviewed arguments with independently checked computation" for H3, H5 and H7 $t=0$, matching the H5 receipt, the H3 evidence audit, the BRIEF claim, §2.3 and Table 2. "Replayed" survives only where the H3 ref supports it (§2.3 L110; Table 2 H3 row L205).
  - **Review m1 applied:** "The hexagon verification and ours both reduce …" (L137); no Lean property is attributed to the TACAS paper alone.
  - **R-TITLE:** "A Drop at Forty-Nine in Erdős Problem 85" (L56) contains no "certificate-checked", "theorem", "proof" or claim about the answer.
  - R-AUD: `audience_check` governance 0, private-locator 0.
  - `scope_lint.py`: PASS (34 numbers, 40 Lean names) against `erdos85-certpilot/proofs/Proofs`.

## Outstanding dependencies

None. `anvil.lib.pending_marker erdos85-drop.9/` returns `pass: true`, 0 markers. Run without `--write-review`: the existing `erdos85-drop.9.pending/_review.json` already records the identical clean result, and this run leaves sibling dirs untouched (parallel-safe).

## Release preconditions (non-blocking for AUDITED; must precede the release tag / Zenodo step)

- **P1: the linked receipt `STRATA_AND_SMALL_ORDERS_20260928.md` is corrected only in an uncommitted working tree** (review M2; §8 L257 links it through `\repobase` = `erdos85/integration`).
  - Working tree (`erdos85-certpilot`, 10:11): H3 row now says "reviewed paper reductions with exhaustively replayed Python searches … no SAT verdict or LRAT proof exists for either cell formula (corrected 2026-10-07 …)", and the H1 row carries a "superseded 2026-10-07" note naming `orderFortyNineStratumExcluded_one_of_capacityInventory_checked` and the 12,094 + 1,160 + 96 + 1 split. Both corrections agree with the paper. `git status` shows the file as ` M` (not committed).
  - `origin/erdos85/integration` (`4fee7764397`) still reads, line 18, "checked LRAT proofs for both cells", and line 17 "the row-to-stratum assembly is an open formal obligation". The v9 commit `13400a4c890` is not an ancestor of integration.
  - Because §1 says "every number traces to a linked receipt", a reader who follows this link before the merge meets a statement the paper corrects.
  - **Fix:** commit the corrected file on `erdos85/paper-v6` together with v9, merge into `erdos85/integration`, and only then switch `\repobase` to the release tag. Optionally refresh the stale working copy `erdos85-drop/refs/STRATA_AND_SMALL_ORDERS_20260928.md` (it still carries both old rows).
- **P2: everything else the paper links is already public.** All 50 distinct `\repofile`/`\repofiletab` targets (55 uses) exist on both `origin/erdos85/integration` and `origin/erdos85/paper-v6` (`git ls-tree`), including the 9 that were paper-v6-only at the v8 audit (`CHECKING.md`, `h1_checker_kit/`, `h1_bank_check_20261006/` and receipts, `historical96_cake_lpr_receipts.jsonl`, both axiom receipts) and the new `Q7_H3_PROFILE_EXCLUSION_20260910.md` (byte-identical to the ref). Only P1's content is stale.

## Minor findings (carried from the review; optional)

- **m2 (review m2): Table 2 caption vs. "Case split" and "H3" rows** (L195, L202, L205). The caption says axiom lists are those printed by `#print axioms`, but neither `not_c4FreeMinDegreeWitness_fortyNine_seven_of_strata` nor `threeHighCanonicalGraphCover_all` appears in the cold audit, and those rows give no axiom list. Fix: add "(not in the cold audit)" to those cells, or print their axioms into a linked receipt.
- **m3 (review m3): post-table H3 sentence** (L214). "H3 could instead be closed by a certificate for each of its two cell formulas, but neither has been produced" is accurate; per `H3_EVIDENCE_AUDIT_20261007.md` the cell formulas were never run and four scout CNFs ended `s UNKNOWN` after ~12 h of Kissat. Optional: append "and whether they are within reach is untested".

## Nits (none changes a count, an evidence level or a link)

- **N1 (review n4)** (L110): "H3 is excluded by a reviewed paper argument" → optionally "H3 is excluded, outside Lean, by a reviewed paper argument", mirroring the H7 $t=0$ paragraph.
- **N2 (review n5)** (L89): §2 heading "The drop at 48 to 49" could echo the new title ("The drop at forty-nine").
- **N3 (review n1)** (L244): "the existence halves of the census" is opaque and defined by no receipt.
- **N4 (review n2)**: `tan2021cakelpr` and `heule2018schur` have no DOI; `biere2020cadical` (2020) is cited for CaDiCaL 3.0.1. Add DOIs only through a resolver.
- **N5 (review n3)** (L144 vs L175/L181): cake_lpr "commit `a36874a8`" vs the build `d23c413b…` used for the historical and cube-leaf checks; the receipts do not record that build's commit.
- **N6**: `H3_EVIDENCE_AUDIT_20261007.md` cites the cover's module as `Erdos85ThreeHighOneFiber.lean`; the file is `Erdos85OrderFortyNineThreeHighOneFiber.lean` (the paper's name is correct). Ref-side typo only.

## Non-critical notes

- **Build: clean, converged in 4 xelatex passes** (cap 5). xelatex → bibtex → xelatex (pass 2: natbib "Citation(s) may have changed", citations still undefined) → xelatex (pass 3: "Label(s) may have changed") → xelatex (pass 4: neither warning; `.aux` byte-identical to pass 3). All 5 invocations exit 0. Final log: 0 errors, 0 undefined citations/references, 0 overfull boxes, 4 underfull (badness 3271/10000/5741 in the §5 residue paragraph L220–221, long Lean names; 10000 on the §8 opening line L252–253, repository URL). Font-shape substitution warnings for Menlo are cosmetic. BibTeX: 0 warnings. 12 pages; references from p. 11. Raw bytes of all passes landed via `sidecar copy` (`compile-log.txt`, sha256 `06a2ac66ec987033…`).
- **Shipped PDF is current.** `erdos85-drop.9/main.pdf` (10:11, rebuilt by the operator after the title edit) has a converged log (no rerun warning) and its `pdftotext` text layer is identical to this audit's fixpoint PDF; it shows the R-TITLE title. The reviewer's "must be rebuilt" note is resolved. (Binary sha256 differs only through build timestamps/IDs.)
- **R-LINK / link hygiene.** 55 `\repofile`/`\repofiletab` uses, 50 distinct targets, all through `\repobase`; all present on integration (see P2). Room transcript URL linked (R-BRIDGE). No bucket name or `s3://` in the paper; "Not published" (L263) correctly excludes the bank proofs and checker kit.
- **Audience-fit notes** (step 6c): none (governance 0, private-locator 0).
- **Unverified citations (10) and partial (6).** No PDF of any cited work is on disk; before submission the author should confirm the claims carried by `tan2021cakelpr` (parsing inside the HOL4 guarantee, L135), `heule2024hexagon` (cake_lpr-checked, L137) and `zhang2017polarity` (r(109), r(155) bounds, L239).
- **Evidence drift.** `BRIEF.md` changed after the v9 snapshot (R-H3, R-TITLE, corrected `claim`); `refs_drifted: false` (`anvil.lib.evidence_drift check erdos85-drop erdos85-drop.9`). The paper agrees with both amendments. Advisory only.
- **Corpus provenance tier:** inactive (no `corpus:` key). No `.corpus-audit/` sibling written.
- **Iteration cap:** v9 is an operator-override pass beyond `max_iterations: 8`. Every remaining item is a wording nit or the P1 repository merge; none requires another lifecycle iteration.
- **Git sync:** skipped (no `.anvil/config.json`; run instructions exclude commits). No solver, AWS, Docker or Lean build was run.
