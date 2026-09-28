# Findings — erdos85-drop.5 (cross-section observations)

## R-AUD (audience only) — held; the `audience_fit` flag of `erdos85-drop.4.operator/` is resolved in the text

Governance-vocabulary grep on `erdos85-drop.5/main.tex` (case-insensitive, comments included), each hit judged:

| Term | Hits | Judgment |
|---|---|---|
| `authoriz` | 0 | — |
| `goal` | 0 | — |
| `message` | 0 | — |
| `outline v` | 0 | — |
| `s3://` | 0 | — |
| `refs/` | 0 | — |
| `board` | 0 | — |
| `commission`, `ticket` | 0 | — |
| `operator` | 4 | L284 "The defect operator" (the linear-algebra operator of §5.2); L319 the acknowledgement the BRIEF requires ("The project's human operator, who set its priorities and scope, … are acknowledged; neither is an author."), addressed to the reader; L358, L369 `\operatorname` (LaTeX). No sentence addresses the operator. |
| `budget` | 5 | the budget-plan file name in path and label (L256, L327), "replay budget model" (L262), "deletion budgets" (L356), "budgets" in the census-tooling pointer (L379) — all technical. |
| `cancel` | 1 | "cancellation" of a trace term (L377). |
| `gate` | 9 word-hits | "aggregate" ×4, the directory names `baer-repair-gate`, `retained-subplane-gate`, `mod2-root-gate`, "memory gate" (L262, a checker's memory limit), "review gates" (L319, the acknowledgement — nit in comments.md). No publication gate. |
| `transcript` | 5 | L319 (acknowledgement), L338 ("the reviews themselves are entries in the unpublished transcript"), L340 ("the collaboration transcript" among the three unpublished collections), L367 (Appendix B opening), L379 (Methods) — each says the transcript is unpublished; none points into it. |
| `room` | 2 | "shared room infrastructure" (L319), "Room protocol: a persistent shared chat room (the unpublished transcript)" (L379). |
| `publication` | 1 | a LaTeX comment in the preamble (L31), not in the rendered text. |

Every v4 example the operator critique listed is gone or restated as a reader-relevant fact, checked one by one in the sentence-level diff of v4 → v5: §4.5 "No replay wave is authorized by this estimate." → "The estimate prices a replay that has not been run; no certificate was replayed or produced for this paper."; "subject to the operator's publication gate" (§4.5, §7) → "The certificate bank is not public; a requester-pays copy with an exact release manifest would let others fund independent verification." / "No requester-pays copy of the certificate bank has been published, so no release manifest is listed."; Appendix A "all 20 authorized solver attempts" → "all 20 solver attempts"; the abstract's and §5.3's "the operator's plane-order reading" → "a stated rival" / "the plane-order reading is the principal rival"; §1 "the appendices carry transcript pointers into the campaign record" → the link sentence; §7's contributions paragraph reduced to the acknowledgement; Appendix B's "Persistence", "The human role", "Scope words" and "Why Erdős problems" paragraphs removed with every goal number, message number, outline version, commit hash and "operator review" pointer (0 residual hits for each), the technical core of "Scope words" (both axiom lists printed) folded into "Silence is not success" and the pre-fire-manifest sentence into the exchange-rate paragraph. Appendix A's outline-version / commit-hash / divergence / message pointers are now section and row pointers into the two linked public records (`FINAL_PROOF_OUTLINE.md`, `CUTS_LEDGER_DRAFT.md`); rows 1, 56 and 174–180 exist in `CUTS_LEDGER_DRAFT.md`.

What Appendix B keeps is technical (verification asymmetry; the 80/88-owner case study; adversarial diversity; the structure–compute exchange rate; silence is not success; Methods as pointers), written for a reader, each lesson naming the Lean modules and ledger files that carry it. The two process anecdotes that remain ("withdrawn five minutes later", "three agents waited for the final file check") state a lesson without a transcript pointer.

## R-LINK (public links) — held; the `non_public_links` flag of `erdos85-drop.4.operator/` is resolved in the text

- Preamble [L36–L38]: `\newcommand{\repobase}{https://github.com/rjwalters/lean-genius/blob/erdos85/integration}`, `\repofile{<path>}{<label>}` → `\href{\repobase/#1}{\lean{#2}}`, and the table variant `\repofiletab`; one base macro, switchable to the release tag.
- **69 `\repofile` / `\repofiletab` uses, 60 distinct repository paths** (the task brief's "73" was an estimate; the source count is 69). Every label is a suffix of its path (0 mismatches). **Every path exists on disk** at `/Volumes/Stripe/lean-genius/claude-e85-wrapup/<path>` (0 missing; 16 Lean modules under `proofs/Proofs/`, 44 research paths under `research/problems/erdos-85-wip-01/`, of which 11 are directories). The `AXIOM_AUDIT_COLD_20260927.md` report is linked at its real location inside `AXIOM_AUDIT_COLD_20260927/` (verified on disk), not at the research root as the thread's `refs/` copy suggested.
- **GitHub spot-check** (read-only `curl`, HTTP status of `https://github.com/rjwalters/lean-genius/blob/erdos85/integration/<path>`): 11 of 11 file targets returned 200 (`Erdos85FiniteDropWitnesses.lean`, `Erdos85OrderFortyNineSevenHighCertificates.lean`, `Erdos85PartialCentralReconstruction.lean`, `CENSUS_TIMING_20260928.md`, `q7_h5_closure_ledger/reviewer/REVIEW2065.json`, `sat49/BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt`, `AXIOM_AUDIT_COLD_20260927/axioms.out`, `phase_b_h1_census_20260927/cube-h1_81494a6ef36d3ec9/tree-check.json`, `CUTS_LEDGER_DRAFT.md`, `cayley-census-q11-q13/CAYLEY_CENSUS_Q11_Q13_20260913.md`, `manuscript/FIRST_DROP_LITERATURE_CHECK.md`); 3 of 3 directory targets returned 301 → 200 at the `/tree/` URL (`phase_b_h1_verdict_cloud_20260921/`, `l6-representability/`, `proofs/Proofs/`) — the redirect nit in comments.md.
- **Rendered PDF**: the scratch compile's link annotations carry exactly 64 distinct URIs — the 60 repository paths, the repository root `\url`, and the three bibliography URLs (arXiv, ANU, erdosproblems.com); every repository URI starts with `\repobase`; none contains a backslash, a space or `%5C` (raw underscores survive the macro).
- **No bare artifact names remain**: a scan of the body with every `\repofile` argument masked finds 0 tokens ending in `.lean`, `.md`, `.py`, `.json`, `.tsv`, `.txt` or `.lz4p7` and 0 `\lean{}`/`\texttt{}` arguments containing a slash other than the branch name `\texttt{erdos85/integration}`. The eleven certificate modules between `T1Rep0` and `T7Rep0` are named by range, with both endpoints linked; the S3 bucket, the artifact-volume paths and the checksum manifest of v4 are gone.
- **Non-public material in one sentence**: "Three collections are not published: the certificate bank (about 6 TB gzipped), the artifact volume that holds the full solver logs, CNF snapshots, run directories and the thirteen packed LRAT files the H7 certificate modules read, and the collaboration transcript." (§7 [L340]); §4.2 says the modules read "from an absolute path on the project's artifact volume" with no path.

## The v4 audit minors and nits — fixed in the text

| Item | v5 text | Verified against |
|---|---|---|
| m1 "cells" for "representatives" (§1) | "one for each of its thirteen canonical representatives with a positive triple" [L85] | Table 2 (fourteen representatives, $1,1,2,3,3,2,1,1$), §3.2, §4.2, §6 |
| m2 complement completion "for eleven" (§4.2) | "source enumeration, with complement completion where the ledger required it (three roots), for eleven of the twelve $a=7$ roots and a cycle-exclusion chain for the twelfth" [L195] | `H7_CLOSURE_20260915.md`: A7 "with source-complement completion 2683 where required"; 2683 appears on `cube_F7_t10`, `_t11`, `_t13` only |
| m3 1,412 preparations "for the 1,161 residual rows" (§1, §7) | "1,412 input preparations over the four cloud passes for the 1,137 rows dispatched to the cloud (the 24 pilot rows ran on the local Mac; …)" [L85]; "the 1,412 preparation receipts for the 1,137 cloud-dispatched rows" [L325] | `CENSUS.md` Table (pilot 24; pass 1 1,137); `CENSUS_TIMING_20260928.md` (1,132 + 261 + 17 + 2 = 1,412) |
| m4 "compiler-generated axioms that we list" (§2) | "which adds compiler-generated axioms: we list them for the witnesses (Table 1) and state the dependency for the certificate checks (Section 4.2)" [L107] | Table 1 caption; §4.2 |
| n1 two vocabularies for one trust mechanism | "Lean records each `native_decide` use as a per-declaration axiom named `…_native.native_decide.ax_N`; the six such entries in Table 1 are instances of the compiler-trust axiom `Lean.ofReduceBool`, and that single name is used below for the thirteen H7 certificate checks" [L117] | `axioms.out` (six `…_native.native_decide.ax_N` entries) |
| n2 "over four passes" (Table 4) | "under declared caps over the pilot plus four cloud passes" [L242] | Table 3 |

## No disclosure weakened while the governance text was cut

Sentence-level diff of `erdos85-drop.4/main.tex` → `erdos85-drop.5/main.tex` (links normalized to labels), every removed or replaced sentence read:

- Trust statements kept or strengthened: "The certificates reside on absolute local paths, not in the public source tree." → "The packed certificates reside on the project's artifact volume, which is not published, so the thirteen modules cannot be rebuilt from the public source tree alone (Section 7)." (§4.2); Table 4 "certificates on absolute local paths" → "certificates on the unpublished artifact volume"; §4.4 "read their certificates from absolute local paths" → "from the unpublished artifact volume"; the `Lean.ofReduceBool` dependency, the missing cold rebuild and the 2026-08-15 manifests are unchanged in §4.2, Table 4, §4.4 and §6.
- "No certificate is produced" statements kept or strengthened: Table 4 "no certificate is produced" and "none a certificate from this paper" unchanged; §4.2 "none has a certificate produced by this paper" unchanged; §4.5 gains "no certificate was replayed or produced for this paper".
- Result A's evidence level unchanged: "computational evidence" (title, abstract, §1, §4 heading), "verdict-level evidence, not a theorem" (abstract), "Result A is evidence, not a theorem" (§1), "a computational result, not an unconditional Lean theorem" (§4), "Result A is computational evidence, not a theorem" (§6); *decided* is applied only to Boza's entries, the negated non-claim and "63-to-64 is not a decided drop"; *conjecture* only in "not a conjecture we endorse"; nothing is claimed about Erdős Problem 85 itself (abstract, §1 twice, §6). `scope_lint.py`: PASS.
- A-REG: "an unproved hypothesis with a stated rival, not a forecast" (abstract), "an unproved hypothesis with a stated rival, not a conjecture we endorse" (§1), "the live mathematical frontier, not a conclusion licensed by the finite data; the plane-order reading is the principal rival" (§5.3). The rival's content is unchanged; only its attribution to the operator is gone.
- Dropped from Appendix B without loss: the "Scope words" sentence "a completed census does not decide an eventual property" is carried by §6 ("compatible with either answer to the problem as posed, which a finite computation cannot settle"); the "Persistence" paragraph's four-records inventory and the "Why Erdős problems" motivation carried no disclosure.
- One small loss, recorded as a minor: the abstract's lower-sides sentence dropped "through `native_decide`" (kept in §1, Table 1, §4.1, §6).
- Every `refs/`-prefixed receipt of v4 §7 is present in v5 at its canonical repository path; the receipt list lost no entry and gained `AXIOM_AUDIT_COLD_20260927.md`, `h7-closure-ledger-20260915/`, `sat49/data/`, `h1-census-table.json`, the cloud-tooling directory and the cube-tree checker.

## Lean identifiers — 0 missing

85 distinct `\lean{}` / `\leantab{}` / `\texttt{}` identifier-shaped arguments; 69 matched by `grep` against a one-pass dump of all `theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|opaque` declarations under `/Volumes/Stripe/lean-genius/claude-e85-wrapup/proofs/Proofs/` (no build). The 16 non-matches are all explained: the core axioms `propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`; `CNF.Unsat` (Std, used as `Unsat` in the cube consumer's signature); the applied forms `OrderFortyNineStratumExcluded h` and `orderFortyNineHighVertices G` (both bare names are `def`s); the hypothesis `hno49`; the case id `h1_81494a6ef36d3ec9`; the `v2cnf` binary; `native_decide`; the wildcard `h305Owner88*_check` (exactly six `theorem h305Owner88…_check` declarations exist); the two planned endpoint names `minDegreeForC4_…_of_generatedSevenBaseCertificates`, absent by §3.1's own statement; and two macro-definition fragments from the preamble. The 16 `.lean` modules named through `\repofile` all exist as files. `scope_lint.py erdos85-drop.5/main.tex`: PASS (65 numbers, 53 Lean names).

## Number traceability

`scope_lint.py` PASS covers every 4+-digit number and every unit-bearing decimal against `refs/` (excluding `DRAFT.md`). The two new arithmetic-bearing phrases of v5 (1,137 + 24 = 1,161; the three complement-completion roots among the eleven $a=7$ rows) match `CENSUS.md` / `CENSUS_TIMING_20260928.md` and `H7_CLOSURE_20260915.md`. The "1,413 cloud run directories" of §4.2 and §7 match `CENSUS.md` line 6. The v4 spot-checks of §4.5–4.6 against `CERT_BANK_STATS_20260926.md`, the budget plan, the fleet-cost JSON and `H1_V3_SOLVER_TIMING_20260916.md` were not repeated: those sentences are byte-identical to v4 except for the added links.

## Rendering and build

Compiled in a scratch copy (`main.tex`, `refs.bib`, `anvil-paper.cls`; the version dir untouched): `xelatex` → `bibtex` → `xelatex` → `xelatex` (the document uses `fontspec`; `pdflatex` not applicable), all exits 0; 0 errors; 0 undefined citations or references; no "Rerun" / "Label(s) may have changed" on the third pass; BibTeX 0 warnings; 0 overfull boxes; 5 underfull lines (badness 1776, 2285, 3547, 3989, 6094; none at 10000; v4: 7); 26 cosmetic `TU/Menlo` font-shape warnings from the `hyphenat` `htt` option. 20 pages (v4: 21): §7 starts p. 14, Appendix A p. 16, Appendix B p. 18, References p. 19. `pdftotext`: 0 `??`, 0 `[?]`, 12 bibliography entries. The version dir's own `compile-log.txt` and `main.pdf` agree (20 pages, 0 overfull). Render gate passed (`_gate.json`).

## Structure and the cold-reader check — pass

Abstract (two paragraphs: Result A with its qualifier and Boza correspondence; Theorem B with its rival) → introduction (two results, significance, non-claims, organization) → related work → definitions and interface → Result A (witnesses, strata, evidence table, trust, cost, cube route) → Theorem B → interpretation → contributions and availability → appendices. A reader can state both results and the qualifier from the abstract alone; the central claim is the BRIEF's strongest honest claim, not a subsidiary; the title could not describe fifty adjacent papers. No underclaiming / buried-lede finding.

## Prior-review items (v4 review) — disposition

Minors: representatives noun (fixed); complement completion (fixed); which review numbers are inspectable (fixed by the §7 sentence and the links at each quotation); packed-LRAT release status (fixed) and size (declined — no receipt; accepted); 303-word abstract (fixed: two paragraphs, 260 tokens); ninety-word certificate sentence (fixed: three sentences); method lineage (declined again — web search off; accepted, still open under D4). Nits: "an `include_str`" (fixed); `\lean{}` for paths (resolved by R-LINK — `\lean{}` arguments are now Lean names, the binary, the hypothesis, the axioms and the case id); figure (declined with reason; still open under D6); underfulls and font warnings (no action needed).

## Evidence drift

`anvil.lib.evidence_drift check erdos85-drop/ erdos85-drop.5/`: `CLEAN` (brief_mtime 1790632806.27 = the BRIEF as amended on 2026-09-28 with R-AUD / R-LINK; refs_mtime 1790628614.00; both equal to the v5 snapshot). The BRIEF amendment predates the v5 revision, so the version under review was drafted against the binding rules.

## Conditional tiers (all inactive this pass)

`erdos85-drop/.anvil.json` declares only `max_iterations: 6` (no `venue`, no `artifact_verify`); `BRIEF.md` frontmatter has no `corpus:`, no `subjects:`/`voice:`, no `pending_sources:`; `web_search: false`. No litsearch, vision or corpus-audit sibling exists at any version. Rubric version transition: none (`erdos85-drop.4.review/_meta.json` is stamped `anvil-pub-v2`, the current rubric).

## Iteration cap

This is iteration 5 of `max_iterations: 6` (cap raised from 4 on 2026-09-28 for the operator-directed revision). The paper advances above threshold with no critical flag and no pending marker, so the thread reaches `READY` on the score path and proceeds to `paper-audit`; the v4 audit's tool-evidence pass (citation audit, numerical audit, compile) must be re-run on v5 before `AUDITED`, and the operator sibling's two flags should be recorded as resolved there as well so that `anvil.lib.critics.aggregate` over the v5 siblings is no longer BLOCK.
