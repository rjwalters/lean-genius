# Changelog — erdos85-drop.4 → erdos85-drop.5

Operator-directed revision (per-thread cap raised 4 → 6 in `erdos85-drop/.anvil.json`). Revised
against every critic sibling at version 4: `erdos85-drop.4.review/` (generic rubric `anvil-pub-v2`,
37/44, `advance: true`, 0 critical, 0 major, 7 minor, 6 nit), `erdos85-drop.4.audit/` (tool
evidence, AUDITED: 0 critical, 0 major, 4 minor m1–m4, 2 nits n1–n2, non-critical notes),
`erdos85-drop.4.operator/` (judgment, `verdict: BLOCK`, 2 critical flags `audience_fit` and
`non_public_links`, 3 blocker + 1 major findings; `critique.md` F1/F2 and the audit carry-overs),
`erdos85-drop.4.numeric/` (0 findings) and `erdos85-drop.4.pending/` (0 findings, no `[PENDING]`
markers). No venue overlay, litsearch, vision or corpus-audit sibling exists at version 4; the
corpus tier is inactive (no `corpus:` key), so no `provenance.md` is carried. Iteration 5 of
`max_iterations: 6`, `revised_from: 4`.

Verdict pre-check (paper-revise step 4): the reviewer advanced v4 and the audit raised no critical
flag, but the operator sibling carries two critical flags tied to the two hard rules added to
`BRIEF.md` on 2026-09-28 (R-AUD, R-LINK); `anvil.lib.critics.aggregate` over the five siblings is
BLOCK, so revision is required. Both flags are addressed in the prose (generic-rubric-standing
flags are not declinable).

## Build and checks

- Build in `erdos85-drop.5/` (`compile-log.txt`; the document uses `fontspec`, so `xelatex` is
  kept): `xelatex` + `bibtex` + `xelatex` ×2, all exits 0; **0 LaTeX errors, 0 undefined citations
  or references** (`Label(s) may have changed`: 0 on the final pass), BibTeX 0 warnings (the
  `warning$ -- 0` counter line is the only "warning" token in `main.blg`), **0 overfull boxes,
  5 underfull lines, maximum badness 6094, none at 10000** (v4: 0 / 7 / 6094), 54 cosmetic
  `TU/Menlo` font-shape lines from the `hyphenat` `htt` option (unchanged class of warning),
  **20 pages** (v4: 21): §7 starts p. 14, Appendix A p. 16, Appendix B p. 18, References p. 19, so
  the body is 13 pages against the BRIEF's 12–18-page target. `pdftotext main.pdf`: 0 `??`,
  0 `[?]`, 12 bibliography entries.
- `python3 scope_lint.py erdos85-drop.5/main.tex`: **PASS** (65 numbers checked, 53 Lean names
  checked; v4: 66 / 53). Note for the lint: its identifier regex matches `\texttt{}` and `\lean{}`
  only, so the labels inside `\repofile{}` are not scanned. No coverage is lost — every label is a
  file or directory name (`.lean`, `.md`, `.py`, `.json`, `.tsv`, `.txt` or a trailing `/`), which
  the lint excludes anyway — and every Lean *declaration* name is still written with `\lean{}` /
  `\leantab{}`. `scope_lint.py` was not edited.
- Link check (read-only): all 69 `\repofile` / `\repofiletab` uses (60 distinct repository paths)
  were verified with `os.path.exists` against `/Volumes/Stripe/lean-genius/claude-e85-wrapup/`;
  **no named path is missing**. One path differed from the v4 wording: the cold-audit report
  `AXIOM_AUDIT_COLD_20260927.md` lives *inside* `AXIOM_AUDIT_COLD_20260927/` (beside `axioms.out`
  and `axioms.lean`), not at the research root as the thread's `refs/` copy suggests; §7 links the
  directory, the report and `axioms.out` at their real paths. An uncompressed scratch compile
  (`xdvipdfmx -z 0`) shows exactly 60 distinct link URIs in the PDF, one per path, all under
  `https://github.com/rjwalters/lean-genius/blob/erdos85/integration/`, none containing `\`, a
  space or a `%5C` escape (raw underscores survive `\href` when passed through the macro; verified).
- Governance-vocabulary grep on the final `main.tex` (`-i`): `authoriz` 0; `goal` 0; `message` 0;
  `outline v` 0; `s3://` 0; `refs/` 0; `board` 0; `operator` 4 — L284 "The defect operator" (the
  linear-algebra operator of §5.2), L319 the one-sentence acknowledgement of the project's human
  operator that the BRIEF requires ("acknowledged, not authors"), and L358 / L369 `\operatorname`
  (LaTeX). Also checked: `transcript` 5 occurrences (the acknowledgement, the review-number sentence, the
  availability paragraph, the Appendix B opening and the Methods pointer — each says it is
  unpublished), `room` 3 ("shared room infrastructure" in the acknowledgement; "Room protocol" and
  "chat room" in the Methods pointer), `gate` 14 word-hits (aggregate ×4, `baer-repair-gate` ×2,
  `retained-subplane-gate` ×2, `mod2-root-gate` ×2, "memory gate" ×3, "review gates" ×1; no
  publication gate), `budget` 7 (the budget-plan file name ×4 in path and label, "replay budget
  model", "deletion budgets", "budgets" in the census-tooling pointer), `cancel` 1 ("cancellation"
  of a trace term). No `\lean{}`
  argument is a path or file name any more (`\lean{[^}]*/` and `\lean{…\.(md|py|json|tsv|txt|lean)}`:
  0 hits).
- No solver, AWS, Docker, Lean build or git command was run. `erdos85-drop.4/`, the critic siblings,
  `BRIEF.md` and `refs/` were not modified. `figures/` carried over (empty in v4; no `figures/src/`).

## Structural changes (summary)

- **Preamble (R-LINK).** `\newcommand{\repobase}{https://github.com/rjwalters/lean-genius/blob/erdos85/integration}`
  and `\newcommand{\repofile}[2]{\href{\repobase/#1}{\lean{#2}}}` added after the `\lean`/`\leantab`
  definitions (hyperref is loaded by `anvil-paper.cls`). The label is typeset in typewriter through
  the existing `\lean` url-command rather than bare `\texttt{}` so that raw underscores need no
  escaping and long module names can break at underscores, dots, slashes and (discouraged)
  camel-case boundaries — with bare `\texttt` the first compile produced an 81 pt overfull line on
  `Erdos85PartialCentralReconstruction.lean` and two badness-10000 lines on certificate-module
  names. `\repofiletab` (label via `\leantab`, no camel-case breaks) is used for the single link
  inside a table cell (Table 4, witnesses row). `\lean{}` / `\leantab{}` remain the macros for Lean
  *declaration* names.
- **Every named artifact is a link.** 69 links, 60 distinct paths: 16 Lean modules under
  `proofs/Proofs/` (the witnesses module, the two consumers, the H7 census, the T1Rep0 and T7Rep0
  certificate modules, the H7 certificates aggregate, the two capacity modules, the `v2cnf` emitter,
  the owner-88 certificate module, the partial-central-reconstruction module) and 44 research paths
  under `research/problems/erdos-85-wip-01/` (the §7 receipt list at its canonical locations, the
  H5 ledger directory and files, the H7 closure ledger and its review archive, the cloud tooling
  directory and the cube tree checker, the non-isomorphism script, receipt and data directory, the
  Appendix A ledger files and directories, the proof outline and the cuts ledger). The thread's
  `refs/` copies are no longer named anywhere.
- **§7 rewritten.** The receipts paragraph opens by saying every link points at the branch of
  record and will be repointed at the release tag; the receipt list is unchanged in content but
  every entry is a link at its canonical path; a new sentence states which review numbers a reader
  can inspect (the identifiers recorded in the linked ledger files) and that the reviews themselves
  are in the unpublished transcript; "Data and code availability" names the public locations and
  describes the three unpublished collections (certificate bank, artifact volume with logs, CNFs,
  run directories and the thirteen packed LRAT files, collaboration transcript) in one sentence
  with no bucket name or volume path.
- **Appendix B rewritten** as "Technical lessons from the collaboration": five technical
  paragraphs (verification asymmetry; the 80/88-owner case study; adversarial diversity; the
  structure–compute exchange rate; silence is not success) plus "Methods" as pointers. All
  room-message numbers, review numbers that only index the transcript, outline-version pointers,
  goal numbers, authorizations and commit hashes removed; "Persistence" and "The human role"
  dropped; the technical core of "Scope words" (both axiom lists printed for the two order-64
  theorems) folded into "Silence is not success"; the non-technical "Why Erdős problems" paragraph
  dropped. Appendix B is now one page (v4: three).
- **Appendix A pointers** replaced: outline-version and commit-hash pointers become section/row
  pointers into two linked public files, the campaign's working proof outline
  (`FINAL_PROOF_OUTLINE.md`) and its cuts ledger (`CUTS_LEDGER_DRAFT.md`); the eight ledger files
  and directories already named are linked.
- **Abstract** split into two paragraphs (Result A / Theorem B), the negative-map sentence removed
  (it lives in §5.3), the solver names and the "cheaper cube-partitioned route" clause dropped;
  303 → 260 whitespace tokens (including LaTeX macros).
- **§3.1** long Lean names (the two finite-drop-core statements and the two planned endpoint
  names) moved into `flushleft` blocks, as §5.2 already does, after the reflow caused by the new
  sentence produced two badness-10000 lines.

## Critic notes → changes

| Source | Note | Resolution |
|---|---|---|
| erdos85-drop.4.operator (critical-flag `audience_fit`, R-AUD) | Statements about authorization, publication gating, operator goals and private-transcript pointers addressed to the operator rather than the reader (L237, L239, L300, L321, L344, L346–L368 and the whole text) | Addressed everywhere. §4.5 L237 "The cancelled replay plan is retained as a cost model, not an active launch plan." → "The replay plan (link) was not executed; it is retained here as a cost model."; "No replay wave is authorized by this estimate." → "The estimate prices a replay that has not been run; no certificate was replayed or produced for this paper." §4.5 L239 "…subject to the operator's publication gate and an exact release manifest." → "The certificate bank is not public; a requester-pays copy with an exact release manifest would let others fund independent verification." §6 L294 "can be released…" → "is not yet public; released as a requester-pays object store with an exact manifest, it would let…". §7 L319 → "No requester-pays copy of the certificate bank has been published, so no release manifest is listed." §7 L321 "a requester-pays copy is subject to the operator's publication gate" → removed; the bank is described as unpublished. §1 L84 "the appendices carry transcript pointers into the campaign record" → "Every file, directory and Lean module the paper names is linked to its location on the branch of record (§7), and material that is not published is described as such." §1 L86 "records how the collaboration ran" → "records the technical lessons of the collaboration". Appendix A L327 "Ledger pointers (outline versions, cuts-ledger rows, commit hashes) are transcript pointers into the campaign record." → the two consolidated records are linked and the pointers are to their sections and rows; L330–L339 outline-version, commit-hash, divergence-number and room-message pointers removed (see the Appendix A row below); L342 "(outline v2.64, §A.5.2)" → "(proof outline §A.5.2)"; L344 "all 20 authorized solver attempts" → "all 20 solver attempts". Appendix B L346–L368 rewritten (see the next row). Every governance word is gone (grep above). |
| erdos85-drop.4.operator (blocker, D9; F1) | Appendix B carries governance narrative (goal numbers, authorizations, operator review, room-message numbers) that no reader can use | Appendix B rewritten as "Technical lessons from the collaboration". Kept and rewritten without pointers: verification asymmetry ("message 31890/31895" → "was withdrawn five minutes later, when its author re-expanded…"); the 80/88-owner case study ("room messages 31664, 31674, 31697; outline v2.64 entry 2.61" and "messages 31809, 31845, 31882" removed; the certificate module is now a link; "the integrator rebuilt the chain cold" → "a cold rebuild of the chain printed the exact six Owner88 axioms"); adversarial diversity ("Review #939", "messages 31868–31874", "messages 31905, 31907, 31913; banked at 19f227dced and 0ae7069f40", "messages 31989, 31994, 31997" removed; the P8 episode now points at the inverse-sign entry of Appendix A); the exchange rate ("message 31994", "d0a17f358b; message 32032" → section cross-references); silence is not success ("message 31890/31886", "messages 31905–31913", "messages 31845, 31846, 31882" removed). Dropped: "Persistence" (goals #25, #38, #39; commits; messages) except its technical core — the verified pre-fire manifest of the thirteen input hashes — which is one sentence at the end of the exchange-rate paragraph, scoped to the certificate campaign of §4.2 as the v4 text was; "The human role" (goals #36, #38, #39, #40; "nothing goes external before operator review (messages 31965, 31970)"). "Scope words" (messages 31845, 31846, 31882; "the operator cancelled certificate production and replay for this paper") folded into "Silence is not success" as the axiom-list sentence; the Result A clause is carried by §4.2 L202, Table 4 and §6 ("no certificate is produced"; "none has a certificate produced by this paper"). "Why Erdős problems" dropped as motivational rather than technical (not on the operator's keep list; D9). "Methods" kept as pointers; "persistent SQLite chat" → "a persistent shared chat room (the unpublished transcript)". Intro paragraph: the transcript is stated to be unpublished and each lesson names the Lean modules and ledger files that carry it. |
| erdos85-drop.4.operator (F1, §1 contributions) | "The human operator set compute policy, research priorities, authorship, scope, and the final read-through gate" reads as governance | §7 L300 reduced to the acknowledgement the BRIEF requires: "The project's human operator, who set its priorities and scope, and its shared room infrastructure, which supplied coordination, claims, review gates and a durable transcript, are acknowledged; neither is an author." The Claude Fable / GPT Sol contribution sentences and "High-variance proposals were admitted only after independent Lean elaboration or exact certificate replay" are unchanged (transcript-true). |
| erdos85-drop.4.operator (R-AUD, applied to the whole text) | Rival hypothesis attributed to "the operator" (abstract L57; §5.3 L288) | "the operator's plane-order reading is presented as the rival" → abstract: "an unproved hypothesis with a stated rival"; §5.3: "the plane-order reading is the principal rival, under which special orders may organize both the constructions and the obstructions…". The rival's content is unchanged; only the governance attribution is removed. |
| erdos85-drop.4.operator (critical-flag `non_public_links`, R-LINK; blocker D5, L301–L322) | Artifacts and receipts named as repo-relative paths and private locators (S3 bucket, artifact volume) rather than public links | `\repobase` / `\repofile` added (preamble L36–L38). §7 rewritten: every receipt is a link at its canonical path (the `refs/` prefix and the "(files under refs/ are written as refs/)" sentence are gone; `refs/CENSUS_TIMING_20260928.md` → `CENSUS_TIMING_20260928.md`, `refs/H5_CLOSURE_LEDGER_README_20260910.md` → `q7_h5_closure_ledger/README.md`, `refs/H5_CLOSURE_REVIEWED_RESULT_20260910.md` → `q7_h5_closure_ledger/REVIEWED_RESULT.md`, `refs/h5-closure-review2065.json` → `q7_h5_closure_ledger/review2065.json`, `refs/h5-closure-reviewer-REVIEW2065.json` → `q7_h5_closure_ledger/reviewer/REVIEW2065.json`, `refs/BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt` → `sat49/BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt`, `refs/PAUSE_HANDOFF_20260927.md` → `PAUSE_HANDOFF_20260927.md`, `refs/STRATA_AND_SMALL_ORDERS_20260928.md` and `refs/H7_POSITIVE_TRIPLE_CELLS_…` → root paths, `refs/CERT_BANK_STATS_20260926.md` → root path; `AXIOM_AUDIT_COLD_20260927/` linked with its report and `axioms.out` inside it; directories `phase_b_h1_census_20260927/`, `phase_b_h1_verdict_cloud_20260921/`, `h7-closure-ledger-20260915/`, `sat49/data/` link to the directory). The preamble sentence says the links point at the branch of record and will be repointed at the release tag. The S3 URI `s3://2am-erdos85-certs/sat49/campaign-20260825/`, the volume paths `artifacts/erdos85-sat49/` and `artifacts/erdos85-sat49-MANIFEST-20260927.sha256` are removed; one sentence describes the three unpublished collections without paths or bucket names. `\url{https://github.com/rjwalters/lean-genius}` kept. |
| erdos85-drop.4.operator (major D5, L327–L344 and §3.2/§4.2 modules) | Appendix A ledger files and §3.2/§4.2 Lean modules are bare names | Linked: §3.1 `Erdos85FiniteDropWitnesses.lean`; §3.2 `Erdos85OrderFortyNineSmallHighVerifiedFrontier.lean`, `Erdos85OrderFortyNineSmallHighCubeGridTerminal.lean`; §4.1 `sat49/verify_boza48_nonisomorphism.py` and its receipt; §4.2 `PHASE_B_H5_H7_INVENTORY_20260910.md`, `q7_h5_closure_ledger/`, `Erdos85OrderFortyNineSevenHighCanonicalCensus.lean`, the T1Rep0 and T7Rep0 certificate modules, `Erdos85OrderFortyNineSevenHighCertificates.lean` (the aggregate's module, newly named), `Erdos85VertexSubsetEdgeCapacity.lean`, `Erdos85OrderFortyNineSevenHighT0ExteriorPairCapacity.lean`, `H7_CLOSURE_20260915.md` + `h7-closure-ledger-20260915/`, `cube_tree_check.py` + `tree-check.json`; Table 4 witnesses module; §4.4 `Erdos85OneHighV2CnfEmit.lean` (the `Proofs/` prefix of the old `\lean{}` dropped); §4.5 the budget plan; Appendix A `NONBIP_CONNECTED_LITERATURE_DIVERGENCE.md`, `Erdos85PartialCentralReconstruction.lean` (newly named; the module behind "a core-Lean partial common-neighbour reconstruction", per the cuts ledger row 177), `PARTIAL_CENTRAL_OPERATION_AUDIT.md`, `l6-cyclic-trace/UNIFORM.md`, `l6-representability/`, `baer-repair-gate/`, `BAER_POLARITY_EXTENSION.md`, `retained-subplane-gate/`, `mod2-root-gate/`, `CUTS_LEDGER_DRAFT.md`, `FINAL_PROOF_OUTLINE.md`, `q9_solver_controls/Q9_EXISTENCE_DECISION_20260911.md`, `cayley-census-q11-q13/CAYLEY_CENSUS_Q11_Q13_20260913.md`; Appendix B `Erdos85MuNegThreeZeroFiveCorrectOwnerCertificate.lean`. |
| erdos85-drop.4.operator / R-AUD (Appendix A pointers) | Outline-version, commit-hash, divergence and room-message pointers in the negative map | Determinant: "(outline §A.5.3(i), commit 0ed91c72d6)" → "(proof outline §A.5.3(i); cuts ledger row 1)" — the cuts ledger's row 1 is "Determinant / D-spectrum route ELIMINATED uniformly" and the outline's §A.5.3 (i) is the same item. Real spectrum: "(f6ee2ed421; divergence #66)" → "recorded in the cuts ledger"; "(outline versions v2.66–v2.69.3)" → "(proof outline §A.5.3)". Packing: "(e401f3034f; room message 31951)" → "(cuts ledger)". Inverse-sign: "(19f227dced; outline v2.62; room messages 31962–31963)" → "(cuts ledger row 56; Appendix B)" — row 56 is "Inverse-potential strict sign terminal DEAD". Variants: "banked in … at cf2243a6e8" → "recorded in (link)". Flag relaxations: "(cuts ledger rows 174–180)" → the same rows with the ledger linked (rows 174–180 verified present in `CUTS_LEDGER_DRAFT.md`). Commit hashes are dropped rather than linked because no git command was permitted to resolve the abbreviated hashes; the linked ledger files carry them. |
| erdos85-drop.4.audit (minor m1; = review minor 1) | §1 L74 "one for each of its canonical cells with a positive triple" — one per representative | "one for each of its thirteen canonical representatives with a positive triple" (§1 L81). |
| erdos85-drop.4.audit (minor m2; = review minor 2) | §4.2 L176 "complement completion for eleven of the twelve a = 7 roots" homogenizes the route; `H7_CLOSURE_20260915.md` applies 2683 "where required" (three roots) | "source enumeration, with complement completion where the ledger required it (three roots), for eleven of the twelve $a=7$ roots and a cycle-exclusion chain for the twelfth" (§4.2 L195); the ledger is now linked in the same sentence. |
| erdos85-drop.4.audit (minor m3) | "1,412 input preparations for the 1,161 residual rows over four cloud passes" (§1 L74; §7 L306) — the preparations concern the 1,137 cloud-dispatched rows | §1 L81: "1,412 input preparations over the four cloud passes for the 1,137 rows dispatched to the cloud (the 24 pilot rows ran on the local Mac; a row that reached its cap was prepared again for the next pass)"; §7 receipt entry: "the 1,412 preparation receipts for the 1,137 cloud-dispatched rows". §4.4 L233 ("of the 1,412 preparation receipts in the four cloud passes") was already exact. |
| erdos85-drop.4.audit (minor m4) | §2 L96 "compiler-generated axioms that we list" — only the witnesses' axioms are listed | "which adds compiler-generated axioms: we list them for the witnesses (Table 1) and state the dependency for the certificate checks (Section 4.2)" (§2 L107). |
| erdos85-drop.4.audit (nit n1) | Two vocabularies for one trust mechanism (`…_native.native_decide.ax_N` in Table 1 vs `Lean.ofReduceBool` for the H7 checks) | One sentence in §3.1 (L117): "Lean records each `native_decide` use as a per-declaration axiom named `…_native.native_decide.ax_N`; the six such entries in Table 1 are instances of the compiler-trust axiom `Lean.ofReduceBool`, and that single name is used below for the thirteen H7 certificate checks of Section 4.2, whose axiom lists were not printed in the cold audit." The §4.2, Table 4, §4.4 and §6 wording (`Lean.ofReduceBool`) is unchanged. |
| erdos85-drop.4.audit (nit n2) | Table 4 "over four passes" — the 1,160 rows span the pilot and cloud passes 1, 2, 3, 3b | "under declared caps over the pilot plus four cloud passes" (Table 4, H1 residual roots row). |
| erdos85-drop.4.audit (non-critical: 9 unverified + 3 partial citations; App. A `zhang2017polarity` values and Boza r(109)/r(155) bounds) | Off-disk citation verification is an author obligation | Declined — unchanged from v3/v4: no PDF of any cited work is in `refs/`, web search is off, and nothing is invented; the obligation stands for the authors before submission. |
| erdos85-drop.4.audit (non-critical: figures) | None; `paper-figures` matter | Declined for this pass (see the review D6 row). |
| erdos85-drop.4.review (generic, minor D2; L172, L176, L347) | Reviewed closures cite numbered room reviews; the paper does not say which numbers have a public snapshot | §7 L338: "The review numbers quoted for H5 and for the H7 $t=0$ cell … are the identifiers recorded in the linked ledger files, which state each review's outcome, checker and pinned hashes; the reviews themselves are entries in the unpublished transcript, so the ledger statements are what a reader can inspect." Verified: 2037 / 2032 / 2062 / 2063 / 2065 appear in `q7_h5_closure_ledger/README.md`; 1573 / 1574 / 2091 / 2718 / 2116 / 2683 / 2117 appear in `H7_CLOSURE_20260915.md`; both files are linked where the numbers are quoted (§4.2, Table 2, Table 4, §7). Under R-AUD, review numbers that only indexed the transcript (Appendix B's #939) are removed. |
| erdos85-drop.4.review (generic, minor D5; Table 4, §7 L321) | State the total size and release status of the thirteen packed LRAT files | Release status addressed: §4.2 L193 "The packed certificates reside on the project's artifact volume, which is not published, so the thirteen modules cannot be rebuilt from the public source tree alone (§7)"; Table 4 "certificates on the unpublished artifact volume"; §4.4 "read their certificates from the unpublished artifact volume"; §7 names the packed files among the unpublished collections. Size **declined**: the receipt (`H7_POSITIVE_TRIPLE_CELLS_…_20260928.md`) lists thirteen per-file byte counts but no total, and the BRIEF forbids new numbers; a summed "about 9.3 GB" would be a figure no receipt carries. |
| erdos85-drop.4.review (generic, minor D9; abstract L57) | 303-word single-paragraph abstract; negative-map sentence and the parenthetical A-REG definition belong elsewhere | Two paragraphs (Result A / Theorem B); the negative-map sentence removed (§5.3 carries it); the solver names, the "cheaper cube-partitioned route" clause and the "explicit graphs checked in Lean 4 through `native_decide`" detail cut; the A-REG parenthetical kept in compressed form because the abstract must say what A-REG is. 303 → 260 whitespace tokens (LaTeX macros counted). |
| erdos85-drop.4.review (generic, minor D7; §4.2 L174) | Ninety-word certificate sentence with five identifiers | Split into three sentences after "by `native_decide`" and after "representative" (§4.2 L193); the aggregate now also names and links its module. |
| erdos85-drop.4.review (generic, minor D7; §1 L74) | "cells" for "representatives" | Fixed (audit m1 row). |
| erdos85-drop.4.review (generic, minor D1; §4.2 L176) | "complement completion for eleven" vs "where required" | Fixed (audit m2 row). |
| erdos85-drop.4.review (generic, minor D4 `related-work`; §2 L90) | Method-lineage gap; `paper-litsearch` before publication | Declined again — web search off, no litsearch sibling, nothing may be invented; §2's scope statement stands. |
| erdos85-drop.4.review (generic, nit D7; §4.2 L174) | "a `include_str`" → "an" | Fixed ("an `include_str`"). |
| erdos85-drop.4.review (generic, nit D7; L303–L321) | `\lean{}` used for paths, S3 URIs, scripts and the case id | Resolved by R-LINK: every path, script and receipt is now a `\repofile{}` link; `\lean{}` arguments are Lean names, the `v2cnf` binary, the hypothesis `hno49`, the Lean core axioms and the case id `h1_81494a6ef36d3ec9` (an instance tag, kept in `\lean{}` as before). |
| erdos85-drop.4.review (generic, nit D6) | No figure; cube-tree diagram or solve-time histogram possible | Declined for this pass: the operator-directed scope is R-AUD / R-LINK plus the carry-overs; a figure would be a `paper-figures` step from `cube-tree-check.json` / `h1-census-table.tsv` and is left to that command. `figures/` carried over empty. |
| erdos85-drop.4.review (generic, nits: 7 underfull lines; 22 font-shape warnings; procedural) | No action needed | No action; v5 has 5 underfull lines (max 6094) and the same cosmetic `hyphenat`/Menlo warnings. |
| erdos85-drop.4.numeric (tool evidence) | 0 findings | Nothing to address. The two new arithmetic-bearing phrases (1,137 + 24 = 1,161; "three roots" of the eleven $a=7$ rows) match `CENSUS.md` / `CENSUS_TIMING_20260928.md` and `H7_CLOSURE_20260915.md`. |
| erdos85-drop.4.pending (tool evidence) | 0 markers | Nothing to address; no `[PENDING …]` marker exists in v5. |

## Hard scope rules (BRIEF) — held while cutting the governance text

Result A remains "computational evidence" / "a computational result, not an unconditional Lean
theorem" / "evidence, not a theorem" and is never called proved, decided or a theorem; nothing is
claimed about Erdős Problem 85 itself (abstract, §1, §6 unchanged); A-REG is "an unproved
hypothesis with a stated rival, not a conjecture we endorse" (§1) and "not a forecast" (abstract);
no verdict or certificate is promoted — the trust caveats on the thirteen H7 certificate modules
(`Lean.ofReduceBool`; compiled at the 2026-08-15 commits and not rebuilt in the cold audit;
certificates on the unpublished artifact volume) are kept in §4.2, Table 4, §4.4 and §6, and "no
certificate is produced" / "none has a certificate produced by this paper" / "no certificate was
replayed or produced for this paper" are kept or strengthened in Table 4, §4.2 L202 and §4.5;
every number still traces to a linked receipt (`scope_lint` PASS; no new numbers introduced —
the only new figure-like tokens are the review identifiers already present and the row numbers
of the linked cuts ledger). Authorship and the transcript-true contribution sentences are
unchanged; the human operator and the room infrastructure are acknowledged, not authors.
