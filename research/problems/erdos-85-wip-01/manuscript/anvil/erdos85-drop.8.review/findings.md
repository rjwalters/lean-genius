# Findings — erdos85-drop.8

Cross-section observations. The rubric is the same as in the prior iteration (`anvil-pub-v2` both times), so this review has no rubric-transition subsection.

## 1. The four review questions

### Q1. Is the v7 critical flag (close prior work) resolved?

**Yes.**

- `heule2024hexagon` and `subercaseaux2024hexagonlean` are cited in §3 with `\citet` and pointed to from §1. They resolve in `refs.bib` with DOIs.
- The paragraph credits the precedent as the closest one. It says theirs is stronger on encoding faithfulness, and it limits the new contribution to specific, checkable items: scale inside a whole-stratum reduction, hash-only check-then-discard, bank re-validation, and a public checker.
- The general lineage is credited too. Heule's Pythagorean and Schur results "check proofs too large to keep" [L136], so streaming and discarding is not presented as new. What is presented as new is the hash receipts and byte-identical regeneration.
- No novelty is overclaimed.

The one residual issue is M1 (major, non-blocking). The comparison sets their *encoding proof* against our *file-to-formula link*, although H1's encoding-to-stratum link is itself a Lean theorem, with `native_decide`. The fairness runs against this paper. The paper does not overstate.

### Q2. Do the scope rules (critical) hold?

**All hold.**

| Rule | Status | Evidence |
|---|---|---|
| Result A never theorem/proof/decided | held | `resultA` environment; "Result A is not a theorem of Lean" (§1); "The result is not a Lean theorem" (Abstract); scope_lint banned patterns PASS. "established ... at this level of evidence" stays epistemic |
| "Formally verified checker" only for H1 | held | Used for cake_lpr on H1 and once for the cited precedent. H3: "checked LRAT proofs", checker not recorded. H7 t>=1: "certificates checked inside Lean". H5 and H7 t=0: reviewed |
| cake_lpr outside Lean | held | "a HOL4 theorem about its compiled binary, not a Lean kernel check" (§3.4); Table 1 caption; Table 2 "outside Lean" |
| Both H1 open items wherever status is summarized | held | Abstract [L67], §1 [L88], §3.4 [L188], Table 2 H1-orbits row (i)/(ii) naming `v2cnf`, post-table paragraph [L215] |
| H1 cover theorem axioms | held | 3 standard + 23 native_decide, no sorryAx [L130], matching `H1_COVER_AXIOMS_20261006.txt` (23 counted). Receipt linked in §2.4 and §8. Table 2 row: "nothing; not standard-axiom-only" |
| `LRAT.check` at most once | held | One mention, §3.2 [L176], "not part of the argument" (citation gap: m1) |
| Nothing claimed about Erdős 85 | held | "one drop is compatible with either answer to the problem" |
| A-REG a hypothesis with a rival | held | "a hypothesis with a stated rival"; plane-order rival in §5 |
| R-AUD | held | Audience pre-flight: 0 governance, 0 private-locator hits. Manual read clean. "$225" is a cost fact. Walters credit is neutral |
| R-LINK | held | 49/49 `\repofile` targets exist. 9 are on `erdos85/paper-v6` pending merge (CHECKING.md, h1_checker_kit/, the bank-check dir and 3 receipts, historical96_cake_lpr_receipts.jsonl, COMPOSITION_AXIOMS, H1_COVER_AXIOMS), which is not a defect. The room URL is linked, per R-BRIDGE. No bucket name appears in the paper. "Not published" correctly excludes the bank |
| Authorship amendment | held | Order, joint Sol/Astra sentence, seat-change sentence, Opus credit, room acknowledged |

### Q3. Do the numbers match the receipts?

**All numbers trace.** I recomputed them from `refs/`; the detail is in `verdict.md`.

- 13,351 = 12,094 + 1,160 + 96 + 1, with the four sets disjoint and their union exact.
- cake_lpr covers all four sets (historical: 96/96 `CAKE_LPR_VERIFIED`, checker `d23c413b`).
- 96 historical: 0.103 TB.
- Bank: 22.55 TB.
- Total: 28.35 TB, which the paper gives as "about 28 TB".
- Cost: $224.42, which the paper gives as "about $225", scoped to the census plus the bank.
- Abstract: 1,767 rendered characters, under 1,920.

Four claims were checked more deeply:

- **Historical CNF check.** `replay_historical96.py` rejects any archived CNF whose sha256 is not the census-manifest hash, which supports "against the CNF with the expected hash".
- **Identical conversions.** 0 of 96 historical LRAT hashes differ from the earlier pass.
- **Census hosts.** The TSV `instance_type` tally is 1,157 Graviton + 3 Mac.
- **Heap sizes.** The TSV `heap_mb` tally is 1,075 at 4 GB, 72 at 8 GB, 12 at 16 GB and 1 at 12 GB.

The numeric detector reports 0 findings over 312 numbers, and scope_lint passes with 34 numbers and 39 Lean names.

### Q4. Does the paper keep R-SIMPLE's balance?

**Yes.**

- **Length.** The main text is 10 pages, and references begin on p. 11. There are no appendices and one status table.
- **No buried lede.** The abstract leads with the drop, then the H1 reduction, then the uniform cake_lpr check at 28 TB. §1 states both results within the first page, followed by "What is new" and "What is not claimed".
- **No overclaiming.** Caveats mark the boundaries without occupying the centre. The only place a cold reader could over-read is the operator-fixed title "A Certificate-Checked Drop", since H5 and H7 t=0 have no certificates. The abstract corrects this two sentences later (m2).
- **No underclaiming.** The H1 reduction is now presented as audited, and the method is presented as a contribution with a public checker. The only underclaim is M1's comparison sentence.

## 2. v7 items in v8

| v7 item | v8 status |
|---|---|
| Flag close_prior_work_ignored | resolved |
| M1 cover theorem "not in the cold axiom audit" | resolved (axioms stated and linked; row reads "nothing") |
| M2 post-table paragraph named one H1 item | resolved (both items, plus why both are needed) |
| M3 "formally verified checker" over 50 LRAT.check orbits | resolved by evidence (96/96 historical orbits cake_lpr) |
| M4 Lean/Mathlib uncited | resolved |
| m1 H3 checker | resolved as far as the receipts allow (I confirmed STRATA/PHASE_B/Q7 do not name one) |
| m2 "none ... is a search problem" | resolved |
| m3 abstract gap sentence | resolved |
| m4 abstract length | resolved (1,767 characters) |
| m5 historical row size | resolved |
| m6 "roughly ten times" | resolved (dropped) |
| m7 q=4 analogue | resolved (`sixteenRegular` names exist in Erdos85Problem.lean) |

## 3. Residual risk for publication

- **Precedent comparison (M1).** This is the one sentence a formal-methods referee will read closely. Getting it exactly right helps the paper, since it currently undersells its own Lean-verified reduction.
- **Public-checker wording (m4).** For the historical and macOS rows, the hash comparison with "ours" is not possible. CHECKING.md already says so, and the paper should match it.
- **Branch merge.** 9 linked targets exist only on `erdos85/paper-v6`. `\repobase` points at `erdos85/integration`, so the links are dead until the merge, or until `\repobase` is switched to the release tag at publication.
