# Verdict — erdos85-drop.6

**Total: 34 / 44** (prior iteration `erdos85-drop.5.review/`: 38 / 44)

**Decision: `advance: false`**. One blocking critical flag is raised, and the total is also below 35. The pending-marker gate passed (no `[PENDING …]` marker), so the only things holding the thread are the flag and the score. Iteration 6 of `max_iterations: 6`, run as an operator override, so another revise pass needs the operator's decision.

## Critical flags

### 1. `scope_overclaim_h1_certificate_check`: "every H1 instance" omits the 2026-08 certificate bank that closes most of H1

The headline new claim says H1 *is* the 1,257 Phase B rows and that every one of them, and so "the whole stratum", has been checked by a formally verified checker:

- Abstract [L68]: "The fourth, the one-high stratum H1, consists of 1,257 SAT instances, and every one of them now has an unsatisfiability proof accepted, outside Lean, by a formally verified checker".
- §4.5 [L268]: "Every H1 instance now carries a checked certificate".
- §4.4 [L264]: "for H1 they are no longer in the trust base".
- §6 [L344]: "the whole stratum was certificate-checked in one run, and the solvers left the H1 trust base".
- Table 5 [L288]: "All of H1 & 1,257".

The receipts say something narrower. `H1_CERT_RECEIPTS_README_20261006.md` says "Every H1 residual root is now certificate-checked". `PHASE_B_H1_H3_INVENTORY_20260910.md` defines the 1,257 frozen tags as "the capacity universe [13,351 rows] minus 11,954 previously screened rows whose positive-size objects are still present, minus 140 additional rows with fresh producer-success ledgers" and adds: "This is producer screening; uploaded certificates were not downloaded or kernel-checked in this pass." `H1_REPLAY_SPOT_16_BUDGET_PLAN_20260916.md` states that "the full 13,351-slot closure" needs both the "12,019 historical ready" bank certificates and the 1,288 gaps. The paper keeps that framing in §4.2 [L232] ("the capacity-grid snapshot of 13,351 slots with 1,288 certificate gaps").

So about 12,000 H1 instances rest on 2026-08 certificates. Their only check was producer-side drat-trim at production time, recorded in ledgers. They were never re-validated payload by payload, and the October run checked none of them. The paper itself treats exactly that evidence class as insufficient, because it re-checked the 96 "historical" rows that carry the same 2026-08 drat-trim verification.

v5 disclosed the gap ("The bank of 12,019 historical ready certificate inputs for the H1 rows is inventoried (objects and metadata, not yet validated payload by payload)", v5 §6, plus a Table 4 row). v6 deleted both as "obsolete" and calls the bank replay plan "superseded" (§7 [L362]). The October run did not supersede it, because it never touched the bank.

In addition, `PAUSE_HANDOFF_20260927.md` says the capacity-grid framing "additionally needs the 34 outside-frozen slots". These are verdict-only, and the paper never says whether the H1 exclusion depends on them.

A reader who compares §4.2's 13,351-slot grid with the abstract's "every one of them" would stop here. This is a disclosure weakened relative to the AUDITED v5, and it breaks R-CERT's rule to "name the remaining gaps every time the status is summarized." It also makes the BRIEF frontmatter claim ("Every SAT instance behind the 48-to-49 drop now has an unsatisfiability certificate accepted by a formally verified checker") unsupported by the receipts. The operator should know that the BRIEF claim itself overstates the receipts.

**Fix (no new numbers needed).**
- State that H1's closure runs over the 13,351-slot capacity universe.
- State that the October check covered the 1,257-row Phase B set (1,161 residual roots plus 96 historical).
- State that the remaining ~12,000 slots rest on the 2026-08 certificate bank, verified at production by drat-trim (unverified) and not re-validated or checked by a verified checker. The 12,019 / 11,954 / 140 counts are all receipted.
- Add "re-validating the 2026-08 bank" to every status summary's gap list.
- Restore the Table 4 bank row.
- Say whether the 34 outside slots are needed.
- Rephrase "H1 consists of 1,257", "every H1 instance", "the whole stratum" and "left the H1 trust base" to "the Phase B residual of H1".

The alternative is to run the bank through drat-trim → cake_lpr. That is an operator decision, and it would need new receipts.

## Re-evaluation of the three critical flags in `erdos85-drop.5.operator/`

- **`brief_amendment` (R-CERT reframing): resolved in form, but the reframing caused flag 1 above.**
  - The title is the BRIEF title.
  - The abstract, §1, the Result A statement, Table 2, Table 4, §4.2, §4.4, the new §4.5 "Certifying H1 (October 2026)" with Table 5, the new §4.6 "Why the whole-instance route sufficed", the §6 heading (no "price of certainty") and the "In sum" close all tell the certified-computation story.
  - "We chose to stop at belief" is gone, and the unrun replay pricing is retired.
  - cake_lpr is introduced as CakeML-verified and outside Lean ("cake_lpr is a verified checker, but it is not the Lean kernel"). All five R-CERT gaps are named in the abstract, §1, §4 opening, §4.3 and §6.
  - The 34 outside slots are kept out of the 1,257.
  - Authorship and contributions follow the 2026-10-06 amendment, including the seat sentence.
  - The bank omission is the one place where the reframing went too far.
- **`operator_defect` (a), `Lean.ofReduceBool` in §3.1: resolved.** §3.1 [L119] now says the audit output "never prints the name `Lean.ofReduceBool`". Reading the per-declaration axioms that way "is a statement about how Lean implements native_decide, not a line of the audit output". This matches `refs/axioms.out`, which prints only `…_native.native_decide.ax_N`.
- **`operator_defect` (b), Appendix B hashes and abstract `native_decide`: resolved.** Appendix B [L409] now reads "thirteen base-input hashes (the four H3 scouts, three H5 cells and six H7 $t=0$ cubes of the host manifest above, not the thirteen H7 certificate modules…)" (4+3+6 = 13). The abstract says "checked in Lean 4 through `native_decide`" and lists `native_decide` among the gaps.

## The original scope rules: held

- Result A is never called a theorem, proof or decided value. The word "theorem" appears 47 times; each Result A use is negated.
- No external check is promoted to a kernel check.
- Nothing is claimed about Erdős 85.
- A-REG is "an unproved hypothesis with a stated rival".
- R-AUD: grep finds 0 hits for authoriz, goal, ticket, board, message, s3://, Stripe, refs/ or ceiling. The 3 "operator" hits are the defect operator and `\operatorname`. The 6 "budget" hits are a single file name.
- `audience_check`: 0 governance and 0 private-locator hits. Its 14 `unlinked_artifact_path` hits (L357–L370) are false positives, because every flagged path is inside `\repofile`, which the detector does not expand.
- R-LINK: 71 distinct `\repofile` paths. 70 exist on `origin/erdos85/integration`. The 71st, `h1_cert_pilot_20261001/COMPOSITION_AXIOMS_20261006.txt`, is on `erdos85/paper-v6` (HEAD) and lands with the merge, so it is not a defect.
- The README link and the transcript URL return HTTP 200.

## Dimension summary

| # | Dimension | Weight | v5 | v6 |
|---|---|---|---|---|
| 1 | Rigor of method / argument | 6 | 6 | 5 |
| 2 | Evidence sufficiency | 6 | 5 | 4 |
| 3 | Clarity of contribution | 5 | 5 | 4 |
| 4 | Related-work positioning | 5 | 3 | 4 |
| 5 | Reproducibility | 5 | 4 | 4 |
| 6 | Figure & table quality | 4 | 3 | 3 |
| 7 | Prose & structural quality | 4 | 4 | 3 |
| 8 | Citation hygiene | 5 | 5 | 4 |
| 9 | Rhetorical economy | 4 | 3 | 3 |
| | **Total** | **44** | **38** | **34** |

Full justifications are in `scoring.md`. Line-level items are in `comments.md` (1 blocker, 3 major, 7 minor, 4 nit). Cross-section verification, the receipt recomputation and the checker-trust analysis are in `findings.md`.

## Top 3 revision priorities

1. **Fix the H1 scope (flag 1).** Restore the 2026-08 bank disclosure. Rephrase every "H1 consists of / every H1 instance / whole stratum / left the trust base" sentence to the Phase B residual. Add bank re-validation, and the 34 outside slots if they are needed, to the gap list wherever status is summarized. Restore the Table 4 bank row. The operator should also amend the BRIEF frontmatter claim, or decide to run the bank through a verified checker.
2. **Qualify the compiled `LRAT.check` once, where the reader meets it.** In §4.5 or Table 5, name `lratreplay`, state that `LRAT.check`'s algorithm is proved sound in Lean (`Std.Tactic.BVDecide.LRAT.check_sound`) while compiled execution and the DIMACS/LRAT parsing in the front end are trusted, and note that this is the same compiler trust as the H7 `native_decide` checks. For the 30 leaves also accepted by cake_lpr, say that `LRAT.check` is redundant rather than part of the trust base (§4.4 currently says the opposite).
3. **Make the hardest-row and Table 5 statements match their receipts.** The leaves were solved with a macOS CaDiCaL build and checked from files by a cake_lpr binary the paper does not identify. The six largest leaves have no proof sha256. Replace "checked the same way", correct the Table 5 caption, and hedge the §4.6 "splitting would have multiplied the bytes" counterfactual.

## Judgments requested by the dispatcher

**Item 3: is it accurate to call Lean's compiled standard-library `LRAT.check` part of "a formally verified checker"?** It is accurate in the body and slightly loose in the abstract. It is not a flag.
- `Std.Tactic.BVDecide.LRAT.check_sound` exists in the pinned v4.31.0 toolchain, so "whose soundness is a Lean theorem but whose execution trusts the compiler" (§4.4) is true. That is the standard `bv_decide` trust model.
- What the paper leaves out:
  - The checks ran through the project's `lratreplay` executable (`Proofs.Erdos85LratRuntime`), whose DIMACS and LRAT parsing is unverified. cake_lpr's end-to-end theorem does cover parsing.
  - For the 50 historical certificates checked only by `LRAT.check`, the trust is therefore the same as for the H7 `native_decide` LRAT checks, minus the Lean statement.
  - §4.4's claim that trust sits in `LRAT.check` "for … 30 of the 36 cube leaves" is wrong in direction. Those 30 were also accepted by cake_lpr, so `LRAT.check` adds redundancy there, not trust.
- The abstract's "formally verified checker: … 96 earlier certificates by cake_lpr or Lean's compiled LRAT checker" is defensible but should carry a short qualifier (priority 2).

**Item 3: is the "certificate-checked" framing in the title and abstract consistent with the stated limits?** The abstract does not bury the lede, and on everything except H1's extent it does not overclaim. It says "certificate-checked computational evidence", names all five gaps and says "not a theorem". The overclaim is flag 1, which concerns the extent of H1, not the checker. The title "A Certificate-Checked Drop" is set by the BRIEF and is a minor stretch, because H5 and the H7 $t=0$ cell rest on reviewed arguments with no certificates. The Result A statement ("certificate-checked computation and reviewed arguments together support") is the accurate form. This is recorded as a minor for the operator, not a flag.

**Item 4: are the three `.5.operator` flags resolved?** Yes, all three are resolved in the text (see above). The R-CERT reframing created flag 1.

## Procedural

- Render gate: pass (`_gate.json`: 23 pages, 0 overfull boxes above 5 pt, 0 placeholders); `pdftotext` shows 0 `??`.
- Numeric consistency: 935 numbers, 1 claim, 0 findings (`erdos85-drop.6.numeric/`).
- Pending markers: 0 (`erdos85-drop.6.pending/`).
- Audience check: advisory; 0 governance and 0 private-locator hits; 14 false-positive unlinked-path hits on `\repofile` lines (`erdos85-drop.6.audience/`).
- Evidence drift: `CLEAN`.
- `scope_lint.py --proofs <certpilot>/proofs/Proofs`: PASS (58 numbers, 57 Lean names).
- Quoted-evidence self-check (`anvil.lib.evidence_check`) on the staged `scoring.md`: 9 dimensions, 0 findings.
- Receipt recomputation was done in Python from the `refs/` copies and the public pilot receipts. I also checked the five leaves whose receipts lack `cube_sha_ok` against the unpublished tree `results.json`: all 36 cube hashes match.
- No solver, Lean build, AWS or git-write command was run. v6, `BRIEF.md` and `refs/` were not modified.
- No venue overlay, corpus tier, subject tier or `artifact_verify` block is declared.
