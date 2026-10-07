# Comments — erdos85-drop.9

Keyed to rendered section headings, with `main.tex` line numbers in brackets. The thread is single-file, with no `\input` children.

## blocker

None.

## major

- **M1 — Abstract [L66] and Result A [L78]: "independently replayed computation" for H5 and H7 ($t=0$).**
  - Excerpts: "the others are closed by reviewed arguments with independently replayed computation (H3, H5; H7, $t=0$)" and "by reviewed arguments with independently replayed computation for H3, H5 and H7 with $t=0$".
  - "Replayed" is supported for H3 (`Q7_H3_PROFILE_EXCLUSION_20260910.md`: "independently replayed finite computations"; unchanged-source, no-deadline replays) and for nothing else.
  - The H5 receipt (`q7_h5_closure_ledger/README.md`) says "independently checked finite-computation exclusion".
  - §2.3 [L116] says one H7 $t=0$ source enumeration "rests on an audit of the enumerator code rather than an independent replay".
  - `H3_EVIDENCE_AUDIT_20261007.md`, the BRIEF `claim` and the paper's own §2.3 [L112] and Table 2 [L206, L208] all use "independently checked".
  - Fix: "reviewed arguments with independently checked computation" in both places. Optionally write "(H3, replayed; H5; H7, $t=0$)" if the extra credit to H3 is wanted. Do not change Table 2's H3 row.
- **M2 — §8 Availability [L257]: the linked receipt `STRATA_AND_SMALL_ORDERS_20260928.md` contradicts the paper.**
  - (a) The copy on `origin/erdos85/integration`, which is the `\repobase` target, still reads "checked LRAT proofs for both cells (`PHASE_B_H1_H3_INVENTORY_20260910.md`, `Q7_H1_H3_SQUEEZE_20260910.md`)". The in-place correction is committed only on `origin/erdos85/paper-v6` (`13400a4c890`).
  - (b) Both copies keep the H1 row "1,257 rows = 96 certificate-verified + 1,161 two-solver UNSAT; the row-to-stratum assembly is an open formal obligation". That contradicts §2.4 ("So, in Lean, H1 reduces to 13,351 SAT questions") and Table 2 ("H1 reduction ... nothing").
  - The paper links this file as the source of "the strata and small-order names", and §1 says "every number traces to a linked receipt", so a reader who follows the link meets superseded claims.
  - Fix outside `main.tex`: update the H1 row, or add a dated "superseded by the paper / H1_COVER_AXIOMS" banner, and merge paper-v6 into integration before the release tag. Alternatively, link the Lean names to the modules directly and drop this receipt from §8.

## minor

- **m1 — §3 opening [L137]: antecedent of "Both works".**
  - Excerpt: "Both works reduce the mathematical statement, in Lean, to the unsatisfiability of a formula defined in Lean".
  - The preceding sentences describe two papers, `heule2024hexagon` and `subercaseaux2024hexagonlean`. The first has no Lean component, so the literal reading misattributes a Lean reduction to it.
  - Fix: "The hexagon verification and ours both reduce ...". This is a one-phrase edit, and the next sentence ("On this axis we claim no advantage") already supplies the intended contrast.
- **m2 — Table 2 caption [L195] vs. the "Case split" and "H3" rows [L202, L205].**
  - Excerpt: "axiom lists are those printed by \texttt{\#print axioms}".
  - Neither `not_c4FreeMinDegreeWitness_fortyNine_seven_of_strata` nor `threeHighCanonicalGraphCover_all` appears in `AXIOM_AUDIT_COLD_20260927/axioms.lean`/`axioms.out`, and the rows give no axiom list. That is not wrong, but a reader may assume these rows were audited.
  - Fix: add "(not in the cold audit)" to those cells, or print their axioms into a linked receipt as was done for the H1 cover. `Erdos85OrderFortyNineThreeHighOneFiber.lean` has 0 direct `native_decide` uses.
- **m3 — §4 post-table [L214]: "H3 could instead be closed by a certificate for each of its two cell formulas, but neither has been produced."**
  - This is accurate. Per `H3_EVIDENCE_AUDIT_20261007.md`, the cell formulas were materialized but never run, and the four alternative scout CNFs ended `s UNKNOWN` after about 12 h of Kissat.
  - Optional: add "and whether they are within reach is untested", so the sentence does not read as a routine remaining step.

## nit

- **n5 — Title [L56] (R-TITLE, operator decision; resolved).** "A Drop at Forty-Nine in Erdős Problem 85" does not overclaim: it asserts only the drop, with no "certificate-checked", "theorem" or "proof", and nothing about the answer. It replaced the v8/v9 title mid-review. Optional: align the §2 heading "The drop at 48 to 49" [L89] with the title's wording. `main.pdf` predates the title edit and must be rebuilt.

- **n1 — §7 Contributions [L244]: "the existence halves of the census".** Carried from v8 n3. The phrase is still opaque, and no receipt defines it. Left for the authors.
- **n2 — refs.bib.** No DOI for `tan2021cakelpr` or `heule2018schur`. `biere2020cadical` describes a 2020 release, not 3.0.1. Carried from the v8 audit (N4/N5); add DOIs only through the resolver.
- **n3 — §3.1 [L144] cake_lpr "commit `a36874a8`" vs. the "`d23c413b…`" build named in §3.2/§3.3.** Carried from v8 audit N3. A reader cannot tell which binary the commit names. Declined in v9 for lack of a receipt; the reasoning is acceptable.
- **n4 — §2.3 H3 [L110]: "H3 is excluded by a reviewed paper argument".** Consider "H3 is excluded, outside Lean, by a reviewed paper argument", to mirror the H7 $t=0$ paragraph's "the closure itself is not [a Lean theorem]". This is optional, since the preceding sentence already says the exclusions are undischarged in Lean.

## Procedural notes

- sidecar: staged and committed through `python -m anvil.lib.sidecar stage/commit` (issue #645 CLI shim), invoked as `PYTHONPATH=.anvil python3 -m ...` rather than `uv run`. The Stripe volume was accessed unsandboxed.
- numeric-consistency: automated (`anvil.lib.numeric_consistency`), 328 numbers, 0 findings; sidecar `erdos85-drop.9.numeric/`.
- pending-marker: automated, 0 markers; sidecar `erdos85-drop.9.pending/`.
- audience-check: automated. 0 governance and 0 private-locator hits. The 6 `unlinked_artifact_path` hits (§8, L254–L259) are `\repofile` arguments, so they are false positives, unchanged since v7. Sidecar `erdos85-drop.9.audience/`.
- render-gate: pass (12 pages, 0 overfull, 0 placeholders), using `erdos85-drop.9/compile-log.txt` because `paper-audit` has not yet run on v9; see `_gate.json`.
- evidence-check: `anvil.lib.evidence_check` on the staged `scoring.md` returned 9 dimensions, 0 findings, pass.
- evidence-drift: EVIDENCE-DRIFT on `BRIEF.md` (R-H3 amendment), re-weighed in `verdict.md`.
