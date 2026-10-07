# Comments — erdos85-drop.8

Comments are keyed to rendered section headings, with `main.tex` source lines in brackets. Severity counts: 0 blocker, 1 major, 5 minor, 6 nit.

The v8 review passes (39/44, no critical flag, `advance: true`). None of the items below blocks. This is iteration 8 of `max_iterations: 8`, so they are inputs to `paper-audit` or to an operator-directed polish pass, not to another revise cycle under the current cap.

## Major

**M1. §3 opening, the empty-hexagon comparison sets two different links against each other.** `related-work`
- Excerpt: "On encoding faithfulness their result is stronger than ours: their encoding is proved correct in Lean, whereas we connect each checked CNF file to its Lean formula only through a compiled Lean emitter" [L138].
- Problem: the sentence sets *their encoding-correctness proof* against *our file-to-formula link*. The paper itself proves the encoding-to-stratum link for H1 in Lean. `orderFortyNineStratumExcluded_one_of_capacityInventory_checked`, with 23 `native_decide` axioms, makes `OneHighFamilyV2CheckedUnsat` of the Lean term sufficient, and §3.4 says "the Lean reduction of Section 2.4 answers it for the Lean term" [L188]. A formal-methods reader can take [L138] to mean our encoding is not verified in Lean, which undersells the paper and conflicts with §3.4. The comparison also implies their pipeline has no compiled-code step between the Lean formula and the checked DIMACS file. That is reviewer recall only (web search is off): I believe their CNF is also emitted by executing Lean code, and the reviser declined to make finer claims about their pipeline (changelog, scope tension 2).
- Fix: say where theirs is stronger on the same axis. For example: "Both reduce the mathematical statement to a Lean-defined formula; theirs does so without `native_decide`[if true] and [state how their DIMACS file is tied to the Lean formula, if the litsearch notes support it], whereas our reduction uses 23 `native_decide` axioms and ties each checked file to its Lean formula only through a compiled emitter." If the precedent's file link cannot be confirmed from the cited paper, keep "their encoding is proved correct in Lean" but add "as is ours for H1, with `native_decide` (Section 2.4)" so the contrast falls on the file link and the `native_decide` dependence. Confirm the precedent details by re-running `paper-litsearch` on `subercaseaux2024hexagonlean`. Do not add citations by hand.

## Minor

**m1. §3.2 "The historical certificates": Lean's `LRAT.check` is referenced but not cited.**
- Excerpt: "in which 50 of them had also been accepted by the compiled \lratcheck{} of Lean's standard library" [L176].
- R-SIMPLE (e): "cite the Lean LRAT checker if referenced". R-V8 §1: "mention at most once, or drop it". It is mentioned once, but with no citation. Now that cake_lpr covers all 96 historical orbits, the simplest fix is to drop the clause. The cross-check is "not part of the argument". Otherwise, resolve a citation for Lean's LRAT checker (`bv_decide`/LeanSAT) through `paper-litsearch`.

**m2. Title and abstract: "certificate-checked" covers strata with no certificates.**
- Excerpt: "First, $f(48)=8$ and $f(49)=7$, a strict drop between adjacent orders, as a certificate-checked computational result." [L67].
- H5 has "No SAT certificate is involved" [L113], and H7 $t=0$ is a reviewed closure ledger. The abstract qualifies this two sentences later, and the title is fixed by BRIEF R-CERT, so this is not a scope violation. A cold reader of the title alone still over-reads it. Consider "a certificate-checked computational result for its largest stratum" or "a computational result, certificate-checked where it is largest". Alternatively, put the reviewed-argument strata in the same sentence. Changing the title is an operator decision.

**m3. Abstract: the small-strata sentence maps three methods onto "three strata" imprecisely.**
- Excerpt: "The other three strata are closed by checked LRAT proofs, by certificates checked inside Lean, and by reviewed arguments with independently checked computation." [L67].
- H7 is split: $t\ge1$ by certificates in Lean, $t=0$ by a reviewed ledger. "Checked LRAT proofs" for H3 has no named checker, and §2.3 says "for H3 we rely equally on the independent argument" [L111]. A parenthetical would make the mapping exact within the character budget, which currently has about 150 characters of room: "(H3; H7 with $t\ge1$; H5 and H7 with $t=0$)".

**m4. §8 "Checking H1 yourself": the comparison for historical orbits is not possible as written.**
- Excerpt: "re-solves a census or historical orbit with the pinned CaDiCaL and compares the proof's sha256 with ours" [L262].
- The 96 historical receipts hash drat-trim LRAT converted from archived Kissat DRAT (`historical96_cake_lpr_receipts.jsonl`, `lrat_sha256`). No CaDiCaL proof hash of ours exists for them to compare against. The same is true for the 3 macOS census rows, which CHECKING.md reports as "PASS (proof differs …)". The re-solve is still a valid independent cake_lpr check of the same formula. Fix: "re-solves a census or historical orbit with the pinned CaDiCaL and checks the fresh proof with \cakelpr{} (for census orbits solved on Linux, the proof's sha256 also matches ours)". By the same logic, §3.4's "repeat any part of the H1 check" is right about the formula but not about the archived historical proofs, which are not published.

**m5. `refs.bib`: `heule2024hexagon` lacks its volume.**
- The entry has `series = {Lecture Notes in Computer Science}` but no `volume`. The other LNCS entries (`tan2021cakelpr` 12652, `moura2021lean4` 12699) carry one. Add the volume through `paper-litsearch` or `cite.resolve()` from the DOI `10.1007/978-3-031-57246-3_5`. Do not type it by hand.

## Nit

**n1. §3.2 "The fresh census": "the solver's own 24-hour limit on the longest orbit" [L174].** The census README says this was CaDiCaL's `-t` cap as configured by the pipeline, so it was a chosen setting, not a solver default. Suggest "a 24-hour solver time cap on the longest orbit".

**n2. §3.4 "What the check establishes": a cost sentence in the trust paragraph.** "The census and the bank re-check cost about \$225 of cloud compute in total." [L188] sits between the trust argument and the public-checker sentence. It reads better in §3.2 or §8. The figure traces to $204 + $20.42 = $224.42.

**n3. §7 "Contributions": "the existence halves of the census" [L245] is opaque to a reader.** If it means the lower-side witness graphs, say so.

**n4. Build: the final xelatex pass in `compile-log.txt` still prints "Label(s) may have changed. Rerun to get cross-references right."** A scratch rebuild (xelatex, bibtex, then xelatex ×4) reaches the fixpoint on pass 3. The text layer is identical to the shipped PDF, so no reference is wrong. `paper-audit`'s convergence-loop compile will settle it.

**n5. `erdos85-drop.8.audience/`: 6 `unlinked_artifact_path` hits in §8 [L255–L260], all false positives.** Every flagged path sits inside `\repofile`, which the detector does not expand. There are 0 governance-vocabulary hits and 0 private-locator hits. No deduction.

**n6. Procedural.** Deterministic gates this pass:
- render gate: PASS (12 pages, 0 overfull boxes, 0 placeholders); `_gate.json` written;
- numeric consistency: PASS (312 numbers, 0 findings);
- pending marker: PASS (0 markers);
- evidence_check on `scoring.md`: PASS (9/9, 0 findings);
- `scope_lint.py --refs erdos85-drop/refs --proofs <certpilot>/proofs/Proofs`: PASS (34 numbers, 39 Lean names);
- evidence drift: EVIDENCE-DRIFT, advisory only (BRIEF.md frontmatter `claim` updated 2026-10-07 after v8 was written; refs unchanged; the new claim matches v8);
- venue overlay: none (`.anvil.json` declares no `venue`);
- corpus and subject tiers: inactive;
- `artifact_verify`: not declared.

Tools were run via `PYTHONPATH=.anvil python3 -m anvil.lib.<module>`. The sidecar was written with the `python -m anvil.lib.sidecar stage/commit` CLI shim. `/Volumes/Stripe` was accessed unsandboxed because of intermittent sandbox EPERM. Nothing outside the v8 critic siblings was modified.
