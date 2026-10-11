# Comments — erdos85-drop.10

Keyed to rendered section headings, with `main.tex` line numbers in brackets. The thread is single-file, with no `\input` children. Lean and path checks were run against the pinned commit `1d0772cd825462f5230f224c2110231c6483d5e4`.

## blocker

None.

## major

- **M1 — §4 post-table [L232], §1 "What is not claimed" [L87], Table 2 row "H7, $t\ge1$" [L223]: the headline Lean theorem cannot be compiled from the published snapshot, and the paper's "complete list" omits this.**
  - Excerpts: "The packed certificate files they read are not included in the repository" (§2.3 [L121]); "The right-hand column is the complete list of what separates Result A from a Lean theorem: admitting the H1 and H7 checks into Lean, a kernel link ..., and, for a fully independent audit, a cold rebuild of every module" (§4 [L232]).
  - At the pinned commit, the 13 modules `Erdos85OrderFortyNineSevenHighT1Rep0Certificate.lean` … `T7Rep0Certificate.lean` each contain `include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/strata-lrat/h7_t*_rep*.packed.lz4p7"`. That is an absolute path on a private volume. `Erdos85OrderFortyNineCapstoneH3` imports these modules through the capstone, so `lake build` of the stated theorem fails on any other machine. (The 18 $h=9$ certificates are in `proofs/Proofs/Certificates/` and are fine.)
  - The paper discloses the fact but not its consequence. A reader is told the upper side "is a single Lean theorem" (§1 [L85]) and that a cold rebuild would only "still list the `native_decide` axioms" (§4 [L232]). That is true only on the producing host.
  - Fix (one line): add "and publication of the 13 packed H7 ($t\ge1$) certificate files, which the capstone reads by absolute path, without which it cannot be recompiled from the public repository" to the post-table list and to "What is not claimed". Better: publish the files (repo or Zenodo) and repoint `include_str` before the tag.

- **M2 — §8 Availability [L277]: the linked receipt `STRATA_AND_SMALL_ORDERS_20260928.md` contradicts v10 for H3, H5 and H7.** (v9 M2, partly fixed and now stale again.)
  - At the pinned commit, the H1 and H3 rows carry 2026-10-07 correction notes, but:
    - the H5 row still gives the evidence as "reviewed paper/computation cover";
    - the H7 row says "the Lean capstone `orderFortyNineStratumExcluded_seven_of_emptyCubeEvidenceVectors` ... is not instantiated";
    - the H3 row describes the exclusions as reviewed Python searches with no Lean discharge.
  - v10 says H3 and H5 are excluded in Lean and H7 ($t=0$) reduces to `orderFortyNineStratumExcluded_seven_of_structuralHsbEvidence`. The paper links this file as the source of "the strata and small-order names", and §1 promises "every number traces to a linked receipt".
  - Fix (one line): add a dated "superseded for H3/H5/H7 by `order49_h3_closed_capstone_20261008/README.md` and `release_assembly_20261011/README.md`" banner to the file on the release branch, or drop it from §8 and cite the capstone README for the names.

- **M3 — Abstract [L66], §1 [L85, L87] vs. `erdos85-drop/BRIEF.md`: the BRIEF was not amended for v10, and its hard scope rule conflicts with the new wording.**
  - BRIEF hard rule (critical if violated): "Never call Result A a theorem, proof, or 'decided'". BRIEF frontmatter `claim`: "not a Lean theorem, because ... the H3 and H5 premises and the H7 t = 0 capstone are open in Lean".
  - v10: "The result is a Lean theorem conditional on two explicit unsatisfiability hypotheses" (Abstract [L66]); "Result A is not an unconditional theorem of Lean" (§1 [L87]).
  - v10's substance is accurate: the conditional statement exists in Lean, and both hypotheses are stated wherever it is mentioned. I therefore raise no critical flag, on the dispatch's stated standard: conditional on two explicit UNSAT hypotheses, never unconditional.
  - But the only authority for the change is `erdos85-drop.9.operator/`, an agent-transcribed instruction. Its agreed wording was "Lean-verified reduction conditional on explicitly stated UNSAT evidence, externally checked by cake_lpr", not "the result is a Lean theorem". An auditor reading the BRIEF will flag the abstract sentence.
  - Fix (one line), either:
    - (a) the operator adds an R-V10 BRIEF amendment that updates `claim` and replaces the hard rule with "never call Result A an unconditional Lean theorem"; or
    - (b) reword the abstract sentence to "Lean derives the upper side from two explicit unsatisfiability hypotheses, $h_{\mathrm{H1}}$ and $h_{\mathrm{H7}}$, which the external checks support but which are not admitted into Lean."
  - (b) also removes the only spot where a skimmer could stop reading at "The result is a Lean theorem".

## minor

- **m1 — Abstract [L66]: "Lean splits ... into four strata, excludes H3 and H5".** §2.2 [L97] has $h\in\{1,3,5,7,9\}$, with $h=9$ refuted in Lean. Fix: "into five strata by the number of degree-8 vertices, refutes H9 and excludes H3 and H5, and reduces H1 and H7 ...", or say "four remaining strata".
- **m2 — Result A [L78], §2.3 [L123, L130], Table 2 [L224]: the depth parameter.** The capstone takes `(depth : Nat)`, and `SevenHighT0CanonicalHsbEvidence depth …` quantifies over `SevenHighT0Hsb.leaves depth mask`. "377,776 leaf formulas" is the count at depth 3, which the campaign used (README §1), and it is not a Lean-proved count. Fix: write "the 377,776 leaf formulas at symmetry-breaking depth 3" once in §2.3, and "at depth 3" in Result A.
- **m3 — §2.3 "The H7 certificates" [L132]: "about \$215 of cloud compute".** No cost appears in the linked `campaign_totals.json`, in `summary.json` or in the campaign README at the pinned commit. The README has only pre-run estimates ($68 spot; $160/$300 caps). R-SIMPLE also limits dollar figures to one sentence, and the $225 H1 figure (§3.2 [L191]) already uses it. Fix: delete the clause, or add the spend to a linked receipt.
- **m4 — Abstract [L66]: "each checked file is tied to its Lean formula by a compiled emitter".** That is exact for H1 (`v2cnf`). For H7, the base cubes were printed by interpreted `lean --run` (`EmitCube.lean`), and the symmetry-breaking and cover lines by a native generator hash-matched to Lean output. §3.4 [L203] and Table 2 [L225] already say "the emitters". Fix: "by emitters, not a kernel proof".
- **m5 — Table 2 "H7, $t=0$ formulas" [L225]: "377,804 refutations accepted by cake_lpr".** Strictly, 377,803 formulas were refuted directly and one through 257 split formulas, which the parenthetical half-says. Fix: "all 377,804 formulas refuted by cake_lpr, one leaf through a 256-way split (257 formulas) composed by a Lean lemma".
- **m6 — §2.3 [L130, L132], Table 2 [L224, L225]: no printed-axiom receipt for the H7 reduction or the split lemma.** H1's composition has `COMPOSITION_AXIOMS_20261006.txt`, and Table 2's H1 row says "a standard-axiom Lean lemma"; the H7 rows say only "a Lean lemma" and "not standard-axiom-only". Both source files end in `#print axioms`. Fix: link their printed outputs (or a receipt) in §8 and state the counts.
- **m7 — §2.2 [L104], §2.3 [L117, L119, L130], §7 [L262]: version-history voice.** "Lean now proves …", "agree but are no longer needed" (×3), "now superseded". A first-time reader has no earlier version for these to refer to. Fix: "An earlier reviewed argument (not used here) reaches the same conclusion: …".
- **m8 — §2.3 "The H7 certificates" [L132]: length.** The paragraph runs about 330 words, and the main text grew from 10 to 11 pages (R-SIMPLE target ~10). Fix: keep the pinned hashes, the identity method, the split, the scopes and the counts; move the three-pass/cap narrative, the machine type and the cost to the linked campaign README.
- **m9 — §8 "Small strata" [L278]: the item now lists only superseded reviewed arguments.** The Lean artifacts are in the next item. Fix: relabel it "Earlier reviewed arguments (superseded)".

## nit

- **n1 — §2.3 [L132]: "including the 233 that hit a cap and were re-run".** 232 were re-run at 12 h. The one that hit 12 h was split, not re-run. Fix: "232 re-run and one split".
- **n2 — §2.3 [L132]: first mention of CaDiCaL 3.0.1 is uncited.** The citation first appears in §2.4 [L147]. Move `\citep{biere2020cadical,biere2024cadical2}` to this first mention.
- **n3 — §1 [L85], §2.2 [L104]: "outright".** True: there is no hypothesis. But a reader may take it as "standard axioms". Consider "outright (by `native_decide`)". Table 2 already says "not standard-axiom-only".
- **n4 — §2.3 H5 [L119].** For parallel with H3's "408 `native_decide` axioms", give H5's printed count: 58 = 40 search + 18 graph-cover (`H5_TERMINAL_REVIEW_README_20261008.md`, "61 axioms").
- **n5 — refs.bib (carried from v9 n2).** No DOI for `tan2021cakelpr` or `heule2018schur`. Add them only through the resolver.

## v9 findings re-checked

- v9 M1 ("independently replayed"): obsolete. The sentence is gone, and H3/H5 are now credited to Lean.
- v9 M2 (stale STRATA receipt): partly fixed (the H1/H3 notes are on the release branch); stale again for v10 → M2 above.
- v9 m1 ("Both works"): fixed (L153).
- v9 m2 (Table 2 caption, axioms): fixed by "where axioms are listed".
- v9 m3 (H3 certificate sentence): obsolete.

## Procedural notes

- sidecar: staged and committed through `python -m anvil.lib.sidecar stage/commit` (issue #645 CLI shim), invoked as `PYTHONPATH=.anvil .anvil/.venv/bin/python -m ...`. `uv run` was not used; the system python3 lacks pydantic. The Stripe volume was read directly.
- numeric-consistency: automated (`anvil.lib.numeric_consistency`): 380 numbers, 0 findings; sidecar `erdos85-drop.10.numeric/`. A manual reconciliation of every H7/capstone number against `h7_collected_summary_20261011.json`, `h7_campaign_totals_20261011.json`, the residual/split manifests and the release/capstone READMEs is in `findings.md` §1.
- pending-marker: automated, 0 markers; sidecar `erdos85-drop.10.pending/`.
- audience-check: automated. 0 governance and 0 private-locator hits. The 8 `unlinked_artifact_path` hits (§8, L274–L281) are `\repofile` arguments and are false positives; all 64 link targets exist at the pinned commit. Sidecar `erdos85-drop.10.audience/`.
- render-gate: pass (14 pages, 0 overfull, 0 placeholders) on `erdos85-drop.10/main.pdf` and `compile-log.txt`; see `_gate.json`. The final xelatex pass has 0 undefined references; `pdftotext` finds 0 `??`.
- evidence-check: `anvil.lib.evidence_check` on the staged `scoring.md`: 9 dimensions, 0 findings, pass.
- evidence-drift: NO-SNAPSHOT (`erdos85-drop.10/_progress.json` has no `evidence_snapshot`; it was a direct edit). By hand: `BRIEF.md` is unchanged since v9, but `refs/` gained 7 files on 2026-10-11. They are the evidence for v10, and the BRIEF's `claim` and hard rules no longer match the paper (M3).
- No `lake build` or other heavy compute was run. Lean claims were checked by reading source at the pinned commit with `git show`.
