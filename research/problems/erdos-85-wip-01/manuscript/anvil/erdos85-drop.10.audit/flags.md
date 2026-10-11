# Audit flags for erdos85-drop.10

**Inputs.**

- `erdos85-drop/BRIEF.md`, unamended since R-TITLE (2026-10-07). There is no R-V10.
- `erdos85-drop/refs/**`, 51 entries. Seven were added on 2026-10-11 for v10. One more, `CAPSTONE_ABSOLUTE_PATH_AUDIT_20261011.json` (untracked), appeared during this audit; it was read and is cited below.
- Review `erdos85-drop.10.review/`: 37/44, advance, 0 critical; majors M1–M3.
- Deterministic siblings: `.10.numeric`, `.10.pending`, `.10.audience`.
- Codex's independent rebuild `erdos85-drop.10.independent/`.
- `erdos85-drop.9.operator/`, an agent-transcribed operator instruction and not a human review.
- The pinned commit `1d0772cd825462f5230f224c2110231c6483d5e4`, read with `git show`, `git cat-file` and `git archive`. It is an ancestor of `origin/erdos85/release-assembly-20261011`; `git ls-remote` gives the remote head as `98ee2fc33428`.
- A fresh `xelatex` + `bibtex` + `xelatex`×3 compile of a scratch copy.

No Lean build and no heavy compute was run. Nothing was written to `erdos85-drop.10/`, `paper/`, the review sidecar or any other sibling.

**Verdict: BLOCK.** There are two critical flags, both one-line text fixes. The thread stays `READY-WITH-AUDIT-FLAGS`; it is not `AUDITED`. The build, citations, link targets, pending gate and every count in the paper are clean. The substance of the upper side meets the dispatch standard: in every mention it reads as conditional on two explicit UNSAT hypotheses checked by cake_lpr outside Lean.

## Critical flags (block advancement to AUDITED)

- **C1 — BRIEF hard scope rule, "critical if violated": Result A is called a theorem** (Abstract L66, §1 L85).
  - BRIEF "Hard scope rules": "Never call Result A a theorem, proof, or 'decided'." R-CERT and R-SIMPLE restate it ("Result A is still never a theorem"; "never 'theorem'/'proof'/'decided' for Result A"). The frontmatter `claim` still says "not a Lean theorem".
  - v10 L66: "The result is a Lean theorem conditional on two explicit unsatisfiability hypotheses". "The result" is Result A.
  - v10 L85: "so the upper side is a single Lean theorem whose only hypotheses are the two families of checked formulas".
  - The Lean fact is accurate. `not_c4FreeMinDegreeWitness_fortyNine_seven_of_h1_h7Evidence` takes exactly `hOne`, `depth` and `hSeven` (pin, `Erdos85OrderFortyNineCapstoneH3.lean` L18–28), and its docstring says "this is not an unconditional Lean proof". The hypotheses are named in the same sentence, so this is not an overclaim of substance. But the rule is unamended. Its only claimed relaxation is `erdos85-drop.9.operator/`, an agent transcription whose own agreed wording ("Lean-verified reduction conditional on explicitly stated UNSAT evidence") avoids "theorem". A dispatching agent's message cannot amend the BRIEF.
  - `scope_lint.py` does not catch this, because its pattern needs the literal "Result A is …".
  - The other uses comply: Result A L78 ("the conclusion of the Lean theorem …", which names the implication), L87, L232.
  - **Fix (either path clears it):**
    - (a) Reword L66: "Lean derives the upper side from two explicit unsatisfiability hypotheses, $h_{\mathrm{H1}}$ and $h_{\mathrm{H7}}$, which the external checks support but which are not admitted into Lean;". Reword L85: "… so Lean derives the upper side from exactly two hypotheses, the two families of checked formulas."
    - (b) The operator adds an R-V10 BRIEF amendment that replaces the rule with "never call Result A an unconditional Lean theorem" and updates `claim`.
  - Either way, a re-audit of the resulting version is needed. This sidecar is read-only once written.

- **C2 — Untraced number: "about \$215 of cloud compute"** (§2.3 "The H7 certificates", L132).
  - The sentence cites `h7_hsb_campaign_20261008/receipts/collected/campaign_totals.json`. At the pin, that file is byte-identical to `refs/h7_campaign_totals_20261011.json`, and it has no cost field.
  - The H7 README at the pin (= `refs/H7_HSB_CAMPAIGN_README_20261011.md`) has only pre-run estimates ($68 spot; $160 hard stop).
  - No file in `refs/` contains \$215.
  - The figure first appears in commit `d56328ec42b`, after the pin, in the README L9–10: "Cost (controller-reported estimates, not billing totals): main \$125.24, residual \$81.99, split \$1.53, plus about \$6 … about \$215 in all" (sum \$214.76).
  - So the number violates both the BRIEF rule that every number traces to `refs/` and the paper's own promise that "every number traces to a linked receipt" (L87). The paper also drops the source's qualifier.
  - It also makes the paper's second dollar sentence, against R-SIMPLE's "dollar figures at most one sentence" (the H1 \$225 at L191 is the first).
  - **Fix:**
    - Preferred: delete ", and about \$215 of cloud compute" from L132, which also restores R-SIMPLE.
    - Or: repin `\repobase` to a commit at or after `d56328ec42b`, link `h7_hsb_campaign_20261008/README.md` for the figure, write "about \$215 of cloud compute (a controller-reported estimate, not a billing total)", and copy that README revision into `refs/`.

## Outstanding dependencies

None. `python -m anvil.lib.pending_marker erdos85-drop.10/` returns `pass: true` with 0 markers. It was run without `--write-review`: `.10.pending/` already holds the identical result, and this run leaves sibling dirs untouched (parallel-safe).

## Major findings (non-blocking for AUDITED; release preconditions before tag / Zenodo)

- **M1 (= review M1, independently confirmed) — the capstone cannot be recompiled from the public repository, and the paper does not say so** (§4 post-table L232, §1 "What is not claimed" L87; Table 2 L223 and §8 L285 disclose only that the files are absent).
  - The import closure of `Erdos85OrderFortyNineCapstoneH3` at the pin has 892 modules, traced over the extracted sources. Exactly 13 of them, `Erdos85OrderFortyNineSevenHighT{1..7}Rep*Certificate`, `include_str` absolute paths `/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/strata-lrat/h7_t*_rep*.packed.lz4p7`.
  - `refs/CAPSTONE_ABSOLUTE_PATH_AUDIT_20261011.json`: 13 files, 2,574,916,357 B in all, largest 1,606,429,555 B. That is far over GitHub's 100 MB per-file limit, so publication needs Zenodo or LFS, not a plain commit.
  - L232 calls the right-hand column "the complete list" and paraphrases it without this item, and it says a cold rebuild "would still list the native_decide axioms". That is true only on the producing host.
  - (Many `Erdos85H1V2CertP0I*` modules also carry absolute paths. They are outside the capstone closure and are not cited.)
  - **Fix:** add "and publication of the 13 packed H7 ($t\ge1$) certificate files, which the capstone reads by absolute path and without which it cannot be recompiled from the public repository" to L232 and L87. Better: deposit the files (Zenodo), repoint `include_str` to a repository-relative path or a fetch step, and repin before the tag.

- **M2 (= review M2, confirmed; v9 P1 recurs) — the linked receipt `STRATA_AND_SMALL_ORDERS_20260928.md` contradicts v10** (§8 L277).
  - At the pin and unchanged through `98ee2fc`:
    - the H3 row describes reviewed Python searches and no Lean discharge;
    - the H5 row says "reviewed paper/computation cover";
    - the H7 row says the Lean capstone "is not instantiated".
  - v10 says H3 and H5 are excluded in Lean and H7 ($t=0$) reduces to `orderFortyNineStratumExcluded_seven_of_structuralHsbEvidence`.
  - **Fix:** commit a dated "superseded for H3/H5/H7 by `order49_h3_closed_capstone_20261008/README.md` and `release_assembly_20261011/README.md`" banner on the release branch and repin, or cite the capstone README for "the strata names" in L277 instead.

- **Review M3 is absorbed into C1.** This audit treats the BRIEF conflict as critical because the BRIEF labels the rule "critical if violated" and no amendment exists.

## Minor findings

- **m1** Abstract L66: "into four strata". §2.2 has $h\in\{1,3,5,7,9\}$ with $h=9$ refuted. Fix: "into five strata …, refutes H9, excludes H3 and H5" or "four remaining strata".
- **m2** Result A L78, §2.3 L123, Table 2 L224: 377,776 is the leaf count at symmetry-breaking depth 3. The capstone quantifies over `(depth : Nat)` and the leaves of `SevenHighT0Hsb.leaves depth mask`. Fix: "377,776 leaf formulas at symmetry-breaking depth 3", once in §2.3 and in Result A.
- **m3** Abstract L66: "tied to its Lean formula by a compiled emitter". For H7 the base cubes were printed by interpreted `lake env lean --run` (`EmitCube.lean`, README L38–39) and the hsb/cover lines by a native generator hash-matched to Lean. Fix: "by emitters, not a kernel proof" (as §3.4 and Table 2 already say).
- **m4** Table 2 L225: "377,804 refutations accepted by cake_lpr". 377,803 were refuted directly and one through 257 split formulas. Fix: "all 377,804 formulas refuted by cake_lpr, one leaf through a 256-way split (257 formulas) composed by a Lean lemma".
- **m5** Table 2 L224–L225, §2.3 L130/L132: no printed-axiom receipt is linked for the H7 reduction or for `sevenHighT0CanonicalHsbLeafChecked_of_split`. H1 has `COMPOSITION_AXIOMS_20261006.txt`. Fix: link their `#print axioms` output and state the counts.
- **m6** L232: the "complete list" sentence does not mention the H7 $t\ge1$ row's own open item (files not public). It is fixed together with M1.

## Nits (none changes a count, evidence level or link)

- **N1** (L132) "including the 233 that hit a cap and were re-run": 232 were re-run at 12 h and 1 was split. Fix: "232 re-run and one split".
- **N2** (L132) The first mention of CaDiCaL 3.0.1 is uncited; the citation is at L147. Move `\citep{biere2020cadical,biere2024cadical2}` to L132.
- **N3** (L104, L117, L119, L130, L262) Version-history voice ("now proves", "no longer needed" ×3, "now superseded"). Fix: "An earlier reviewed argument (not used here) …".
- **N4** (L203) "the same trusted base": the H7 checker `4d47ffdd…` is the builder build of commit `a36874a8`, and the H1 fleet checker is `95b64883…`. They share a commit, not a binary. Fix: "the same checker commit".
- **N5** (L278) The "Small strata" item now lists only superseded reviewed arguments. Fix: relabel it "Earlier reviewed arguments (superseded)".
- **N6** (L119) For parallel with H3, give H5's printed count: 61 = 3 + 40 + 18 graph-cover.
- **N7** Review n5 is stale: `tan2021cakelpr` and `heule2018schur` both carry DOIs in `refs.bib`.

## Non-critical notes

- **Build: clean, converged at pass 4** (cap 5).
  - Sequence: xelatex → bibtex → xelatex (pass 2: natbib "Citation(s) may have changed") → xelatex (pass 3: "Label(s) may have changed") → xelatex (pass 4: neither warning; `.aux` byte-identical to pass 3).
  - All 5 invocations exit 0.
  - Final log: 0 errors, 0 undefined citations/references (the 26 "undefined" lines are Menlo font-shape substitutions, cosmetic), 0 overfull, 6 underfull. Three are at L238–239 (long Lean names) and three at L272–273 (repository URL line).
  - BibTeX: 0 warnings. 14 pages; references from p. 12.
  - Raw bytes of all passes landed via `sidecar copy` (`compile-log.txt`, sha256 `49dc18d2cc202949…`).
- **Shipped PDF is current.** `pdftotext -layout` of `erdos85-drop.10/main.pdf` (sha256 `61cf7c3a…a798`) is identical to this audit's fixpoint PDF. The source hashes (main.tex `c3d226a7…`, refs.bib `2d5b67fb…`, cls `a010d389…`) equal codex's independent record.
- **Link hygiene (step 6c).**
  - `audience_check`: governance 0, private_locator 0, unlinked_artifact_path 8.
  - All 8 hits are `\repofile` arguments, which the scanner does not expand: false positives, dropped.
  - `public_repo_url` is `derived` (`https://github.com/rjwalters/lean-genius`), not declared, so these would be non-critical regardless.
  - All 63 distinct targets (69 uses) exist at the pin.
  - "Not published" (L285) names the H7 $t\ge1$ packed certificates, the remaining certificate storage and the artifact volume. No bucket name or `s3://` appears in the paper.
- **Audience-fit notes:** none in the paper text. The linked README at `d56328ec42b`, if adopted per C2, mentions "the operator's \$300 H7 ceiling". That is governance vocabulary in a receipt, not in the paper, but it is worth trimming if it becomes a cited source.
- **Claim-scope sweep (dispatch focus).**
  - H1 and H7 ($t=0$) are never said to be excluded in Lean. Both are "reduced" (L66, L104, Table 2).
  - cake_lpr is outside Lean in every mention (L66, L87, L203, Table 2 L220/L225, L232).
  - The `native_decide` dependence is disclosed with counts (L66, L111, L153, Table 2).
  - "Outright" for H3/H5 (L85, L104) is paired with Table 2's "not standard-axiom-only".
  - Nothing is claimed about Erdős 85 (L66, L87). A-REG is "a hypothesis with a stated rival" (L68, L246).
  - The only scope defect is the wording in C1.
- **Unverified citations (11) and partial (6).** No source PDF is on disk.
- **Evidence drift.** `anvil.lib.evidence_drift check erdos85-drop erdos85-drop.10`: NO-SNAPSHOT (v10 was a direct edit), treated as clean. By hand: the BRIEF `claim` and "Strongest honest claim" describe the pre-v10 state (H3/H5/H7 $t=0$ open in Lean). This is advisory, and it is the root of C1.
- **Corpus provenance tier:** inactive (no `corpus:` key). No `.corpus-audit/` sibling.
- **Iteration cap:** v10 is iteration 10 of `max_iterations: 8`, under an operator override whose only record is agent-transcribed. C1 and C2 are one-line text edits, and M1/M2 are repository actions, so none of them needs a full lifecycle iteration. They do need a new version (or a BRIEF amendment) plus a re-audit before `AUDITED`.
- **Git sync:** skipped (no `.anvil/config.json`; the run instructions exclude commits).
