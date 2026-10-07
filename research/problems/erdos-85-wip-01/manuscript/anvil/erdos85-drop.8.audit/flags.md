# Audit flags for erdos85-drop.8

**Inputs.**

- `erdos85-drop/BRIEF.md`, with every amendment through R-V8 (R-AUD, R-LINK, R-CERT, Authorship, R-SIMPLE, R-BRIDGE, R-V8).
- `erdos85-drop/refs/**` (42 entries).
- The v8 review sibling `erdos85-drop.8.review/` (39/44, advance, 0 critical flags) and the deterministic siblings `.8.numeric`, `.8.pending` and `.8.audience`.
- The public branch content, read with `git show` at `origin/erdos85/integration` (`d1e12a86a60`) and `origin/erdos85/paper-v6` (`e451a842779`, equal to local HEAD).
- The Lean source under `proofs/Proofs/`, searched with ripgrep only, never built.
- The Crossref and DataCite metadata for the two hexagon DOIs.
- A fresh `xelatex` + `bibtex` + `xelatex` compile of a scratch copy.

**Verdict: AUDITED.**

- 0 critical flags.
- The pending gate passes.
- The reviewer's `advance: true` stands.
- The v8 version directory and every other sibling directory were left untouched.

## Critical flags (block advancement to AUDITED)

None.

- **Citations.** All 16 of 16 keys resolve. The PDF at the fixpoint has 0 `??`, `[?]` or `(?)`. No citation has a `does-not-support` verdict: 6 are partial and 10 are unverified because the source is not on disk (`citation-audit.md`).
- **Numbers.** There are 0 mismatches between the text, the tables and the receipts, and 0 untraced numbers. Every H1 total was recomputed from the per-row TSV and JSONL (`numerical-audit.md`).
- **Build.** Clean at the `.aux` fixpoint (non-critical notes below).
- **Unlinked artifact paths.** None qualify as critical. `public_repo_url` is not declared: `.anvil.json` and the BRIEF frontmatter both lack it, so `audience_check` reports `public_repo_url_source: derived`. The 6 hits it reports are, in any case, all `\repofile` links that the scanner does not expand (see the notes).
- **BRIEF scope rules: held.**
  - Result A is never called a theorem, a proof or "decided": "The result is not a Lean theorem" (L67) and "Result A is not a theorem of Lean" (L88).
  - cake_lpr is placed outside Lean: "a HOL4 theorem about its compiled binary, not a Lean kernel check" (L188).
  - Nothing is claimed about Erdős 85 itself: "one drop is compatible with either answer" (L67).
  - A-REG is "a hypothesis with a stated rival" (L69, L229).
  - Both H1 open items, (i) checks not admitted into Lean and (ii) file = formula rests on the compiled emitter, appear in the abstract (L67), in §1 (L88), in §3.4 (L188), in the Table 2 H1-orbits row and in the post-table paragraph (L215).
  - The H1 cover theorem's axioms are stated and linked (L130).
  - `LRAT.check` is mentioned once (L176).
  - R-AUD: a governance and private-locator grep finds 0 hits. The tool hits for "is proved", "theorem" and "proof" are all meta-statements about HOL4, Lean or A-REG.
  - R-LINK: details below.
  - The author line and contribution text follow the Authorship amendment.
  - `scope_lint.py`: PASS (34 numbers, 39 Lean names).

## Outstanding dependencies

None. `anvil.lib.pending_marker erdos85-drop.8/` returns `pass: true` with 0 markers and no `outstanding_sources`.

The tool was run **without** `--write-review`. This run's instructions forbid modifying sibling directories, and the existing `erdos85-drop.8.pending/_review.json`, written by the reviewer at 07:41, already records the identical clean result.

## Major findings (non-blocking)

- **M1: precedent comparison on two different axes** (§3, main.tex L138; carried from review M1, with audit evidence added).
  - The sentence says that, on encoding faithfulness, the empty-hexagon result is stronger because "their encoding is proved correct in Lean, whereas we connect each checked CNF file to its Lean formula only through a compiled Lean emitter".
  - The DataCite abstract of `subercaseaux2024hexagonlean` supports the first half ("we formalize and verify this result in the Lean theorem prover … a framework that connects geometric objects to propositional assignments").
  - The paper's own encoding-to-stratum link for H1 is, however, also a Lean theorem: `orderFortyNineStratumExcluded_one_of_capacityInventory_checked`, with 23 `native_decide` axioms (L130).
  - The sentence therefore sets their *encoding proof* against our *file-to-formula link*. Neither resolver abstract says how the precedent's DIMACS file is tied to its Lean formula, so the asymmetry on the file axis is unverified.
  - **Fix:** compare like with like. For example: "Both reduce the mathematical statement to a formula defined in Lean; their reduction is proved from the standard axioms, ours uses `native_decide` for finite enumeration checks, and we tie each checked file to the Lean formula through a compiled Lean emitter." Do not assert anything about how their file is produced unless the author confirms it from the paper.
  - This is not a claim-support failure, because the precedent *is* credited as stronger and nothing is overclaimed. It is a framing defect that undersells the paper.

## Minor findings

- **m1: the public-checker sentence promises a hash comparison that does not exist for the historical orbits** (§8 "Checking H1 yourself", L262; review minor, confirmed).
  - The sentence reads "`e85-check` … re-solves a census or historical orbit with the pinned CaDiCaL and compares the proof's sha256 with ours".
  - The 96 historical orbits were never solved by CaDiCaL. Their receipts hash drat-trim LRAT converted from archived Kissat DRAT (`h1_cert_historical96_cake_lpr_receipts.jsonl`; L176), so no CaDiCaL proof hash exists to compare against.
  - For the 3 Apple-silicon census orbits, a Linux re-solve gives a different proof, as `CHECKING.md` itself says ("reported as `PASS (proof differs …)`").
  - `CHECKING.md`'s own "Census + historical" table row has the same ambiguity. Its result tally lists bank, census and cube outcomes but no historical outcome.
  - **Fix (paper):** "… re-solves a census or historical orbit with the pinned CaDiCaL and checks the fresh proof with cake_lpr; for the 1,157 census orbits solved on Linux the proof's sha256 must also equal ours." **Fix (CHECKING.md, optional):** say the same.
- **m2: Lean's `LRAT.check` is referenced without a citation** (L176; review minor m1).
  - The attribution is accurate: `Erdos85LratRuntime.lean` uses Lean core's `LRAT` namespace.
  - R-SIMPLE (e) requires a citation if the checker is referenced, and R-V8 §1 allows dropping the mention.
  - **Fix:** drop the clause from "in which 50 of them …" to "… Section~\ref{sec:cube}", ending the sentence at "… in an earlier conversion pass." No resolvable citation is on disk, so do not invent one.
- **m3: the abstract's mapping of three methods to "the other three strata" is loose** (L67; review minor).
  - H7 is split by method between its t ≥ 1 and t = 0 cells, and H5 and H7 t=0 share the "reviewed arguments" method.
  - **Fix:** "The other three strata are closed by checked LRAT proofs (H3), certificates checked inside Lean (H7, t ≥ 1) and reviewed arguments with independently checked computation (H5; H7, t = 0)." This adds 30 to 40 characters, still under the 1,920 limit (currently 1,767).
- **m4: `heule2024hexagon` lacks its LNCS volume** (refs.bib; review minor).
  - Crossref's record for `10.1007/978-3-031-57246-3_5` carries no `volume` field, only the container titles "Lecture Notes in Computer Science / TACAS", pages 61–80, and ISBNs 978-3-031-57245-6 and 978-3-031-57246-3.
  - The volume could not be resolved from metadata in this run.
  - **Fix:** take the volume number from the Springer landing page for the DOI (TACAS 2024 Part I), and do not guess. The rendered entry is otherwise correct and complete enough to locate the paper.
- **m5: the shipped `erdos85-drop.8/main.pdf` is one xelatex pass short of the fixpoint** (version-dir build artefacts).
  - `erdos85-drop.8/main.log` ends with `LaTeX Warning: Label(s) may have changed. Rerun to get cross-references right.` (its line 887).
  - In the audit's scratch build, pass 3 moved the `sec:method` (§3.1) anchor from p. 4 to p. 5, and pass 4 was byte-stable.
  - The text layer of the shipped PDF is identical to the fixpoint PDF (`pdftotext` diff empty), so only the hyperref outline and anchor page for §3.1 are stale.
  - **Fix:** in the final build, run xelatex until neither "Label(s) may have changed" nor natbib's "Citation(s) may have changed" appears, which takes 4 xelatex passes for this paper, then ship that PDF.
- **m6: title scope** (L57; review minor, operator-owned).
  - "A Certificate-Checked Drop" also covers H5 and H7 t=0, which have no certificates. The abstract corrects this within two sentences.
  - The title is fixed by BRIEF R-CERT, so it is recorded for the operator's decision only.

## Nits (none changes a count, an evidence level or a link)

- **N1** (L174): "the solver's own 24-hour limit" was a configured cap. The census README says "CaDiCaL's 24 h `-t` cap on the longest row". Fix: "a 24-hour solver time cap on the longest orbit".
- **N2** (L188): the cost sentence ("about \$225 …") sits inside the trust paragraph. Move it to the end of §3.2 or to §8 (review nit).
- **N3** (L145 vs L176/L182): method step 2 gives cake_lpr as "commit `a36874a8`" generically. The historical and cube-leaf checks used a build identified only by binary sha256 `d23c413b…`, and the receipts do not record its commit. Optional: "(commit `a36874a8` for the bank and census; Section 3.2 gives the build used for the historical and cube-leaf checks)".
- **N4** (refs.bib, rendered bibliography):
  - `heule2016pythagorean` renders "boolean Pythagorean". Brace it as `{B}oolean`.
  - `bloom-erdos85` renders "Erdős problem #85". Brace the whole title.
  - `tan2021cakelpr` and `heule2018schur` carry no DOI. This is optional, and DOIs should be added only if resolved.
- **N5** (L132): CaDiCaL 3.0.1 is cited through the 2020 competition description (`biere2020cadical`). This is conventional, but a reader may notice the version gap. No on-disk alternative exists, so leave it unless a resolver-checked newer system description is added.
- **N6** (L123): `oneHighCapacityInventory_total_length`, which the paper cites for the 13,351 count, is itself proved by `native_decide`. It is not a dependency of the cover theorem (its axiom is absent from `H1_COVER_AXIOMS_20261006.txt`), so nothing in Table 2 changes. Optional: "(\lean{…}, by `native_decide`)".

## Non-critical notes

- **Build: clean, converged in 4 xelatex passes** (cap 5). The fixpoint is the absence of both rerun warnings plus a byte-identical `.aux`.
  - The sequence was xelatex, bibtex, xelatex, xelatex, xelatex, and all 5 invocations exited 0.
  - Pass 2, the first after bibtex, did not print "Label(s) may have changed" but still had all 22 citation occurrences undefined and printed natbib's `Citation(s) may have changed`. Under author-year natbib, `\bibcite` lands in the `.aux` only on that pass.
  - Pass 3 resolved the citations, which shifted §3.1 to p. 5 and printed "Label(s) may have changed". Pass 4 printed neither warning, and its `.aux` was byte-identical to pass 3's.
  - The final log has 0 errors, 0 undefined citations or references and 0 overfull boxes. It has 4 underfull boxes: badness 3271, 10000 and 5741 in the §5 residue paragraph at L221 (long Lean names), and 10000 on the §8 opening line at L253 (repository URL).
  - There are 56 cosmetic `Font shape TU/Menlo…` substitution lines. BibTeX reports `warning$ -- 0`.
  - The PDF has 12 pages, with references starting on p. 11, so the main text is 10 pages. `pdftotext` finds 0 `??`.
  - The compile ran in a scratch copy of `main.tex`, `refs.bib` and `anvil-paper.cls`. The raw bytes of all 5 invocations landed in `compile-log.txt` via `sidecar copy` (sha256 `4edfa8c634996a91…`).
  - **Tooling note for anvil:** the spec's convergence test greps only for "Label(s) may have changed". On this natbib paper that test would have stopped at pass 2 with `(?)` citations in the PDF. Grepping for "may have changed" covers both packages.
- **R-LINK and link hygiene.**
  - There are 55 `\repofile` / `\repofiletab` uses over 49 distinct targets, all through the single `\repobase` macro.
  - 40 of 49 exist on `origin/erdos85/integration`.
  - The other 9 exist only on `origin/erdos85/paper-v6` (`e451a842779`) and are verified there by `git cat-file`: `CHECKING.md`, `h1_checker_kit/`, `h1_bank_check_20261006/` and its 3 receipts, `historical96_cake_lpr_receipts.jsonl`, `COMPOSITION_AXIOMS_20261006.txt` and `H1_COVER_AXIOMS_20261006.txt`.
  - These 9 resolve after paper-v6 is merged into `erdos85/integration`. Per this run's instructions they are not a critical flag.
  - GitHub sample: 2 of 2 integration files returned 200, 1 integration directory returned 301, `CHECKING.md` returned 404 on integration and 200 on paper-v6.
  - The `audience_check` link-hygiene result is `pass: false` (6 hits, L255–L260). These are false positives: every flagged path is the argument of a live `\repofile`, which the scanner does not expand. The same 6 hits were reported for v7 and v8 by the `.audience` sibling.
  - The room transcript URL is linked (R-BRIDGE). No bucket name or `s3://` appears in the paper.
  - "Not published" (L264) correctly excludes the bank proofs and the checker kit (R-V8 §4).
- **Audience-fit notes** (step 6c): none. `governance_vocabulary` 0, `private_locator` 0.
- **Unverified citations (10)** and **partial (6)**: no PDF of any cited work is on disk.
  - Before submission, the author should confirm the claims carried by `tan2021cakelpr` (parsing included in the HOL4 guarantee, L136), `heule2024hexagon` (cake_lpr-checked, L138) and `zhang2017polarity` (r(109) and r(155) bounds, L240).
- **Evidence drift** (`anvil.lib.evidence_drift check`): `brief_drifted: true`, `refs_drifted: false`.
  - The BRIEF frontmatter `claim` was updated at 07:41, after the v8 snapshot.
  - The reviewer judged that update consistent with v8 (R-BRIDGE wording). It is advisory only and does not gate.
- **Corpus provenance tier:** inactive, because the BRIEF frontmatter has no `corpus:` key. No `.corpus-audit/` sibling was written.
- **Lean identifiers:** 47 of 47 declaration-shaped names were found (ripgrep, no build). See `numerical-audit.md`, "Deterministic tools".
- **Iteration cap:** this is iteration 8 of `max_iterations: 8`. Every recommended fix above is mechanical or wording-level and suits a final operator pass. None changes a number, an evidence level or a link target.
- **Git sync:** skipped. There is no `.anvil/config.json` in the consumer root, and this run's instructions exclude commits. No solver, AWS, Docker or Lean build was run. The thread BRIEF, `refs/`, `erdos85-drop.8/` and the `.8.review`, `.8.pending`, `.8.numeric` and `.8.audience` siblings were not modified.
