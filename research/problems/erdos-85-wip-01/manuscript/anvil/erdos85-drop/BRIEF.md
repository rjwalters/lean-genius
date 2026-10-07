---
title: "A Drop at Forty-Nine in Erdős Problem 85"
author: "Claude Fable, GPT Sol, Astra, Claude Opus and Robb Walters"
affiliation: "Lean Genius project, 2AM Logic"
venue: "arXiv"
anonymous: false
claim: "Lean reduces the one-high stratum H1 — the bulk of the upper side at order 49 — to 13,351 symmetry-reduced SAT formulas, and every one has an unsatisfiability proof accepted by the CakeML-verified checker cake_lpr; the three smaller strata are closed by Lean-checked certificates (H7, t ≥ 1) and reviewed arguments with independently checked computation (H3, H5, H7 t = 0). With Lean-checked lower-side witnesses this gives f(48) = 8 and f(49) = 7, a strict drop, as a certificate-checked computational result — not a Lean theorem, because the external checks are not admitted into Lean, the checked files match the Lean formulas only through a compiled emitter, and the H3 and H5 premises and the H7 t = 0 capstone are open in Lean. Separately, Lean 4 verifies that one uniform proposition, A-REG, implies a negative answer to Erdős Problem 85."
keywords:
  - Erdős problems
  - C4-free graphs
  - minimum degree threshold
  - SAT solving
  - Lean 4
  - cube-and-conquer
documentclass: anvil-paper
web_search: false
---

# Brief: the Erdős 85 twin-result paper

This thread adopts an existing, near-final Markdown manuscript (`refs/DRAFT.md`, banked on
`erdos85/integration` as `research/problems/erdos-85-wip-01/manuscript/DRAFT.md`) into the
anvil paper lifecycle for review and revision. Version 1 is a faithful LaTeX conversion of
that draft; later versions may reorganize and tighten it but must not change any factual claim
without a receipt in `refs/`.

## The two results

1. **Result A (computational).** Let `f(n)` be the least `d` such that every graph on `n`
   vertices with minimum degree at least `d` contains a 4-cycle. Explicit graphs checked in Lean
   (via `native_decide`) give `f(48) ≥ 8` and `f(49) ≥ 7`. The upper side at order 49 splits into
   strata H1, H3, H5, H7; H3/H5/H7 are closed by reviewed arguments plus computation; H1 is
   1,257 SAT instances, 96 with 2026-08 drat-trim-verified certificates and 1,161 refuted by
   Kissat 4.0.4 then CaDiCaL 3.0.1 under declared caps (1,160 whole instances; one by an exact
   36-cube partition after it defeated every whole-instance cap up to 24 h). No SAT model, no
   solver disagreement. This is verdict-only evidence, not a proof; the paper prices the
   certificate route and proposes a cheaper cube-partitioned route.
2. **Theorem B (Lean, standard axioms only).** `BinarySquareRegularExclusion` (A-REG: for every
   k ≥ 3 no C4-free 2^k-regular graph on 4^k vertices) implies `¬ Erdos85Question`. A-REG is a
   live hypothesis, not a conjecture the authors endorse; the plane-order reading is the rival.

## Strongest honest claim

Every input to the formal finite-drop theorem is either Lean-checked or reproducible from banked
solver receipts; the one unproved hypothesis (no C4-free 49-vertex graph of minimum degree 7)
now rests on a complete two-solver census with an empty open list. Readers who know SAT-based
combinatorics will find the census scale (about 1,400 hard instances, 5,700 solver core-hours)
and the cube-partition closure of the hardest instance the surprising parts; readers who know
Erdős 85 will find the one-proposition reduction the generative part.

## Hard scope rules (critical if violated)

- Never call Result A a theorem, proof, or "decided". Never claim anything about Erdős
  Problem 85 itself (one drop is compatible with either answer).
- Never call A-REG a conjecture of the authors; it is a hypothesis with a stated rival.
- Never promote a solver verdict or archived certificate to a kernel-checked statement.
- Every number must trace to `refs/CENSUS.md`, `refs/h1-census-table.json`,
  `refs/AXIOM_AUDIT_COLD_20260927.md` or the literature notes; no new numbers.
- Authorship and contributions follow the operator's ruling (Claude Fable and GPT Sol; the
  human operator and the room infrastructure acknowledged, not authors); contribution
  statements must stay transcript-true.
- Cite Boza for the Ramsey table and the open r(42) entry; cite Afzaly–McKay only for their
  example records; keep the "to our knowledge, first decided strict drop" phrase epistemic and
  conditional on the evidence level (see `refs/FIRST_DROP_LITERATURE_CHECK.md`).
- Conventions: `F(N)` / `f(n)` is the Erdős 85 function; Boza's `r(s) = R(C4, K_{1,s})` is the
  Ramsey function; say which is in use whenever a value is quoted.

## Audience and length

Combinatorialists and formal-methods readers. Target 12 to 18 pages plus appendices; the
negative map and the campaign-process sections may be shortened or moved to appendices if the
reviewer finds them digressive, but the evidence-level table, the trust-boundary discussion,
the cost-to-verify section and §8 must survive intact in substance.

## References supplied

`refs/` holds the prior draft, the census summary and table, the cold axiom audit, the
literature check, the erdosproblems post draft and the pause handoff. `refs.bib` holds the
resolvable citations; do not invent others (web search is off).

## Hard rules added 2026-09-28 after the operator's read-through of v4

These two rules are scope rules of the same standing as the ones above: a violation is a critical flag.

- **R-AUD (audience only).** The audience is combinatorialists and formal-methods readers. No sentence may address the project's operator or team. Remove every statement about what is or is not *authorized*, *commissioned*, *budgeted*, *cancelled by the operator* or *gated for publication*; every goal, ticket or board number; every room-message number or other pointer into the private transcript; and every reference to "operator review" or "the operator's publication gate". What the paper may say instead is the reader-relevant fact (e.g. "no certificates were produced for the residual rows", "the certificate bank is not public"). Appendix B may keep its *technical* lessons (what was checked, what failed, why, and what it cost) written for a reader; the governance narrative (goals, authorizations, who decided what, transcript pointers) goes.
- **R-LINK (public links).** Every artifact, receipt, script, ledger or Lean module the paper names is a hyperlink to its public location in the GitHub repository, through one base-URL macro so the base can be switched from the branch to the release tag at publication: `\newcommand{\repobase}{https://github.com/rjwalters/lean-genius/blob/erdos85/integration}` and `\repofile{<path>}{<label>}` expanding to `\href{\repobase/<path>}{\texttt{<label>}}`. Lean modules live under `proofs/Proofs/`; research files under `research/problems/erdos-85-wip-01/`. Things that are not public (the S3 certificate bank, the artifact volume, the room transcript database) are described in one sentence as not published, never as paths or bucket names. Repo-relative paths without a link are not acceptable in §7, Appendix A or anywhere else.

Canonical public paths of the receipts (all on `erdos85/integration`, under `research/problems/erdos-85-wip-01/`): `CENSUS_TIMING_20260928.md`, `CERT_BANK_STATS_20260926.md`, `STRATA_AND_SMALL_ORDERS_20260928.md`, `H7_POSITIVE_TRIPLE_CELLS_H5_CLOSURE_FORMULA_COUNTS_20260928.md`, `PAUSE_HANDOFF_20260927.md`, `sat49/BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt`, `sat49/verify_boza48_nonisomorphism.py`, `q7_h5_closure_ledger/README.md`, `q7_h5_closure_ledger/REVIEWED_RESULT.md`, `q7_h5_closure_ledger/review2065.json`, `q7_h5_closure_ledger/reviewer/REVIEW2065.json`, `phase_b_h1_census_20260927/…`, `AXIOM_AUDIT_COLD_20260927/axioms.out`, `H7_CLOSURE_20260915.md`, `PHASE_B_*`, `Q7_*`, `manuscript/FIRST_DROP_LITERATURE_CHECK.md`, `phase_b_h1_verdict_cloud_20260921/`, `q9_solver_controls/…`, `cayley-census-q11-q13/…`, and the Appendix A ledger directories. The thread's `refs/` copies are working copies for the critics, not citable locations.


## Brief amendment R-CERT (2026-10-06, after the H1 certificate check)

Between v5 and this amendment the H1 stratum was certificate-checked (receipts in `refs/`:
`H1_CERT_RECEIPTS_README_20261006.md`, `h1_cert_census_summary.json`, `h1_cert_census_receipts.tsv`,
`h1_cert_historical96_receipts.jsonl`, `pilot_h1_81494a_leaf_cake_lpr.jsonl`,
`COMPOSITION_AXIOMS_20261006.txt`, `Erdos85H1CubePilot81494a_excerpt.lean`). Version 6 must be
re-framed around that fact. `refs/MAIN_TEX_20261006_H1_CERT_DIRECT_EDITS.tex` is v5 with first-pass
direct edits that already state most of the new facts (sections "Certifying H1 (October 2026)" and
"Why the whole-instance route sufficed"); use it as source text, but the reviser owns the result
and must re-verify every number against the receipts.

**New framing (operator decision).** Lead with certified computation: every SAT instance behind
the drop has a certificate accepted by a formally verified checker. The title is the frontmatter
title above. The abstract, introduction, Result A section, evidence table, trust section,
interpretation (whose heading still says "the price of certainty") and conclusion must tell that
story consistently — the cost-to-verify / cube-projection material becomes the report of what was
run and what it cost, and the "we chose to stop at belief" framing is retired.

**Facts the paper may state (each traces to the refs above).** 1,160/1,160 census rows CERTIFIED:
CNF regenerated by the pinned `v2cnf` emitter and sha-matched to the census; CaDiCaL 3.0.1 with
binary LRAT proof logging; the proof streamed into `cake_lpr` (Tan, Heule, Myreen, TACAS 2021;
`tan2021cakelpr`), success = CaDiCaL `s UNSATISFIABLE` and cake_lpr `s VERIFIED UNSAT`; proofs
checked and discarded, sha256 and length kept. 5.64 TB of binary LRAT; largest proof 36.2 GB;
3,435 solver CPU-hours; 207 checker CPU-hours; 0 rejections; 0 SAT across 1,196 ledgers.
Determinism: three rows certified twice on different instance types with the same binary gave
byte-identical proofs; a macOS build gives different, equally valid proofs. Pilot root
h1_81494a6ef36d3ec9: 36/36 leaves accepted by cake_lpr (30 also by Lean's compiled `LRAT.check`);
the Lean lemma `cnf_unsat_of_h1Cube81494a` (module `Erdos85H1CubePilot81494a.lean`, generic
`cnf_unsat_of_cubeTree` in `Erdos85CubeTreeComposition.lean`) composes them over the Lean-generated
`oneHighFamilyV2SatCnf`, axioms `propext`, `Quot.sound` only. Historical 96: re-checked from
archived DRAT via drat-trim → LRAT, 50 accepted by compiled `LRAT.check`, 46 by cake_lpr, none
rejected. Memory: Std `LRAT.check` needed about 10× the binary proof size in RAM; cake_lpr streams
with a bounded heap (4 GB for most rows, 16 GB for the longest). Cloud cost about $200.

**Scope rules that still hold (critical if violated).** Result A is still never a theorem, proof
or "decided"; cake_lpr is a CakeML-verified checker *outside* Lean, not a Lean kernel check, and
the paper must say so; "certificate-checked" / "checked by a formally verified checker" are the
permitted phrases. Name the remaining gaps every time the status is summarized: the H1 semantic
bridge (row-to-stratum assembly), the three H5 Boolean-exclusion premises, the uninstantiated H7
t=0 capstone, the `native_decide`/`Lean.ofReduceBool` dependence of the lower-side witnesses and
the H7 certificate modules, and admitting external checks into Lean. The 34 capacity-grid slots
outside the frozen source are verdict-only; do not include them in "every H1 instance".
R-AUD and R-LINK still apply: link the new receipts through `\repofile` — public paths
`research/problems/erdos-85-wip-01/h1_cert_full_20261001/receipts/` (README.md,
h1_cert_census_receipts.tsv, h1_cert_census_summary.json), `h1_cert_full_20261001/`,
`h1_cert_pilot_20261001/` (incl. `COMPOSITION_AXIOMS_20261006.txt`), and the Lean modules above;
no budget/operator/goal language. Contributions: the October 2026 H1 certificate check, including
the Lean cube-tree composition lemma, was run by Claude Opus (authorship line unchanged).

**Also fix in v6 (open items from the v5 manuscript-of-record README).** (a) Audit nit: the §3.1
`Lean.ofReduceBool` identification is a statement about Lean's implementation, not something
`axioms.out` prints — say so. (b) Audit nit: Appendix B "thirteen input hashes" are the 2026-08
grid campaign's inputs, not the thirteen H7 certificate modules — correct it. (c) The abstract
must again disclose that the lower-side witnesses use `native_decide`.


## Authorship amendment (2026-10-06, operator decision; supersedes the earlier authorship rule)

Author line, in this order: **Claude Fable, GPT Sol, Astra, Claude Opus, Robb Walters**.
Affiliation for Robb Walters: 2AM Logic (keep the paper's existing "Lean Genius project, 2AM Logic"
affiliation line). Robb Walters is last author as the person who funds and directs the lab; he is
now an author, so the earlier "human operator acknowledged, not an author" sentence is retired —
but R-AUD still holds (no governance narrative, budgets or authorization language). Astra is
OpenAI's flagship model; in the collaboration room both GPT Sol and Astra worked under the
"sol" persona, so their contributions are stated jointly unless a receipt separates them:
"GPT Sol and Astra (OpenAI) developed the structural reductions, the negative map and the
independent audits; both worked under the shared 'sol' seat of the collaboration room."
Claude Fable: as before. Claude Opus: the October 2026 H1 certificate check, including the Lean
cube-tree composition lemma. Robb Walters: set the project's priorities and scope and directed the
lab (state this neutrally, as a contribution, not as an authorization). The room infrastructure
remains acknowledged, not an author.
Credit granularity (operator, 2026-10-06): joint credit for GPT Sol and Astra is final. Add one
reader-facing sentence to the collaboration/methods text: the work ran over several months and
used the strongest frontier models available at each stage, so the models behind a seat changed
during the project (which is why GPT Sol and Astra share the "sol" seat).


## Brief amendment R-SIMPLE (2026-10-06, operator direction; governs v7)

**The new fact.** The v6 review's critical flag (H1 is 13,351 capacity orbits, not 1,257) is now resolved
by evidence, not wording: the 12,094 orbits that rested on the 2026-08 certificate bank were re-checked
by cake_lpr — 12,094/12,094 VERIFIED (refs: `H1_BANK_CHECK_README_20261006.md`,
`h1_bank_check_summary.json`, `h1_bank_check_receipts.tsv`; public path
`research/problems/erdos-85-wip-01/h1_bank_check_20261006/receipts/`). So **all 13,351 H1 orbits** have
an unsatisfiability proof accepted by a formally verified checker: 12,094 bank + 1,160 census by
cake_lpr; h1_81494a6ef36d3ec9 by cake_lpr on 36 cube leaves + the standard-axiom Lean composition
lemma; 96 historical by cake_lpr (46) or Lean's compiled `LRAT.check` (50). Bank totals: 22.55 TB of
LRAT, largest 26.5 GB, every check within an 8 GB heap; CNF, gz and LRAT sha256 all match the producer
ledgers; one orbit with no producer ledger is verified from the pinned-emitter CNF and cake_lpr alone.
Combined with October: about 28 TB of LRAT checked and discarded. The H1 stratum is *capacity orbits*
(symmetry-reduced); explain in one sentence what an orbit is and why 13,351 cover H1.

**Operator direction (verbatim intent):** "simplify our paper … we really only have a few key results
and I think we will get a better reception from the mathematicians if we don't overclaim" and "I also
don't want to minimize what we've accomplished because I also think we've made a real contribution."
Both are binding: no overclaiming (dims 2/9) and no underclaiming / buried lede (dim 3).

**Structure (target ~10 pages of main text before references; appendices allowed but short):**
1. Introduction: the problem, the two results stated precisely, what is and is not claimed, in one page.
2. The drop at 48→49: lower sides (Lean witnesses via native_decide), the Lean case split into strata,
   how each stratum is closed. H1 is the bulk: 13,351 orbits, all certificate-checked.
3. How H1 was checked: the check-then-discard method (CNF regenerated by a Lean-emitted program and
   hash-matched; proof streamed into cake_lpr; proofs discarded, hashes kept; byte-identical
   regeneration with the same binary); the bank re-check; the cube tree for the hardest orbit and the
   Lean composition lemma. This is a genuine methodological contribution — present it as one.
4. ONE status table: each component (lower sides, case split, H1, H3, H5, H7, the encoding bridge),
   how it is checked, what remains open in Lean. State the open items once, here; elsewhere refer to
   the table instead of repeating the list.
5. Theorem B and the residue beneath A-REG (the defect-operator view), plus the evidence on A-REG,
   with f(15) = f(16) = 5 refuting the q = 4 analogue.
6. A condensed negative map (the few cuts that teach something; link the ledgers for the rest).
7. Short collaboration/methods section: frontier models over several months (seats changed models),
   the cold-audit rule, one or two technical lessons that are real findings.
8. Availability: links to receipts, tooling and Lean modules (R-LINK).

**Cut:** census-pass history and its table, cost projections and the "price of certainty"/replay-plan
material, capacity-grid gap bookkeeping (1,288 slots, 34 outside, auditor counts) except one sentence if
needed, overlapping evidence/trust tables, repeated gap lists, superseded plans. Dollar figures at most
one sentence (total cloud cost for the H1 checks ≈ $225).

**Fix the v6 review majors:** (a) the compiled `LRAT.check` sentence must note it is redundant for the
30 cube leaves (cake_lpr also checked them) and that the project's `lratreplay` parsing front end is
unverified; (b) the hardest row's leaves were solved with a macOS CaDiCaL build and checked from files by
cake_lpr build `d23c413b…` — say so accurately, not "the same way"; (c) six largest leaves have length
but no sha256 receipt; (d) no "1,160 instances of a two-solver census" phrasing that excludes the cube
row; (e) cite the Lean LRAT checker if referenced; keep `heule2018schur`, `tan2021cakelpr`.

All earlier scope rules still hold: never "theorem"/"proof"/"decided" for Result A; cake_lpr is outside
Lean; nothing claimed about Erdős 85 itself; A-REG a hypothesis with a rival; R-AUD; R-LINK; authorship
and contributions per the Authorship amendment.

## Amendment R-BRIDGE (2026-10-06, after v7; resolves the v7 reviser's scope tensions 1 and 3)

**H1 bridge (supersedes earlier "H1 semantic bridge / row-to-stratum assembly open" wording).** Lean
already proves `orderFortyNineStratumExcluded_one_of_capacityInventory_checked`
(`proofs/Proofs/Erdos85OneHighV2CapacityCover.lean`): if each of the 13,351 capacity tables satisfies
`OneHighFamilyV2CheckedUnsat`, the H1 stratum is excluded. Its axioms (receipt
`refs/H1_COVER_AXIOMS_20261006.txt`, public path
`research/problems/erdos-85-wip-01/h1_cert_pilot_20261001/H1_COVER_AXIOMS_20261006.txt`): the three
standard axioms plus 23 `native_decide` axioms from finite enumeration checks; no `sorryAx`. So for H1
what remains open in Lean is exactly two things: (i) the external certificate checks are not admitted
into Lean as `OneHighFamilyV2CheckedUnsat` facts; (ii) that each checked CNF file is the Lean formula
rests on the compiled emitter `v2cnf` (a Lean program, compiled), not on a kernel proof. Name the cover
theorem, its `native_decide` dependence, and these two items in the status table; do not describe the
H1 reduction itself as open.

**Transcript.** The collaboration room transcript is public at https://rjwalters.info/rooms/erdos-85;
R-LINK's "room transcript … not published" no longer applies to it (the S3 certificate buckets and the
artifact volume are still described as not published, except the bank proofs and checker kit once the
public checker is released — see CHECKING.md when it exists).

## Amendment R-V8 (2026-10-07; governs v8, the last iteration under the cap — fixes the v7 review)

**1. Uniform checker (new evidence).** All 96 historical certificates were re-checked by cake_lpr
(refs `h1_cert_historical96_cake_lpr_receipts.jsonl`; public path
`research/problems/erdos-85-wip-01/h1_cert_full_20261001/receipts/historical96_cake_lpr_receipts.jsonl`).
So **cake_lpr checked every one of the 13,351 H1 orbits** (12,094 bank + 1,160 census + 96 historical,
and the hardest orbit via its 36 cube leaves + the Lean composition lemma). Lean's compiled `LRAT.check`
is now only a redundant cross-check (50 historical + 30 leaves) — mention it at most once, or drop it;
the "formally verified checker" headline no longer needs the `lratreplay` qualification.

**2. Close prior work (the v7 critical flag).** Cite and position against `heule2024hexagon`
(Heule & Scheucher, TACAS 2024: empty-hexagon number, cube-and-conquer, cake_lpr-checked proof) and
`subercaseaux2024hexagonlean` (Subercaseaux et al., ITP 2024: Lean verification of that result's
encoding, composed with the cake_lpr check). Both are in the thread refs.bib (DOIs resolved via
Crossref/DataCite). Be precise and fair: theirs is the closest precedent and is STRONGER on encoding
faithfulness (the encoding is verified in Lean); ours links the checked CNF to the Lean formula only
through a compiled Lean emitter. What is distinct here: scale (13,351 formulas, ~28 TB) inside a
whole-stratum Lean reduction, check-then-discard with hash-only receipts and byte-identical
regeneration, re-validation of an archived 22.55 TB certificate bank, and a public checker anyone can
run. Also re-cite `moura2021lean4` and `mathlib2020` (dropped in v7).

**3. R-BRIDGE fixes.** The H1 cover theorem's axioms ARE printed (refs `H1_COVER_AXIOMS_20261006.txt`:
3 standard + 23 native_decide, no sorryAx); link it; do not say "not in the cold axiom audit". Every
H1 open-item statement (status table, text, abstract) must name both items: (i) external checks not
admitted into Lean; (ii) checked-file = Lean formula rests on the compiled emitter.

**4. Public checker (now live).** A third party can re-check H1 on their own AWS machine: public AMI
`ami-05697724475f2e748` (us-east-1), the `e85-check` tool, the checker kit and the 12,094 bank proofs in
a Requester Pays bucket, and the guide `research/problems/erdos-85-wip-01/CHECKING.md` (link via
\repofile). This updates R-LINK: the bank proofs and the checker kit ARE published (Requester Pays);
the rest of the certificate bucket and the artifact volume are not. Put this in Availability and in one
sentence of §3. State it as a fact for readers (no governance language).

**5. v7 minors.** Name the checker used for the H3 proofs (from its receipt; if the receipt does not say,
say so); soften "none of these steps is a search problem"; abstract ≤ 1,900 characters (arXiv limit
1,920); Table 1 historical row gets its size (≈0.103 TB); drop or properly source the "roughly ten times"
memory factor; point f(15)=f(16)=5 to the explicit witness graph in Lean; keep ~10 pp main text.


## Amendment R-H3 (2026-10-07)

The claim above is corrected: no SAT verdict or LRAT proof exists for either H3 cell formula
(refs/H3_EVIDENCE_AUDIT_20261007.md). H3 rests on the reviewed paper argument with exhaustively replayed
searches (refs/Q7_H3_PROFILE_EXCLUSION_20260910.md, review 1685), and its two cell exclusions are open
hypotheses in Lean. The R-V8 minor asking to name the H3 checker is withdrawn: there is no checker to name.


## Amendment R-TITLE (2026-10-07)

Operator decision: title shortened to "A Drop at Forty-Nine in Erdős Problem 85". The drop leads; the uniform reduction (Theorem B) stays in the abstract and body.
