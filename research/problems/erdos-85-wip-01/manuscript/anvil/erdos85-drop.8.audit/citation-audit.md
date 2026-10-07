# Citation audit: erdos85-drop.8

**Scope.** Every `\cite`, `\citep` and `\citet` in `erdos85-drop.8/main.tex` is enumerated below. It is a single-file paper with no `\input` or `\include`. Each key is resolved against `erdos85-drop.8/refs.bib` and then against the rendered bibliography of a fresh compile.

**Claim-support sources.**

- `erdos85-drop/refs/**`. No PDF of any cited work is on disk. The author notes in `FIRST_DROP_LITERATURE_CHECK.md` and `DRAFT.md` cover four keys.
- For the two hexagon papers only, the DOI resolver metadata: the Crossref abstract for `10.1007/978-3-031-57246-3_5` and the DataCite abstract for `10.4230/LIPIcs.ITP.2024.35`. These are the same resolvers through which R-V8 obtained the DOIs. Web search is off, and no other source was consulted.

Verdicts use the spec's four values. "partial" means the on-disk note or resolver abstract supports part of the sentence and the rest is unverified.

## Resolution summary

- 16 distinct keys are cited (22 key occurrences). 16 of 16 resolve in `refs.bib`, which has 16 entries, so none is unused.
- BibTeX reports `warning$ -- 0`.
- At the `.aux` fixpoint (xelatex pass 4) the log has 0 `Citation ... undefined` lines. `pdftotext` of the final PDF has 0 `??`, 0 `[?]` and 0 `(?)`.
- 0 unresolved keys and 0 `does-not-support` verdicts, so this file raises no critical flag.
- `erdos85-drop.8/refs.bib` differs from the thread-root `erdos85-drop/refs.bib` only in entry order and in `year = {n.d.}` / "Undated web page" annotations on the two web entries. No content diverges.

## Per-citation table

| Key | Resolved | Surrounding claim (main.tex line) | Verdict | Notes |
|---|---|---|---|---|
| `bloom-erdos85` | yes | L74: Erdős Problem 85 asks whether f(n+1) ≥ f(n) for all large n. L86: "the maintained record lists no partial result and warns that its literature list may be incomplete" | partial | `FIRST_DROP_LITERATURE_CHECK.md` §1 (checked 2026-08-25) records that the page states the problem for N ≥ 4, marks it open, says that no solution or partial solution is claimed in the comments, and warns that the literature list may be incomplete. The live page was not re-read (web off). |
| `moura2021lean4` | yes | L74: "In Lean 4" | unverified (source not on disk) | A standard system citation. Bib fields (CADE-28, LNCS 12699, 625–635, DOI) are consistent with the known record. |
| `mathlib2020` | yes | L74: "on Mathlib's simple graphs" | unverified (source not on disk) | A standard system citation. |
| `boza2024ramsey` | yes | L76: r(s)=R(C4,K_{1,s}) convention; "Boza's table gives r(41)=49 and leaves r(42)∈{49,50} open". L86: "reports no consecutive equality that yields one, though some of its entries are still ranges". L240: r(109)∈{120,121}, r(155)∈{168,169} together with Zhang et al. | partial | `FIRST_DROP_LITERATURE_CHECK.md` §2 (Boza v2, 12 June 2026) gives r(41)=49, r(42)∈{49,50}, and "no consecutive equality yielding an in-domain strict drop … some later Ramsey entries remain ranges". `DRAFT.md` L722–L727 gives the r(109)/r(155) deductions from Zhang–Chen–Cheng plus Boza. The paper's conversion "r(s) ≤ N iff f(N) ≤ N−s" and "plateau r(s)=r(s+1)=N iff drop f(N)<f(N−1)" were re-derived by hand and are correct. |
| `zhang2017polarity` | yes | L76: co-cited for the r(s) convention. L240: "With the values of Zhang–Chen–Cheng and Boza it leaves r(109)∈{120,121} and r(155)∈{168,169}" | partial | Covered only by the author note `DRAFT.md` L722–L727, which links the DOI and records the deduction. No PDF is on disk, and the bound itself is unverified. This was a carried author obligation in the v3–v5 audits. |
| `afzaly-mckay-extremal` | yes | L94: the 48-vertex witness "is not isomorphic to any of the ten graphs with 48 vertices and 168 edges in the Afzaly–McKay records"; the records "also contain 49-vertex graphs of minimum degree 6, which corroborate f(49) ≥ 7 but say nothing about the upper side" | partial | `BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt`: "PASS: witness is non-isomorphic to all 10 Afzaly--McKay archive graphs" (archive sha256 `7bc1de35…`). `FIRST_DROP_LITERATURE_CHECK.md`: the 49-vertex rows are labelled as a lower-bound collection, not an exhaustive computation, which matches "say nothing about the upper side". The 168-edge figure is from `DRAFT.md` L90. |
| `biere2024kissat` | yes | L132: "Kissat 4.0.4" | unverified (source not on disk) | A system citation for the solver. Version 4.0.4 is post-2024. Citing the competition description is conventional. |
| `biere2020cadical` | yes | L132: "then CaDiCaL 3.0.1" | unverified (source not on disk) | A system citation, version-mismatched (a 2020 competition description cited for release 3.0.1). Conventional, so recorded as a nit only (flags.md N5). |
| `wetzler2014drat` | yes | L136: "DRAT proofs are checked by drat-trim" | unverified (source not on disk) | A standard attribution, and the bib title is "DRAT-trim". |
| `cruzfilipe2017lrat` | yes | L136: "the LRAT format adds hints that let a small checker replay each step" | unverified (source not on disk) | A standard attribution. |
| `tan2021cakelpr` | yes | L136: cake_lpr is "an LRAT checker whose correctness, including file parsing, is proved in HOL4 and carried to machine code by the verified CakeML compiler" | unverified (source not on disk) | Consistent with the bib title ("Verified Propagation Redundancy Checking in CakeML") and with BRIEF R-CERT. The parsing-inclusive claim is load-bearing for the §3.4 trust boundary, and the author should confirm it against the paper. |
| `heule2016pythagorean` | yes | L136: "The largest SAT-based results in combinatorics check proofs too large to keep" | unverified (source not on disk) | A plausible lineage citation. Rendered title "boolean Pythagorean" has a lower-case b (flags.md N4). |
| `heule2018schur` | yes | L136: same sentence | unverified (source not on disk) | No DOI in the entry (optional). |
| `heule2011cube` | yes | L138: "by cube-and-conquer" | unverified (source not on disk) | A standard attribution of the technique. |
| `heule2024hexagon` | yes | L86: "the formally verified empty-hexagon theorem". L138: Heule–Scheucher "showed by cube-and-conquer that every set of 30 points in general position in the plane contains an empty convex hexagon, with the proof checked by cake_lpr" | partial | **Supported by the Crossref abstract:** "Every 30-point set in the plane in general position contains an empty hexagon"; "a search-space partitioning strategy enabling linear-time speedups even when using thousands of cores". This is consistent with cube-and-conquer, though the abstract does not use the term. **Not in the abstract:** "checked by cake_lpr". That detail rests on BRIEF R-V8 only. **Bib:** the LNCS volume is missing, and Crossref returns no volume (flags.md m4). |
| `subercaseaux2024hexagonlean` | yes | L86 as above. L138: they "verified in Lean that the SAT encoding is faithful to the geometric statement and joined that verification to the cake_lpr check". "On encoding faithfulness their result is stronger than ours: their encoding is proved correct in Lean, whereas we connect each checked CNF file to its Lean formula only through a compiled Lean emitter" | partial | **Supported by the DataCite abstract:** "we formalize and verify this result in the Lean theorem prover … a framework that connects geometric objects to propositional assignments". This supports "their encoding is proved correct in Lean". **Not in the abstract:** "joined … to the cake_lpr check", and how their DIMACS file is tied to the Lean formula. The second half of the comparison (stronger *because* our file link is a compiled emitter) therefore contrasts their encoding proof with our file link. That is the reviewer's major M1 (flags.md M1). Bib fields (LIPIcs 309, 35:1–35:19, DOI) match DataCite. |

## Uncited reference to a tool

- **`LRAT.check` (L176)**: "the compiled `LRAT.check` of Lean's standard library (via `Erdos85LratRuntime.lean`)". The module uses Lean core's `LRAT` namespace (`open LRAT`, `LRAT.Internal`; `import Std.Data.HashMap`), so the attribution to Lean's own library is accurate. However, no citation is given, and R-SIMPLE (e) asks for one if the checker is referenced. R-V8 §1 allows dropping the clause. This is the reviewer's minor m1, carried as flags.md m2.

## Receipt-support check (non-bibliographic claims)

The reviewer and this audit both checked the statements that v8 changed against the receipts in `refs/` (detail in `numerical-audit.md`). No statement contradicts a receipt:

- All 96 historical orbits are accepted by cake_lpr (build `d23c413b`).
- The H1 cover theorem's printed axioms are the 3 standard axioms plus 23 `native_decide` axioms, with no `sorryAx`.
- The four composition statements depend on `propext` and `Quot.sound` only.
- 1,157 census rows ran on Graviton and 3 on Apple silicon.
- 4 GB of heap sufficed for 1,075 rows.
- The cube leaves were solved by the macOS CaDiCaL at `/opt/homebrew/bin/cadical`, and every one of the 36 leaf CNFs was hash-checked against the tree. 31 rows carry `cube_sha_ok: true` (backfill script). For the other 5, `solve_leaves.py` refuses to solve on a mismatch.
- Proof sha256 is recorded for exactly 30 leaves, the largest of them 2.42 GB.
- The H3 receipts do not name a checker. `STRATA_AND_SMALL_ORDERS_20260928.md`, `PHASE_B_H1_H3_INVENTORY_20260910.md` and `H7_POSITIVE_TRIPLE_CELLS_…` §3 were all re-read.

## Counts

| Verdict | Keys |
|---|---|
| supports | 0 |
| partial | 6 (`bloom-erdos85`, `boza2024ramsey`, `zhang2017polarity`, `afzaly-mckay-extremal`, `heule2024hexagon`, `subercaseaux2024hexagonlean`) |
| does-not-support | 0 |
| unverified (source not on disk) | 10 |
| unresolved | 0 |
