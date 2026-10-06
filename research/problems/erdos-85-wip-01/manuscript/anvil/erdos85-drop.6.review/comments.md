# Comments — erdos85-drop.6

Keyed to rendered section headings, with `main.tex` source lines in brackets. Severity groups: 1 blocker, 3 major, 7 minor, 4 nit.

## Blocker

**B1. Abstract, §1 Result A, §4.4, §4.5, Table 5, §6, §7: H1 is not 1,257 instances, and the October check did not cover all of H1.** This is critical flag 1.
- Excerpts:
  - "The fourth, the one-high stratum H1, consists of 1,257 SAT instances, and every one of them now has an unsatisfiability proof accepted, outside Lean, by a formally verified checker" [L68]
  - "Every H1 instance now carries a checked certificate" [L268]
  - "the whole stratum was certificate-checked in one run, and the solvers left the H1 trust base" [L344]
  - "the superseded September plan for an in-Lean replay of the certificate bank" [L362]
- What the receipts say:
  - The H1 closure runs over the 13,351-slot capacity universe, which the paper itself cites at [L232].
  - The 1,257 Phase B tags are that universe minus 11,954 + 140 rows that were screened out because the 2026-08 bank held a certificate object for each. Those objects were "not downloaded or kernel-checked" (`PHASE_B_H1_H3_INVENTORY_20260910.md`).
  - The October README scopes itself to "Every H1 residual root".
- About 12,000 H1 instances therefore still rest only on producer-side drat-trim verification from 2026-08. The paper re-checked the 96 historical rows of exactly this class, which shows it regards that level as insufficient.
- v5 disclosed the gap in §6 and in a Table 4 row; v6 removed both.
- **Fix:**
  - Say H1's closure is over 13,351 capacity slots and that the October check covered the 1,257-row Phase B set.
  - Say the rest of H1 rests on the 2026-08 bank, verified by drat-trim at production and not re-validated.
  - Restore the Table 4 bank row (12,019 ready inputs; receipted).
  - Add "re-validating the 2026-08 certificate bank" to the gap list in the abstract, §1, §4 opening, §4.3 and §6.
  - Replace "superseded" at [L362] with "not run".
  - Rephrase "every H1 instance / whole stratum / left the H1 trust base" to the Phase B residual.

## Major

**M1. §4.4 "Where the residual trust sits" and §2 "The trust root": the compiled `LRAT.check` trust statement is incomplete and, for the leaves, points the wrong way.**
- Excerpt: "for 50 historical certificates and 30 of the 36 cube leaves, in Lean's compiled LRAT.check, whose soundness is a Lean theorem but whose execution trusts the compiler" [L264].
- Problems:
  - (a) The 30 leaves were also accepted by cake_lpr, so `LRAT.check` adds redundancy there, not trust. Only the 50 historical certificates depend on it alone.
  - (b) The checks ran through the project's `lratreplay` executable (`proofs/lakefile.toml` → `Proofs.Erdos85LratRuntime`). Its DIMACS and LRAT parsing is unverified, whereas cake_lpr's theorem covers parsing. The soundness theorem (`Std.Tactic.BVDecide.LRAT.check_sound`, present in the pinned v4.31.0 source) is real, but the paper neither names nor links it.
  - (c) This is the same compiler trust as the H7 `native_decide` LRAT checks that the paper lists as a gap. Say so, so the reader can calibrate.
- **Fix:** one sentence in §4.4, plus `\repofile` links to the runtime module and the theorem name. Optionally, the reader-facing qualifier "(algorithm proved sound in Lean; compiled execution and file parsing trusted)" at the first mention in the abstract or Table 5.

**M2. §1 and §4.5 "The hardest row", Table 5 caption: the hardest-row statements do not match their receipts.**
- Excerpts: "the 36 cubes of the hardest row were checked the same way" [L87]; "each receipt keeps the proof's sha256 and length" (Table 5 caption [L278]).
- What the receipts show:
  - The leaves were solved by `/opt/homebrew/bin/cadical`, a macOS build and not the pinned Linux arm64 binary.
  - The proofs were written to `proof.lrat` and checked afterwards, not streamed.
  - The cake_lpr leaf receipts carry `checker_sha256 d23c413b…`, a build the paper never identifies (the census build is `95b64883…`).
  - The six largest leaves, the ones not checked by `LRAT.check`, have no proof sha256 in any receipt, only `lrat_bytes`.
- **Fix:** say the leaves were solved with the macOS CaDiCaL build and checked from files by cake_lpr build `d23c413b…`. Restrict the caption's sha256 claim to the census and historical rows, or state that the leaf receipts keep length only (and sha256 for the 30 `LRAT.check` leaves).

**M3. §4.2 "H1: the two-solver census", Table 4 "H1 capacity-grid slots": the 34 outside slots.**
- Excerpt: "the 34 slots outside the frozen source have verdicts only and are not among the 1,257 H1 instances" [L232].
- `PAUSE_HANDOFF_20260927.md` says "The capacity-grid framing (1,288 gap slots) additionally needs the 34 outside-frozen slots." The paper keeps them out of "every H1 instance", as R-CERT requires. It never says whether H1's exclusion needs them, and if it does, the remaining verdict-only rows belong in the gap list.
- **Fix:** one sentence saying which framing the Lean reduction `orderFortyNineStratumExcluded_one_of_pureFamilies` consumes. If the 34 are needed, name them among the open items. Fold this into the B1 rewrite.

## Minor

**m1. Title and §6 heading: "A Certificate-Checked Drop".** H5 and the H7 $t=0$ cell carry no certificates; they are "reviewed arguments with independently checked computation". The Result A statement says this correctly: "Certificate-checked computation and reviewed arguments together support" [L180]. The title is fixed by the BRIEF (operator decision), so this is for the operator. One option is a title like "…a Certificate-Checked Census…"; another is to accept the shorthand knowingly.

**m2. §4.6 "Why the whole-instance route sufficed": the counterfactual is overgeneralized.** "so on this census splitting would have multiplied the bytes to check rather than reduced them" [L297]. This rests on one cube tree's 6.3 GB per CPU-hour against the census's 1.6. It ignores that splitting cuts CPU-hours on hard rows: for the hardest row, 7.4 CPU-hours of leaves against more than 24 hours of whole-instance solving. **Fix:** "on the one tree measured, cube proofs were denser per CPU-hour than whole-instance proofs", or drop the clause.

**m3. Abstract, sentence 5: the key sentence is hard to parse.** "…by a formally verified checker: the 1,160 instances of a two-solver census and the 36 cubes that partition the hardest instance by the CakeML-verified checker cake_lpr, the cubes composed by a standard-axiom Lean lemma, and 96 earlier certificates by cake_lpr or Lean's compiled LRAT checker." The colon list nests a participial clause inside its second item, and "by … by" repeats. **Fix:** split it into two sentences, one on the checks and one on composition and the historical rows.

**m4. §1 "Result A (computational)": the paragraph is 459 words.** It reproduces most of §4.2 (passes, preparations, core-hours) and §4.5 (the October check). **Fix:** keep the strata and the evidence class per stratum, and point to §4.2 and §4.5 for the counts.

**m5. The five-gap list is repeated near-verbatim in the abstract, §1, the §4 opening, §4.3 and §6.** R-CERT requires naming the gaps "every time the status is summarized". One canonical list (§4.3) plus a short named enumeration elsewhere satisfies the rule at lower cost. Update all five instances when B1 adds the bank item.

**m6. §2 and §4.5: citations.** `heule2018schur` is new and is not in the thread `refs.bib` or the BRIEF (web search off). The attribution "the approach of the largest SAT-based results" [L268] to both cited papers should go to `paper-audit` for claim-support. The Lean standard-library LRAT checker has no citation or link to `check_sound` (see M1). This is tagged `related-work`: a `paper-litsearch` pass could add the Lean `bv_decide` LRAT checker reference and the closest certificate-backed combinatorics results.

**m7. Abstract: "the 1,160 instances of a two-solver census".** The census has 1,161 residual roots (1,160 whole plus 1 cube). As written, the hardest instance reads as outside the census. **Fix:** "the 1,160 whole-instance rows of a two-solver census and the 36 cubes that partition its remaining, hardest row".

## Nit

**n1. `changelog.md` (not the paper): leaf hashes.** It says "`cube_sha_ok` true for all". The public `pilot_h1_81494a_leaf_solves.jsonl` has `cube_sha_ok: true` on 31 leaves; the other 5 lack the field (they were written by `solve_leaves.py`, which refuses a mismatch). I checked all 36 cube hashes against the unpublished tree `results.json` and they all match, so the paper's "each cube CNF hash-checked against the tree" holds. Only the changelog's receipt description is loose.

**n2. `erdos85-drop.6.audience/` false positives.** All 14 `unlinked_artifact_path` hits (L357–L370) are `\repofile` links; the detector does not expand the macro. Add `% anvil-lint-disable: audience_check` above the §7 list, or report the detector gap upstream. No deduction.

**n3. BRIEF R-LINK vs §7 transcript link.** The BRIEF still lists "the room transcript database" among things that are not published. v6 links `https://rjwalters.info/rooms/erdos-85` (HTTP 200 on 2026-10-06), following the operator's direct edits. The operator should reconcile the BRIEF line.

**n4. Naming the second checker.** The paper uses "Lean's compiled LRAT checker" (abstract), "the compiled LRAT.check of Lean's standard library" (§4.5, Table 4) and "Lean's compiled LRAT.check" (§4.4). Pick one name and use it everywhere, ideally with the `Std.Tactic.BVDecide.LRAT` namespace once.
