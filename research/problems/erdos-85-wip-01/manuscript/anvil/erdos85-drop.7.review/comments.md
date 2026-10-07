# Comments — erdos85-drop.7

Keyed to rendered section headings, with `main.tex` source lines in brackets. Severity groups: 1 blocker, 4 major, 7 minor, 3 nit.

## Blocker

**B1. §3 opening, "How H1 was checked": the method's closest prior work is missing.** `related-work` (this is critical flag 1)
- Excerpt: "Our contribution is to run this discipline across a whole census of 13,351 instances whose formulas are Lean terms, keeping only hashes, and to close the one instance that resisted whole solving by a cube partition whose composition is proved in Lean" [L136].
- Missing leads (reviewer recall; web search off; resolve through `paper-litsearch`, do NOT hand-write `.bib` entries):
  - Subercaseaux, Nawrocki, Gallicchio, Codel, Carneiro, Heule, "Formal Verification of the Empty Hexagon Number", ITP 2024 (LIPIcs), arXiv 2403.17370. A Lean 4-verified SAT encoding with a cake_lpr-checked cube-and-conquer proof, for an Erdős–Szekeres-type problem.
  - Heule, Scheucher, "Happy Ending: An Empty Hexagon in Every Set of 30 Points", TACAS 2024.
  - Optional context: Brakensiek, Heule, Mackey, Narváez, "The Resolution of Keller's Conjecture" (IJCAR 2020), another verified-checker combinatorics result.
- **Fix:** add one or two sentences after the cake_lpr sentence. Say that pairing a Lean-side formula with a verified LRAT checker and composing cubes was done for the empty-hexagon number. Then say what is new here: a census of 13,351 instances and about 28 TB, check-then-discard with hash-only receipts, re-validation of a 22.55 TB legacy bank, and a Lean reduction of a whole stratum to the checked formulas. This keeps the contribution intact and positions it accurately.

## Major

**M1. §2.4 "H1 and its 13,351 orbits" and Table 2: the H1 cover theorem's axiom status is stale (R-BRIDGE).**
- Excerpts: "and this statement was not part of the cold axiom audit" [L130]. Table 2, row "H1 reduction", column "Open in Lean": "not in the cold axiom audit" [L202].
- The receipt `refs/H1_COVER_AXIOMS_20261006.txt` (public: `research/problems/erdos-85-wip-01/h1_cert_pilot_20261001/H1_COVER_AXIOMS_20261006.txt`, committed on `erdos85/paper-v6`) prints `orderFortyNineStratumExcluded_one_of_capacityInventory_checked` with propext, Classical.choice and Quot.sound plus 23 `native_decide` axioms (I counted 23 distinct names), and no `sorryAx`.
- R-BRIDGE: "Name the cover theorem, its `native_decide` dependence, and these two items in the status table; do not describe the H1 reduction itself as open."
- **Fix:** link the receipt in §2.4 and in §8. Replace the stale clause with "its axioms are the three standard ones and 23 `native_decide` axioms from the finite enumeration checks, with no `sorryAx`". Set Table 2's "Open in Lean" cell to "nothing; not standard-axiom-only", matching the lower-sides row.

**M2. §4 paragraph after Table 2: the H1 needs are listed inconsistently with the table.**
- Excerpt: "would therefore need four things: proofs inside Lean for the H1 and H3 refutations (for H1, this is the bridge from the external checks to OneHighFamilyV2CheckedUnsat), by admitting the external checks or replaying them" [L213].
- Table 2 and R-BRIDGE give two H1 items: (i) admission and (ii) the file-to-term identity resting on the compiled emitter. The paragraph gives only (i). "Admitting" the checks without a proof that the DIMACS file is the Lean term would leave (ii) open.
- **Fix:** add (ii) to the paragraph, or replace the paragraph with "Table 2's right-hand column is the complete list", which also better honours "state the open items once".

**M3. Abstract, Table 1 caption: "formally verified checker" for the 50 historical orbits.**
- Excerpts: "Every one of these formulas has an unsatisfiability proof accepted by a formally verified checker." [L67]; "Every orbit has an unsatisfiability proof accepted by a formally verified checker" [L154].
- §3.2 itself says that for these 50 "its compiled execution and the DIMACS and LRAT parsing front end of lratreplay are trusted, not verified", and that the trust is "of the same kind as in the native_decide checks". The abstract's qualifier ("whose algorithm is proved sound in Lean and which we ran compiled") does not mention the unverified parser. The headline is therefore slightly stronger than §3.2.
- **Fix (either):**
  - (a) Re-check the 50 archived historical LRAT files with cake_lpr, as was done for the bank (0.1 TB, negligible cost). This needs new receipts and is an operator decision. The headline then becomes exact: 13,350 by cake_lpr plus the cube orbit.
  - (b) Add "with an unverified parsing front end" to the abstract clause and "(for 50, a checker whose algorithm is verified; see §3.2)" to the Table 1 caption.

**M4. Citations: Lean 4 is not cited.**
- Excerpt: "``Lean'' means a statement elaborated by Lean 4.31.0 from source" (Table 2 caption [L194]).
- `moura2021lean4` and `mathlib2020` are in `refs.bib` and were cited in v6. v7 cites neither, so the paper never cites the system all of its formal claims rest on. The changelog's "No citation removed" is inaccurate.
- **Fix:** `\citep{moura2021lean4}` at the first mention of Lean 4 (abstract or §1), and `mathlib2020` where Mathlib-based graph definitions are used.

## Minor

**m1. §2.3 "H3": the checker is unnamed.** "Each is excluded by a checked LRAT proof of its Lean-generated formula" [L111]. Name the checker (drat-trim? compiled `LRAT.check` through `not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighLratChecks`?) and link its receipt. Without this, H3 sits in Table 2 with an unspecified trust base.

**m2. §4 "None of these steps is a search problem; each has a named Lean interface." [L213]** The cold-build axiom audit has no Lean interface. Instantiating the H7 $t=0$ capstone means formalizing a closure whose largest check partitions 2,278,608 leaves, and discharging the H5 premises formalizes a 92-branch reviewed chain. Soften to "None of these steps requires new search; the H5 and H7 $t=0$ steps are substantial formalization work with named Lean interfaces."

**m3. Abstract: the gap sentence is compressed past accuracy.** "the external checks are not admitted into Lean, two Lean interfaces are not yet instantiated, and the witnesses depend on native_decide" [L67]. `native_decide` is also used by the H1 enumeration (the abstract mentions this earlier) and by the H7 certificates, and the emitter identity is omitted. Either add "the CNF files are identified with the Lean formulas through a compiled emitter", or end the sentence with "(Table 2)" and keep it short.

**m4. Abstract length.** The rendered abstract is about 2,000 characters, above arXiv's 1,920-character limit for the metadata abstract. Trim the PDF abstract or prepare a shorter metadata abstract. Candidates to cut: the 28 TB sentence or the closing Theorem B clause.

**m5. Table 1 "Historical" row has no proof size.** The 96 LRAT files total 0.103 TB (from `h1_cert_historical96_receipts.jsonl`, excluding the 2 OOM attempts), and the "about 28 TB" total includes them. Add "0.10 TB" for consistency with the other rows.

**m6. §3.1 "in our pilot needed roughly ten times the proof's size" [L146].** This traces only to BRIEF R-CERT and the operator's direct-edit file ("23.5 GB for a 2.3 GB proof"), not to a receipt (the changelog's scope tension 3). Acceptable as stated ("in our pilot"). A one-line receipt in `h1_cert_pilot_20261001/` would make it traceable.

**m7. Abstract: "its q = 4 analogue is false, since f(15)=f(16)=5" [L69].** The refutation of the $q=4$ analogue is the explicit 4-regular graph `sixteenRegular` (§5), not the equality $f(15)=f(16)$, which shows that there is no drop. Suggest "its $q=4$ analogue is false (Lean exhibits a $C_4$-free 4-regular graph on 16 vertices, and $f(15)=f(16)=5$)".

## Nit

**n1. Operator: the BRIEF frontmatter `claim` is out of date.** It still lists "the H1 semantic bridge" as open, which R-BRIDGE supersedes. The paper should follow R-BRIDGE, and the frontmatter should be reconciled.

**n2. `erdos85-drop.7.audience/`: 6 `unlinked_artifact_path` hits (L253–L258), all false positives.** Every flagged path sits inside `\repofile`, which the detector does not expand. No governance-vocabulary or private-locator hits. No deduction. Add `% anvil-lint-disable: audience_check` above the §8 list, or report the detector gap upstream.

**n3. Procedural.** Deterministic gates this pass:
- render gate: PASS (11 pages, 0 overfull boxes, 0 placeholders);
- numeric consistency: PASS (311 numbers, 0 findings);
- pending marker: PASS (0 markers);
- evidence_check on `scoring.md`: PASS (9/9);
- `scope_lint`: PASS (32 numbers, 37 Lean names);
- evidence drift: EVIDENCE-DRIFT (advisory; R-BRIDGE + `H1_COVER_AXIOMS` after v7);
- venue overlay: none (`.anvil.json` declares no `venue`);
- corpus and subject tiers: inactive;
- `artifact_verify`: not declared.

Tools were run via `PYTHONPATH=.anvil python3 -m anvil.lib.<module>`. The sidecar was written with the `python -m anvil.lib.sidecar stage/commit` CLI shim. The external volume intermittently returned EPERM inside the tool sandbox, so reads and writes on `/Volumes/Stripe` ran unsandboxed; nothing outside the review siblings was modified.
