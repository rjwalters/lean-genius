# Verdict — erdos85-drop.7

**Total: 35 / 44** (prior iteration `erdos85-drop.6.review/`: 34 / 44)

**Decision: `advance: false`**. The total meets the threshold, but one blocking critical flag is raised. The pending-marker gate passed (no `[PENDING …]` marker). This is iteration 7 of `max_iterations: 8`, so one revise pass remains.

## Re-evaluation of the v6 critical flag

**`scope_overclaim_h1_certificate_check`: resolved by evidence.** I recomputed the partition from the receipts in `refs/`:

- The bank TSV has 12,094 distinct tags, all VERIFIED, every heap 8,000 MB. Totals: 22,554,276,624,018 LRAT bytes, 6,285,686,522,598 gz bytes, a maximum of 26,521,722,365 bytes and 408.5 summed check-hours. Orbit `0051c0f06f824a2e` has no producer ledger.
- The census TSV has 1,160 ids. Historical: 96 tags, 50 `LRAT_CHECK_ACCEPTED` and 46 `CAKE_LPR_VERIFIED`, plus 2 superseded OOM attempts. The cube orbit is `81494a6ef36d3ec9`.
- The four sets are pairwise disjoint, and their union is exactly 13,351 tags. The bank summary records `coverage.uncovered: 0`.

The paper now states H1 throughout as 13,351 capacity orbits (§2.4, Table 1). The 34 "outside" slots are moot, since they lie in the verified bank set (changelog, checked against `h1-gap1288-audit.json`). The v6 majors M1 (`LRAT.check` qualification), M2 (hardest-orbit receipts) and M3 (34 slots) are also resolved.

## Critical flags

### 1. `close_prior_work_ignored`: the H1 method is positioned without its closest precedent

R-SIMPLE asks the paper to present the H1 check as "a genuine methodological contribution", and v7 does: "Our contribution is to run this discipline across a whole census of 13,351 instances whose formulas are Lean terms, keeping only hashes, and to close the one instance that resisted whole solving by a cube partition whose composition is proved in Lean" (§3 [L136]). The closest prior work for this combination is not cited or engaged:

- Subercaseaux, Nawrocki, Gallicchio, Codel, Carneiro and Heule, "Formal Verification of the Empty Hexagon Number" (ITP 2024; arXiv 2403.17370). As I recall it, they verified a SAT encoding in Lean 4 and checked the resulting cube-and-conquer UNSAT proof with cake_lpr, for an Erdős–Szekeres-type problem.
- The underlying SAT result, Heule and Scheucher, "Happy ending: an empty hexagon in every set of 30 points" (TACAS 2024).

The paper's declared audience includes formal-methods readers. To them this pairing (Lean-side formula, cake_lpr check, cube composition) is the obvious precedent. Without it, §3 reads as if the pairing itself were new.

This is reviewer recall; the thread has `web_search: false`. The reviser must not add the entries by hand (BRIEF: "do not invent" citations). Run `paper-litsearch` to resolve them, then add one or two sentences to the §3 opening saying what is inherited (Lean-side formula, verified LRAT checker, cube composition) and what is new here:

- census scale (13,351 instances, about 28 TB);
- check-then-discard with hash-only receipts and byte-identical regeneration;
- re-validation of a pre-existing proof bank;
- a Lean reduction of a whole stratum to the checked formulas.

The fix does not shrink the contribution. The new parts remain new. Without the citation, though, a formal-methods referee would read §3 as unaware of its nearest neighbour.

## Brief compliance (R-SIMPLE, R-BRIDGE and the standing scope rules)

- **Scope rules held.**
  - Result A is never a theorem, proof or "decided"; it is a `resultA` environment with "Result A is not a theorem of Lean" (§1).
  - "Formally verified checker" is applied only to H1. H3 is "checked LRAT proofs", H7 $t\ge1$ is "checked inside Lean by `native_decide`", and H5 and H7 $t=0$ are reviewed arguments.
  - cake_lpr is placed outside Lean: "cake_lpr's guarantee is a HOL4 theorem about its compiled binary, not a Lean kernel check" (§3.5).
  - `LRAT.check` is qualified: the soundness theorem is named, compiled execution and `lratreplay` parsing are trusted (§3.2), and it is "a redundant second check, not part of the trust base" for the 30 leaves (§3.3).
  - Nothing is claimed about Erdős 85 ("One drop is compatible with either answer").
  - A-REG is "a hypothesis with a stated rival".
  - R-AUD: the audience scan found 0 governance and 0 private-locator hits, and a manual read found no authorization, budget or goal language.
  - R-LINK: 44 distinct `\repofile` targets. 39 are on `origin/erdos85/integration`; 5 are on `erdos85/paper-v6` (the bank-check dir and its 3 receipts, and `COMPOSITION_AXIOMS_20261006.txt`) and land with the merge, which is not a defect.
  - `scope_lint`: PASS (32 numbers, 37 Lean names).
- **R-BRIDGE mismatches** (amendment written after v7; major, not critical):
  1. §2.4 [L130] and Table 2 [L202] still say the H1 cover theorem "was not part of the cold axiom audit" and list that as the H1-reduction row's open item. Under R-BRIDGE the receipt `H1_COVER_AXIOMS_20261006.txt` exists and prints `orderFortyNineStratumExcluded_one_of_capacityInventory_checked` with the three standard axioms plus 23 `native_decide` axioms and no `sorryAx`. The paper should link that receipt, name the 23 `native_decide` axioms, and set the row's "Open in Lean" to "nothing". R-BRIDGE says "do not describe the H1 reduction itself as open".
  2. Table 2's H1-orbits row names both R-BRIDGE items: "admitting the checks into Lean; file-to-term identity rests on the compiled emitter". The post-table paragraph [L213] and the abstract name only the first. The paragraph should list both.
  3. Transcript: consistent. The room URL is linked in §7, as R-BRIDGE now allows.

## Dimension summary

| # | Dimension | Weight | v6 | v7 |
|---|---|---|---|---|
| 1 | Rigor of method / argument | 6 | 5 | 5 |
| 2 | Evidence sufficiency | 6 | 4 | 5 |
| 3 | Clarity of contribution | 5 | 4 | 4 |
| 4 | Related-work positioning | 5 | 4 | 2 |
| 5 | Reproducibility | 5 | 4 | 4 |
| 6 | Figure & table quality | 4 | 3 | 3 |
| 7 | Prose & structural quality | 4 | 3 | 4 |
| 8 | Citation hygiene | 5 | 4 | 4 |
| 9 | Rhetorical economy | 4 | 3 | 4 |
| | **Total** | **44** | **34** | **35** |

The D4 drop reflects the new flag. v6's D4 4/5 did not check this gap; v7's positioning is not worse than v6's, but v7 now foregrounds the method, as R-SIMPLE requires, so the gap matters more. Full justifications are in `scoring.md`. Line items are in `comments.md`: 1 blocker, 4 major, 7 minor, 3 nit.

## Top 3 revision priorities

1. **Position the method (flag 1).** Run `paper-litsearch` for the Lean empty-hexagon verification (Subercaseaux et al., ITP 2024) and Heule–Scheucher 2024. Add one or two sentences to the §3 opening that credit the inherited pairing and keep the census-scale, check-then-discard, bank re-validation and stratum-reduction parts as the new contribution. Restore `\citep{moura2021lean4}` (and `mathlib2020` if Mathlib is used) at the first mention of Lean 4.
2. **Apply R-BRIDGE.** In §2.4, replace "this statement was not part of the cold axiom audit" with the receipt: the three standard axioms plus 23 `native_decide` axioms, no `sorryAx`, linked as `\repofile{\rp/h1_cert_pilot_20261001/H1_COVER_AXIOMS_20261006.txt}{…}`. Set Table 2's H1-reduction "Open in Lean" to "nothing; 23 `native_decide` axioms". Make the post-table paragraph list both H1 items, admission and emitter identity.
3. **Make the headline exact for the 50 historical orbits.** Either re-check the 50 archived historical LRAT files with cake_lpr, as was done for the other 13,300 (about 0.1 TB, negligible cost; this needs new receipts and is an operator decision), so that the headline becomes "13,350 by cake_lpr plus the cube orbit". Or keep the current split and add "through an unverified parser" to the abstract's `LRAT.check` clause and to the Table 1 caption. Also name the checker of the H3 LRAT proofs.

## Evidence drift (advisory only)

`anvil.lib.evidence_drift` reports **EVIDENCE-DRIFT**: both `BRIEF.md` and `refs/**` changed after v7 was written (R-BRIDGE amendment; `H1_COVER_AXIOMS_20261006.txt`). This is advisory only. It does not change `advance`, any dimension score, or the terminal-state gate. This review re-weighed v7 against the current BRIEF and refs, and the R-BRIDGE mismatches above are the result.
