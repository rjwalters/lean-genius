# Findings — erdos85-drop.10

## 1. Status sentences: paper vs. source and receipts

Lean source was read at the pinned commit `1d0772cd825462f5230f224c2110231c6483d5e4`.

| Location | Paper says | Source / receipt says | Match |
|---|---|---|---|
| Abstract L66, §1 L87 | upper side a Lean theorem conditional on two UNSAT hypotheses, not admitted into Lean | `Erdos85OrderFortyNineCapstoneH3.lean`: hypotheses `hOne`, `depth`, `hSeven`; docstring "not an unconditional Lean proof" | yes |
| Abstract L66 | "into four strata" | §2.2 L97 and `orderFortyNine_card_high_eq_one_or_three_or_five_or_seven_or_nine`: five values, h=9 refuted | **no (m1)** |
| Result A L78 | h_H7: 28 cover + 377,776 leaf formulas | `SevenHighT0CanonicalHsbEvidence depth ...` over `SevenHighT0Hsb.leaves depth mask`; campaign depth 3 | yes, depth unstated (m2) |
| §2.2 L97 | h=9: no external hypothesis, 18 certificates by `native_decide` | `false_of_orderFortyNine_nine_high` imports 18 `T2/T3/T4 Rep*Certificate` modules, each `include_str "Certificates"/...` (in repo) | yes |
| §2.2 L111 | 601 / 607 / 604; 891 hash-pinned imports; not a cold rebuild | `RELEASE_ASSEMBLY_README_20261011.md` "Completed validation" | yes |
| §2.3 H3 L117 | 408 parts (24 + 384), three standard + 408 native | `H3_STRATUM_INTEGRATION_README_20261008.md` L31, L173 (411 total) | yes |
| §2.3 H5 L119 | 40 search parts + graph-cover and cardinality checks | `H5_TERMINAL_REVIEW_README_20261008.md`: 61 = 3 + 40 + 18 | yes (n4: count omitted) |
| §2.3 H7 L121 | t>=1 packed certificate files not in the repository; not replayed | 13 modules `include_str "/Volumes/Stripe/.../h7_t*_rep*.packed.lz4p7"`; capstone imports them via `HsbStratumCapstone -> MixedCapstone -> SplitTerminal -> EmptyCubeTerminal -> CanonicalTerminal -> SevenHighCertificates` | fact yes; consequence unstated (**M1**) |
| §2.3 L123 | 43 classes; 15 counting by kernel `decide`; 28 structural | `Erdos85OrderFortyNineSevenHighT0EmptyCountingCore.lean`: `sevenHighT0CountingCertificates_hold := by decide`; 28-entry `sevenHighT0StructuralCubes`; 19 + 15 + 7 + 2 | yes |
| §2.3 L130 | `orderFortyNineStratumExcluded_seven_of_structuralHsbEvidence` | `...HsbStratumCapstone.lean` L25 | yes |
| §2.3 L132 | split composed by `sevenHighT0CanonicalHsbLeafChecked_of_split`; generator untrusted | `...HsbLeafSplit.lean` L40: arbitrary `blocking` list; the checked sub-cover vouches for it | yes |
| §2.3 L132 | base cube printed by Lean term; hsb/cover lines by native generator matched byte for byte | H7 README §1: `EmitCube.lean` via interpreted `lean --run`; `hsb_lean_identity.json` | yes (abstract's "compiled emitter" loose for H7, m4) |
| §2.3 L132 | 4,269/706 CPU-h, ~20.2 TB (leaf + split); 4,711/740 (all runs) | `h7_collected_summary_20261011.json` totals; `h7_campaign_totals_20261011.json` | yes |
| §2.3 L132 | 232 residual leaves; 257 split formulas | `residual-pass-manifest.jsonl` 232 rows; `split-pass-manifest.jsonl` 257 rows | yes |
| §2.3 L132 | about $215 of cloud compute | no linked receipt states a spend | **untraced (m3)** |
| §2.3 L132 | collector re-run independently | release README "Receipt review": fresh collector run; 29 tables match | yes |
| §3 L153 | "23 for H1, 598 for the whole upper side" | `H1_COVER_AXIOMS`; release README | yes |
| Table 2 L226 | upper side: 3 + 598, no `sorryAx`; not a cold rebuild | release README | yes |
| §4 L232 | right-hand column is "the complete list" | omits publication of the 13 t>=1 certificate files needed to compile the capstone | **no (M1)** |
| §8 L277 | strata names in `STRATA_AND_SMALL_ORDERS_20260928.md` | at pinned commit: H5 "reviewed paper/computation cover"; H7 capstone "not instantiated" | **stale (M2)** |

## 2. Overclaim sweep (every "theorem" / "Lean proves" / "excluded" in the body)

- "theorem" applied to Result A appears only as: "a Lean theorem conditional on two explicit unsatisfiability hypotheses" (L66); "the Lean theorem ... whose only hypotheses are" (L78); "a single Lean theorem whose only hypotheses are the two families of checked formulas" (L85); "Result A is not an unconditional theorem of Lean" (L87). Every one carries its condition in the same sentence.
- "Lean excludes ... outright" (L85, L104) is used only for H3 and H5, which are discharged in Lean with `native_decide`. Table 2 marks both "not standard-axiom-only".
- H1 and H7 (t=0) are never said to be excluded in Lean. Both are "reduced" to unsatisfiability hypotheses (L66, L104, Table 2).
- The external checks are always "outside Lean" / "not admitted into Lean" (L66, L87, L203, Table 2 L220/L225, L232).
- **Conflict with BRIEF (M3):** the unamended hard rule says "Never call Result A a theorem". The `claim` says "not a Lean theorem". v10 needs a BRIEF amendment, or the abstract reword given in `comments.md`.

## 3. Cross-section observations

- **Scope of the change.** The v10 changes are confined to what `changelog.md` lists. `refs.bib` is byte-identical to v9.
- **Trust base.** The paper states the H1 and H7 trust bases in parallel, and §3.4 notes the emitter difference and that there is no public H7 checker image. But the H7 cake_lpr binary (`4d47ffdd...`, the builder build of commit `a36874a8`) is not the H1 Graviton build (`95b64883...`), so "the same trusted base" (L203) holds at the commit level, not the binary level. Nit.
- **Linked receipts.** All 64 `\repofile` targets resolve at the pinned commit. The weak points are stale content (M2) and missing content (m3, m6), not dangling links.
- **Private locators in linked source.** The 13 H7 t>=1 certificate modules carry private absolute paths in public, linked source. This is not a paper-text audience defect, but it is visible to any reader who opens the Lean source. Same root cause as M1.
- **Stale BRIEF claim.** The BRIEF's "Strongest honest claim" and `claim` describe the pre-v10 state (H3/H5/H7 open in Lean). An `R-V10` amendment would realign the audit baseline (M3).

(No rubric version transition: the prior review `erdos85-drop.9.review/` was scored against `anvil-pub-v2`, the same rubric.)
