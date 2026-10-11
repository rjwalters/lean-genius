# Verdict — erdos85-drop.11

**Total: 40 / 44** (prior iteration `erdos85-drop.10.review/`: 37 / 44)

**Decision: `advance: true`.** The total clears the 35-point threshold and no critical flag is set. The pending-marker gate passed (0 markers), so `ready: true`.

v11 is iteration 11 of `max_iterations: 8`, a direct-edit corrections pass under the same operator override as v10. It makes no new claims. This review checked each v10 review and audit finding against the v11 text and the new pin `f6daa149b807972abe1c3e669abce092a863c2bd`. No file under `proofs/` changed between the v10 pin `1d0772cd825` and this pin, so the v10 source checks of the Lean statements still hold.

## Resolution of the v10 findings

| v10 finding | Status in v11 | Evidence |
|---|---|---|
| Audit C1 / review M3: "Lean theorem" wording vs BRIEF hard rule | **Resolved** | Abstract [L66]: "Lean thus derives the upper side from two explicit unsatisfiability hypotheses"; Result A [L78]: "is derived in Lean by … from exactly two hypotheses"; §1 [L85]: "Lean derives the upper side from the two families of checked formulas alone". Every remaining "Lean theorem" near Result A is a negation (L87 ×2, L232). `pdftotext` of the shipped PDF agrees. |
| Audit C2 / review m3: unsourced "about \$215" | **Resolved** | The clause is deleted; `pdftotext` finds no "215". The only dollar sentence left is the H1 "about \$225" [L191], the BRIEF R-SIMPLE figure, which matches the receipts (\$204 census + \$20.42 bank check). |
| Review M1 / audit M1, m6: public-rebuild limitation | **Resolved (disclosed)** | §1 [L87]: "the capstone cannot be recompiled from the public repository alone, because 13 of its certificate modules read packed certificate files (about 2.57 GB) from storage that is not published"; Table 2 H7 $t\ge1$ row; post-table list [L232]. 13 files and 2,574,916,357 B match `refs/CAPSTONE_ABSOLUTE_PATH_AUDIT_20261011.json`. |
| Review M2 / audit M2: stale STRATA receipt | **Resolved** | At the pin, `STRATA_AND_SMALL_ORDERS_20260928.md` opens with "**Superseded status (banner added 2026-10-11).**" It points to the capstone, release and H7 READMEs (commit `a9ba1fc43ce`). All 64 distinct link targets exist at the pin. |
| m1 four/five strata | Resolved | "refutes one case outright, splits the rest into four strata" |
| m2 depth | Resolved | "at the symmetry-breaking depth 3 used throughout (the theorem takes the depth as a parameter)" |
| m4 / audit m3 "compiled emitter" | Resolved | "by emitters, not a kernel proof" (Abstract, L87, §3) |
| m5 / audit m4 Table 2 wording | Resolved | "refutations of all 377,804 formulas … one leaf through a 256-way split" |
| m6 / audit m5 H7 axiom receipt | Resolved | "3 standard + 91 `native_decide`" matches `h7_hsb_capstone_review_20261008/stratum.log` at the pin; the split lemma's axioms are left unasserted |
| m7 / N3 version voice | Mostly resolved | §2.2 and §2.3 fixed; "now superseded" remains at L147 and L262 (nit n1) |
| m8 logistics paragraph | Partly resolved | The paragraph is shorter, but the main text is still 11 pp (D9) |
| m9 / N5 availability label | Resolved | "Earlier reviewed arguments for the small strata, superseded …" |
| N1 233 re-run | Resolved | "232 leaves … re-run …; the one leaf that hit that cap too was split"; "233 timed-out attempts" (232 + 1) |
| N2 CaDiCaL cite | Resolved | cited at the first mention in §2.3 |
| N4 same trusted base | Resolved | "the same cake_lpr commit (a different binary build, sha256 4d47ffdd…)" |
| N6 H5 count | Resolved | "40 finite search parts and 18 graph-cover and cardinality checks … 58 native_decide axioms" (61 printed; H5 README) |
| v10 D4: H7 method not positioned against precedent | **Not addressed** | minor m1 |

## Overclaiming sweep (new edits)

The new sentences were read for overclaiming. "Lean thus derives the upper side from two explicit unsatisfiability hypotheses" (Abstract) and "from the two families of checked formulas alone" (§1) are accurate at the hypothesis level, and the `native_decide` count sits in the same sentence of the abstract. The capstone takes exactly `hOne`, `depth` and `hSeven`. The "91" for the H7 reduction and the "58" for H5 match the printed axiom outputs. No sentence promotes a cake_lpr check to a kernel check, calls H1 or H7 "proved in Lean", or claims anything about Erdős 85. **No new overclaim or inconsistency was introduced.** There is one small framing tension (minor m2): L87 says the capstone cannot be recompiled without the 13 files, but L232 files their publication under "for a fully independent audit".

## Critical flags

None. Hard scope rules re-checked:
- "Never call Result A a theorem": met.
- A-REG is a hypothesis with a rival.
- The "first drop" claim stays epistemic.
- cake_lpr is outside Lean in every mention.
- The `native_decide` dependence is disclosed with counts.
- R-AUD: 0 governance and 0 private-locator hits in the paper.
- R-LINK: 64/64 targets exist at the pin.
- Dollar figures: one sentence.

## Dimension summary

| # | Dimension | Weight | v10 | v11 |
|---|---|---|---|---|
| 1 | Rigor of method / argument | 6 | 5 | 6 |
| 2 | Evidence sufficiency | 6 | 5 | 5 |
| 3 | Clarity of contribution | 5 | 5 | 5 |
| 4 | Related-work positioning | 5 | 4 | 4 |
| 5 | Reproducibility | 5 | 3 | 4 |
| 6 | Figure & table quality | 4 | 4 | 4 |
| 7 | Prose & structural quality | 4 | 3 | 4 |
| 8 | Citation hygiene | 5 | 5 | 5 |
| 9 | Rhetorical economy | 4 | 3 | 3 |
| | **Total** | **44** | **37** | **40** |

## Remaining fixes (advisory; `advance: true`)

1. **Release precondition, not a manuscript defect:** the paper now discloses that the capstone cannot be rebuilt from the public repository. To remove the limitation instead of disclosing it, deposit the 13 packed files (Zenodo or LFS; the largest is 1.6 GB), repoint `include_str`, and repin before the tag.
2. m1: add one sentence positioning the H7 Lean-checked symmetry breaking against \citet{subercaseaux2024hexagonlean}.
3. m2: at L232, replace "for a fully independent audit, publication of the 13 packed …" with "for a rebuild from the public repository, publication of the 13 packed …; for a fully independent audit, a cold rebuild …".
4. Nits: two "now superseded" phrases; the qualifier and receipt link for \$225; "previously settled" → "previously known"; trim "the operator's \$300 H7 ceiling" from the linked H7 README before the tag.

## BRIEF note (advisory)

The BRIEF frontmatter `claim` still reads "the H3 and H5 premises and the H7 t = 0 capstone are open in Lean". The paper now says, with receipts in `refs/` (H3/H5/capstone/release READMEs), that H3 and H5 are excluded in Lean and H7 ($t=0$) is reduced. The paper is right and the BRIEF is stale. An auditor comparing the two will see the mismatch. A one-paragraph R-V10 amendment that updates `claim` (and nothing else) would close it. This changes no score and no gate.

## Evidence drift

`anvil.lib.evidence_drift` reports NO-SNAPSHOT (v11 is a direct edit) and treats that as clean, so there is no automated note.
