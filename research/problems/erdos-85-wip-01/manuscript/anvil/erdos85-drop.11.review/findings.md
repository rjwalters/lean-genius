# Findings — erdos85-drop.11

## 1. Verification of the v10 corrections at the new pin

- **Pin.** `f6daa149b807972abe1c3e669abce092a863c2bd` is on `origin/erdos85/release-assembly-20261011` (an ancestor of the remote head `a2204511564c`). Relative to the v10 pin `1d0772cd825`, it adds only research-side files: the STRATA banner, the H7 README cost lines and anvil sidecars. Nothing under `proofs/` changed. So every Lean-statement check from the v10 review and audit (capstone signature `hOne`/`depth`/`hSeven`, docstring "not an unconditional Lean proof", 601/607/604 axiom counts) carries over unchanged.
- **Link targets.** 70 `\repofile` uses and 64 distinct targets; every target exists at the pin (`git cat-file -e`).
- **STRATA banner (M2).** It is present at the pin, and its first line is "**Superseded status (banner added 2026-10-11).**" It names `H3.orderFortyNineStratumExcluded_three`, `H5.orderFortyNineStratumExcluded_five` and the capstone, and says the capstone is "conditional on explicit H1 and H7 unsatisfiability hypotheses". The banner is consistent with v11.
- **H7 reduction axioms (m6).** In `h7_hsb_capstone_review_20261008/stratum.log` at the pin, `orderFortyNineStratumExcluded_seven_of_structuralHsbEvidence` depends on `propext`, `Classical.choice`, `Quot.sound` and exactly 91 `…native_decide.ax_*` axioms; there is no `sorryAx`. This matches the paper. The split lemma does not appear in that log, and the paper does not assert its axioms, which is correct.
- **Public-rebuild limitation (M1).** `refs/CAPSTONE_ABSOLUTE_PATH_AUDIT_20261011.json` gives 13 `include_str` absolute strings, 13 distinct files, 2,574,916,357 B in total, over 893 manifest sources. The paper's "13 … (about 2.57 GB)" matches.
- **Dollar figures (C2).** The only one left is \$225 (L191). It traces to `H1_CERT_RECEIPTS_README_20261006.md` ("≈ \$204") plus `H1_BANK_CHECK_README_20261006.md` ("about \$20"; summary JSON `cloud_spend_usd_estimate` 20.42), and BRIEF R-SIMPLE names "≈ \$225". The "controller estimate" qualifier is dropped (nit n2).
- **H5 count (N6).** "58 native_decide axioms" + 3 standard = 61, matching `refs/H5_TERMINAL_REVIEW_README_20261008.md` ("Its exact trust set contains 61 axioms").

## 2. Scope wording, full sweep

Every occurrence of "theorem" was checked:
- Abstract: none for Result A.
- L78: "is derived in Lean by".
- L85: "the formally verified empty-hexagon theorem" (the precedent) and "Lean derives the upper side".
- L87: "not an unconditional theorem of Lean" and "separates Result A from a Lean theorem" (negations).
- L117: "the stratum theorem `H3.…`" (a genuine standard Lean theorem about H3, not Result A).
- L123: "the theorem takes the depth as a parameter" (the H7 reduction, a genuine Lean theorem).
- L203: a HOL4 theorem about cake_lpr.
- L232: a negation.
- §5: Theorem B.

None calls Result A, or its upper side, a theorem. The words "proof" and "decided" are not applied to Result A. "Settled" occurs twice: at L85 for prior literature (nit n3), and at L147, where the verdict-only census is explicitly marked "superseded … we do not rely on it".

## 3. Cross-section consistency after the edits

- The abstract, Result A, §1 "What is new" and Table 2 all name two hypotheses, $h_{\mathrm{H1}}$ and $h_{\mathrm{H7}}$.
- The not-published items agree across L87, Table 2, L232 and L285: the 13 $t\ge1$ packed files, the rest of the certificate storage and the artifact volume.
- "Emitters" (plural) is now used consistently. L203 keeps "compiled Lean emitter" for H1, which is correct (`v2cnf`).
- The H7 counts are self-consistent: 232 re-run + 1 split; 233 timed-out attempts = 232 main-pass + 1 residual; 377,804 = 28 + 377,776.
- One framing tension (minor m2): L87 makes recompilation the consequence, while L232 files publication under "for a fully independent audit".

## 4. Release-level observations (outside the rubric)

- The 13 packed H7 $t\ge1$ certificate files are now disclosed as unpublished. Disclosure is enough for the rubric. Publishing them (Zenodo; the largest file is 1.6 GB, over GitHub's per-file limit) and repinning would turn the limitation into a reproducible build.
- The BRIEF frontmatter `claim` still describes the pre-v10 state ("H3 and H5 premises and the H7 t = 0 capstone are open in Lean"). The paper is correct per the receipts in `refs/`. An R-V10 amendment updating `claim` would stop a future audit from flagging the mismatch.
- The linked H7 campaign README at the pin carries "the operator's \$300 H7 ceiling" (nit n4).
