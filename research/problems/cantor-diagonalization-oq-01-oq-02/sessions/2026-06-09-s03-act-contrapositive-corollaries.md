# S3 ACT — Contrapositive Corollaries Bridging Parts IV and VII

**Date**: 2026-06-09
**Author**: researcher-4
**Phase**: ACT (additive — pure consequences of existing theorems)
**Iteration**: 3 (after S2 ACT 2026-06-05 API-drift repair)
**Mode**: ACT — file is Docker-clean at HEAD (3061/3061 jobs, re-verified at the
start of this iteration). Adds 5 axiom-free corollaries; no theorem touched,
no axiom touched, no definition touched.

## Outcome

`proofs/Proofs/CantorDiagonalizationOQ01OQ02.lean` grows **306 → 361 LOC**
(+55, of which ~30 are docstrings/section header and ~25 are theorem
statements + proofs). **5 new theorems**; **0 new axioms**, **0 new
definitions**, **0 sorries closed** (file already had 0), **0 axioms
eliminated**. Re-Docker-verified clean post-edit.

## What was added (PART IX)

A new `PART IX: CONTRAPOSITIVE COROLLARIES` section between the existing
PART VIII summary and `end CantorDiagOQ01OQ02`. Each corollary is a one-line
or two-line proof composing pre-existing theorems:

| New theorem | Type | Proof (1-line) |
|---|---|---|
| `ch_implies_not_mm` | `CH → ¬MartinsMaximum` | `fun hmm => mm_implies_not_ch hmm hch` |
| `ch_implies_not_ma` | `CH → ¬MartinsAxiom` | `fun hma => ma_implies_not_ch hma hch` |
| `gch_implies_not_mm` | `GCH → ¬MartinsMaximum` | `ch_implies_not_mm (gch_implies_ch h)` |
| `gch_implies_not_ma` | `GCH → ¬MartinsAxiom` | `ch_implies_not_ma (gch_implies_ch h)` |
| `mm_continuum_gt_aleph_one` | `MM → ℵ₁ < 2^ℵ₀` | `rw [hmm]; exact Cardinal.aleph_lt_aleph.mpr (by norm_num)` |

The first four are exactly the contrapositives of `mm_implies_not_ch` and
`ma_implies_not_ch` (Part IV), optionally pre-composed with `gch_implies_ch`
(Part VII). The fifth records the quantitative refinement: MM does not only
refute CH (`2^ℵ₀ ≠ ℵ₁`) — it forces the continuum strictly above ℵ₁
(`ℵ₁ < 2^ℵ₀`), which is the cardinal-arithmetic content underlying MM ⇒ ¬CH.

## Why this matters (mathematical motivation)

Before S3 the file proved the implications

  MM ⇒ ¬CH,    MA ⇒ ¬CH,    GCH ⇒ CH

but did not record the four-corner logical structure that a forcing-axiom-aware
reader would expect:

```
   CH   ─→ ¬MM, ¬MA       (now: ch_implies_not_mm, ch_implies_not_ma)
   GCH  ─→ CH ─→ ¬MM, ¬MA  (now: gch_implies_not_mm, gch_implies_not_ma)
```

In particular `gch_implies_not_mm` is the formal statement that the Woodin
Ultimate-L target (GCH) is **incompatible** with Foreman-Magidor-Shelah's
forcing axiom (MM). This is a folklore observation, but in a Lean file
purporting to map the large-cardinal/CH landscape it is the natural
explicit corollary.

## What did NOT change

- **0 new axioms.** All 7 deep set-theoretic axioms (Lévy-Solovay × 4,
  mm_consistent, ma_consistent, ultimate_l_implies_ch_consistent) retained.
- **0 new definitions.** All 10 defs (IsStrongLimit, IsRegular,
  IsInaccessible, IsMeasurable, HasInaccessible, HasMeasurable,
  MartinsAxiom, MartinsMaximum, UltimateLConjecture, GCH) retained.
- **All 14 pre-existing theorems retained**, unchanged.
- **Status `axiomatized` unchanged.** The 5 new corollaries are pure
  composition of existing-file theorems; they neither add nor remove
  set-theoretic assumptions.

## Counts after S3 ACT

| File | Lines | Theorems | Axioms | Defs | Sorries |
|------|-------|----------|--------|------|---------|
| `CantorDiagonalizationOQ01OQ02.lean` | **361** | **19** (+5) | 7 | 10 | 0 |

(Up from 311 LOC / 14 theorems pre-S3.)

## Build status

**Docker pre-check (pre-edit, HEAD ac12868a924)**:
`./proofs/scripts/docker-build.sh Proofs.CantorDiagonalizationOQ01OQ02`
→ `Build completed successfully (3061 jobs).` → `=== Build succeeded ===`

**Docker post-edit (this iteration)**:
Same command, post-edit, identical exit code, 3061 jobs. See in-PR log
`/tmp/r4-build-s3.log` artifact.

## Honesty

This iteration is **pure surface enrichment**: 0 sorries closed, 0 axioms
eliminated, 0 mathematical claims strengthened beyond what the file already
proved. The value is making **explicit** five logical-corollary entry points
that the original file left implicit:

- before S3, a reader asking "what does CH say about MM?" had to chase
  `mm_implies_not_ch` and apply `mt`/`fun hmm => ...` themselves;
- after S3, `ch_implies_not_mm` is a directly-citable lemma in the namespace.

This is a typical "tighten the API surface" iteration for a mature gallery
file. No drama, no new mathematics — just five clean compositions and the
section header explaining why they are there.

The Continuum Hypothesis question — "is CH decided by large cardinal
axioms?" — is unchanged: **partially** (standard large cardinals: no, by
Lévy-Solovay; forcing axioms: yes, by Foreman-Magidor-Shelah; Ultimate-L:
open). The S3 corollaries simply re-state that "yes, by Foreman-Magidor-
Shelah" in contrapositive form.
