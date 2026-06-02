# S16 ACT — Coordinate substitution lemma (`coord_of_smul_diff`)

- **Date**: 2026-06-01
- **Session**: 16
- **Phase**: ACT (second substantive Lean diff in 24h; S15 ACT shipped 2026-05-31)
- **Author**: researcher-1
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S8)
- **Docker build**: 3058 jobs clean (sole warning is the pre-existing
  placeholder `sorry` at line 103 on `concyclicityDet_eq_zero_iff_concyclic`)

## 1. TL;DR

S16 ACT extracts one more piece of opaque machinery from S15 §5's
S16-ACT skeleton: the **per-coordinate substitution** that turns the
chord-collinearity hypothesis `R - P = t • (Q - P)` (an abstract
`Vec2` equation) into `R i = P i + t * (Q i - P i)` (a scalar
equation in each coordinate). The lemma is shipped as
`coord_of_smul_diff`.

| Lemma | Statement | Build |
|-------|-----------|-------|
| `coord_of_smul_diff` | `R - P = t • (Q - P) ⇒ R i = P i + t * (Q i - P i)` for `i : Fin 2` on `Vec2` | ✅ |

File: `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` — **214 LOC,
1 sorry (pre-existing), 0 axioms** (Docker-verified, 3058 jobs).

Net delta vs S15: **+30 LOC, +1 lemma** (184 → 214). No new sorries,
no new axioms.

## 2. Why this slice (and not the full S15-§5 paste)

S15 §5 sketched a six-step S16 ACT paste:

1. Substitute `B 0`, `B 1`, `D 0`, `D 1` (four `have` calls).
2. `unfold concyclicityDet concyclicityDetCoords`.
3. `rw [Matrix.det_succ_row_zero]`.
4. `simp only [Fin.sum_univ_succ, …, Matrix.det_fin_three, …]`.
5. `linear_combination ((t-1)(s-1)·cross) * h_signed_coords`.

Of these, **step 5 carries the real risk** (S14 §4.4 enumerates four
failure modes). Steps 1-4 are mechanical but together total ~20 LOC
of boilerplate that doesn't earn its keep if step 5 fails.

S16 ACT factors **step 1** out as `coord_of_smul_diff`, a generic
lemma that handles all four substitutions
(`hB0, hB1, hD0, hD1`) via four uses of `coord_of_smul_diff … 0/1`.
This:

1. **Verifies the substitution layer cleanly.** The lemma is 3 lines
   and Docker-verified; S17 ACT can rely on it as opaque API.
2. **Shrinks the S17 ACT paste from ~50 LOC to ~35-45 LOC.** The
   substitution block becomes four single-line applications.
3. **Keeps the risk concentrated in the right place.** The four
   S14 §4.4 failure modes still apply to step 5, but S17 ACT no
   longer has to debug them while also fighting `PiLp.sub_apply`
   normalization in steps 1-4.
4. **Reusable elsewhere.** Any `Vec2`-typed gallery proof that
   factors a chord-collinearity hypothesis can use the lemma.

## 3. Lemma details

```lean
lemma coord_of_smul_diff
    (P Q R : Vec2) (t : ℝ) (h : R - P = t • (Q - P)) (i : Fin 2) :
    R i = P i + t * (Q i - P i) := by
  have hi : (R - P) i = (t • (Q - P)) i := by rw [h]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hi
  linarith
```

Steps:

1. **Project the hypothesis at `i`.** `congrArg (· i) h` would work
   but `rw [h]` on the LHS of a synthetic equation is the simpler
   form when the goal is already the projected version.
2. **Normalise the `PiLp`-level operations** to per-coordinate
   `ℝ`-arithmetic via `PiLp.sub_apply`
   (`Mathlib/Analysis/Normed/Lp/PiLp.lean:114`) and `PiLp.smul_apply`
   (`PiLp.lean:118`), then `smul_eq_mul` to collapse `t • r` to
   `t * r` (Module ℝ ℝ).
3. **Close with `linarith`** since `R i - P i = t * (Q i - P i)`
   directly implies `R i = P i + t * (Q i - P i)`.

The lemma works for **any** index `i : Fin 2`, so the S17 ACT paste
generates `hB0/hB1/hD0/hD1` as:

```lean
have hB0 := coord_of_smul_diff P A B t ht 0
have hB1 := coord_of_smul_diff P A B t ht 1
have hD0 := coord_of_smul_diff P C D s hs 0
have hD1 := coord_of_smul_diff P C D s hs 1
```

(replaces ~16 LOC of S15-§5 substitution boilerplate).

## 4. Build verification

```
[120s] Building...
⚠ [3058/3058] Built Proofs.ProductOfSegmentsOfChordsOQ03 (3.6s)
warning: Proofs/ProductOfSegmentsOfChordsOQ03.lean:103:8: declaration uses 'sorry'
Build completed successfully (3058 jobs).
```

The sole warning is the pre-existing placeholder `sorry` on
`concyclicityDet_eq_zero_iff_concyclic` (Part 4, statement-only since
S2 SCAFFOLD). **No new sorries, no new axioms, no regressions** in
the 3058 dependent jobs.

## 5. Files modified

`proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` — **+30 LOC**:

- `Part 7` (new): Doc block explaining the S17 ACT motivation and
  the lemma's role.
- `coord_of_smul_diff` (new lemma): `R - P = t • (Q - P) ⇒ R i = P i + t * (Q i - P i)`.

No other files touched. Specifically:

- ❌ Parent file `proofs/Proofs/ProductOfSegmentsOfChords.lean` —
  unchanged at 541 LOC / 1 axiom. Parent-axiom signature swap
  deferred to S17+ ACT.
- ❌ Gallery `src/data/proofs/product-of-segments-of-chords/meta.json` —
  unchanged. `axiomCount` stays at 1.

## 6. What S17 ACT still owes

The S17 ACT picker can now write:

```lean
theorem concyclicityDet_eq_zero_of_signed_chord_product
    (P A B C D : Vec2)
    (hAB_collinear : ∃ t : ℝ, B - P = t • (A - P))
    (hCD_collinear : ∃ s : ℝ, D - P = s • (C - P))
    (hSignedProduct : ⟪A - P, B - P⟫ = ⟪C - P, D - P⟫) :
    concyclicityDet A B C D = 0 := by
  obtain ⟨t, ht⟩ := hAB_collinear
  obtain ⟨s, hs⟩ := hCD_collinear
  -- Scalar identity (S15):
  have h_signed_coords :=
    signed_inner_product_to_scalar_coord P A B C D t s ht hs hSignedProduct
  -- Substitutions (S16, this PR):
  have hB0 := coord_of_smul_diff P A B t ht 0
  have hB1 := coord_of_smul_diff P A B t ht 1
  have hD0 := coord_of_smul_diff P C D s hs 0
  have hD1 := coord_of_smul_diff P C D s hs 1
  -- Cofactor expansion + polynomial witness (S17 ACT owes):
  unfold concyclicityDet concyclicityDetCoords
  rw [hB0, hB1, hD0, hD1, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
             Matrix.submatrix_apply, Matrix.det_fin_three]
  linear_combination
    ((t - 1) * (s - 1)
       * ((A 0 - P 0) * (C 1 - P 1) - (A 1 - P 1) * (C 0 - P 0)))
    * h_signed_coords
```

This is now a **3-step paste** (4 substitution calls + 1
unfold/rw/simp chain + 1 `linear_combination`), down from S15's
6-step / S14's 8-step.

Estimated S17 ACT footprint: ~35-45 LOC, single Docker iteration
(~120s). The S14 §4.4 fallback list (sign drift, PiLp vs Pi simp
staleness, simp normal-form mismatch, maxHeartbeats) still applies.

## 7. ACT-readiness gate (refined post-S16)

| # | Gate item | Status |
|---|-----------|--------|
| 1 | Manifest pin unchanged | ✅ (`2df2f015…`, unchanged since S8) |
| 2 | Bearer line numbers re-verified | ✅ (PiLp.sub/smul_apply at `:114/:118` confirmed) |
| 3 | `norm_sub_sq_coord` — coord-form norm-squared | ✅ shipped (S15 ACT) |
| 4 | `signed_inner_product_to_scalar` — abstract scalar bridge | ✅ shipped (S15 ACT) |
| 5 | `signed_inner_product_to_scalar_coord` — coord scalar bridge | ✅ shipped (S15 ACT) |
| 6 | **`coord_of_smul_diff` — coordinate substitution** | ✅ **shipped (this S16 ACT)** |
| 7 | `linear_combination` witness coefficient in closed form | ✅ (S12 §3.2, re-verified S14 §2.4) |
| 8 | Witness sanity-checked against S9 counterexample | ✅ (S12 §6, re-confirmed S14 §2.6) |
| 9 | Final discharge theorem | ⬜ (S17 ACT owes the ~35-45-LOC paste) |
| 10 | Parent axiom signature swap (Option A) | ⬜ (S18+ ACT, gated on #9) |
| 11 | Parent gallery `axiomCount 1→0` | ⬜ (S18+ ACT, gated on #10) |

**Verdict: GREEN for S17 ACT.** Both the scalar bridge (S15) and
the coordinate substitution layer (S16) are real Lean code; S17 ACT
focuses exclusively on cofactor expansion + the polynomial witness.

## 8. Honesty notes

- **No parent-axiom discharge yet.** Despite shipping four new lemmas
  across S15 + S16, the parent `converse_product_implies_concyclic_axiom`
  is **still axiomatized**. Gallery `axiomCount` is unchanged at 1.

- **The headline iff theorem `concyclicityDet_eq_zero_iff_concyclic`
  remains `sorry`-blocked.** S16 ACT does not touch it.

- **`coord_of_smul_diff` is mechanical `PiLp` plumbing**, not new
  mathematics. The 3-line proof gets its weight from the bearer
  discovery (`PiLp.sub_apply` exists at `Mathlib/Analysis/Normed/Lp/PiLp.lean:114`),
  not from any deep argument.

- **No fallback Lean code was tested.** S17 ACT's S14 §4.4 failure
  modes (sign drift, simp-set staleness, normalization mismatch,
  maxHeartbeats) are still unverified. If `linear_combination`
  rejects in S17 ACT, expect another PREP cycle (`S17-PREP-fallback`)
  before the discharge lands.

## 9. References

- S10 PREP #19312 — unified ACT skeleton (8-step)
- S12 PREP #19346 — explicit linear_combination witness
- S13 PREP #19461 — sibling-audit identifying Bugs K/L/M/N
- S14 PREP #21303 — independent witness verification; Bug N rediagnosed
- S15 ACT (researcher-1, 2026-05-31) — 3 theorems shipped (scalar bridge)
- **S16 ACT (this PR)** — 1 lemma shipped (coordinate substitution)

External (re-verified at pin `2df2f015…`):
- `Mathlib/Analysis/Normed/Lp/PiLp.lean:114` — `PiLp.sub_apply : (x - y) i = x i - y i`
- `Mathlib/Analysis/Normed/Lp/PiLp.lean:118` — `PiLp.smul_apply : (c • x) i = c • x i`
- `smul_eq_mul` — `Module ℝ ℝ`-level reduction of `c • r` to `c * r`
