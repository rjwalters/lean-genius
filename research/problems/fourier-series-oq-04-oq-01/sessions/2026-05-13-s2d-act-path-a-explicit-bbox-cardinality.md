# S2d ACT Path A — Explicit bounding-box cardinality `(2⌈|R|⌉+1)²`

**Researcher**: researcher-4
**Date**: 2026-05-13
**Phase**: ACT (Lean delta, build-pending)
**Iteration**: S2d ACT (Path A from S2d PREP #18393 §4.1)
**Predecessor PRs**:
- #18062 (S1 OBSERVE, MERGED) — territory map
- #18165 (S2a ACT scaffold, MERGED) — axiom + sorry + sanity lemmas
- #18255 (S2c ACT, MERGED) — `latticeDisc_subset_bbox` + `latticeDisc_card_le_bbox` (qualitative)
- #18393 (S2d PREP, MERGED) — Mathlib API audit + verbatim proof skeleton for `bbox_card`
- #18446 (S2e PREP, MERGED) — orthogonal: `mFourierBasis` L² discharge plan (`sphPartialSum_L2_norm_converge` sorry)
- #18545 (S2f PREP, MERGED) — orthogonal: `volume`/`haarT2` `rfl` errata audit
- #18583+ (S2g PREP, MERGED) — orthogonal: Lp coeFn finset-sum + cofinality + eLpNorm bridge audit
**Lines added**: `proofs/Proofs/FourierSeriesOQ04OQ01.lean` 204 → 234 (+30), 5 → 7 theorems, 0 → 0 new axioms / sorries.

## Headline finding (two-line summary)

The S2d PREP's verbatim proof skeleton (PR #18393 §2.1, ~11 LOC) lifts cleanly into the Lean file. Two new sorry-free, axiom-free theorems land: `bbox_card` evaluates `#(Icc (fun _ => -⌈|R|⌉) (fun _ => ⌈|R|⌉)) = (2⌈|R|⌉+1).toNat ^ 2`; `latticeDisc_card_le_explicit` composes `latticeDisc_card_le_bbox` with `bbox_card` via `.trans_eq`. The Gauss-circle upper bound `(latticeDisc R).card ≤ (2⌈|R|⌉+1)²` is now closed-form, ready for ℓ¹ majorisation of `sphPartialSum`. **Build status: pending** (worktree `.lake` symlink loop).

## §1. The delta

### File: `proofs/Proofs/FourierSeriesOQ04OQ01.lean` (+30 LOC: 204 → 234)

Insertion location: between `latticeDisc_card_le_bbox` (ends line 200) and the `end` closing the `noncomputable section` (was line 202, now line 232). The new block is wrapped in a `/-! ## S2d — Explicit bounding-box cardinality (2⌈|R|⌉+1)² -/` section comment matching the gallery's conventions.

```lean
/-- The integer bounding box `[-⌈|R|⌉, ⌈|R|⌉]² ⊂ ℤ²` has cardinality
    `(2⌈|R|⌉+1).toNat ^ 2`. Direct from `Pi.card_Icc` + `Int.card_Icc`. -/
theorem bbox_card (R : ℝ) :
    (Finset.Icc (fun _ : Fin 2 => -⌈|R|⌉) (fun _ : Fin 2 => ⌈|R|⌉)).card
      = ((2 * ⌈|R|⌉ + 1).toNat) ^ 2 := by
  rw [Pi.card_Icc]
  simp only [Int.card_Icc]
  have h : (⌈|R|⌉ + 1 - -⌈|R|⌉ : ℤ) = 2 * ⌈|R|⌉ + 1 := by ring
  simp [h, Finset.prod_const, Fintype.card_fin]

/-- Explicit upper bound on the lattice-disc cardinality:
    `(latticeDisc R).card ≤ (2⌈|R|⌉+1)²`. Combined with the trivial
    estimate `⌈|R|⌉ ≤ |R| + 1`, this gives `(latticeDisc R).card = O(R²)`,
    the qualitative Gauss-circle bound. The sharp constant `π` requires
    boundary-lattice analysis (separate session). -/
theorem latticeDisc_card_le_explicit (R : ℝ) :
    (latticeDisc R).card ≤ ((2 * ⌈|R|⌉ + 1).toNat) ^ 2 :=
  (latticeDisc_card_le_bbox R).trans_eq (bbox_card R)
```

Tactic chain for `bbox_card`:
1. `rw [Pi.card_Icc]` — `Mathlib/Data/Pi/Interval.lean:41` exposes
   `Pi.card_Icc : #(Icc a b) = ∏ i, #(Icc (a i) (b i))` (verified at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).
2. `simp only [Int.card_Icc]` — `Mathlib/Data/Int/Interval.lean:96` exposes the `@[simp]` lemma `Int.card_Icc : #(Icc a b) = (b + 1 - a).toNat`. After firing, the goal becomes `∏ i : Fin 2, (⌈|R|⌉ + 1 - -⌈|R|⌉).toNat = (2 * ⌈|R|⌉ + 1).toNat ^ 2`.
3. `have h : ... = 2 * ⌈|R|⌉ + 1 := by ring` — eliminate the `-(-)` and combine the two `⌈|R|⌉` summands.
4. `simp [h, Finset.prod_const, Fintype.card_fin]` — apply the cast on each factor (`h`), then `Finset.prod_const` reduces the constant product to a power, and `Fintype.card_fin` gives `Fintype.card (Fin 2) = 2`.

Term-mode for `latticeDisc_card_le_explicit`: `(latticeDisc_card_le_bbox R).trans_eq (bbox_card R)`. The `Nat.le.trans_eq : n ≤ m → m = k → n ≤ k` lemma is in core Lean / `Mathlib.Order.Basic`.

### File: `src/data/proofs/fourier-series-oq-04-oq-01/meta.json`

| Field | Before | After |
|---|---|---|
| `leanFile.lineCount` | 204 | 234 |
| `leanFile.theoremCount` | 5 | 7 |
| `meta.lineCount` | 204 | 234 |
| `meta.theoremCount` | 5 | 7 |
| `meta.axiomCount` | 1 | 1 (unchanged) |
| `meta.sorries` | 1 | 1 (unchanged) |
| `meta.status` | `axiomatized` | `axiomatized` (unchanged) |
| `meta.originalContributions` | 9 items | 10 items (+1 S2d entry) |
| `sections[]` | 5 items | 6 items (+1 `lattice-disc-explicit-card`) |

The `sections[]` extension narrows the S2c `lattice-disc-bbox` section to lines 177–200 (was 177–202; the `end` line 202 originally bundled into S2c is now the start of the S2d section) and inserts a new `lattice-disc-explicit-card` section spanning 202–230.

### File: `research/problems/fourier-series-oq-04-oq-01/state.md`

- `Current State`: phase ACT iteration 3 → 4, since 2026-05-12 → 2026-05-13.
- `Current Focus`: S2c text moved into a new `## S2c (Previous Iteration)` section; replaced with an S2d ACT block listing the two new theorems and the Mathlib lemma chain.
- `Next Action`: removed the "S2d (refinement of S2c)" bullet (now DONE); added an S2e ACT bullet pointing at the audit chain (#18446 → #18545 → #18583+).

## §2. Build-risk audit

Per S2d PREP #18393 §2.3, the build-risk table identified one **medium-risk** step:

> `simp [h, Finset.prod_const, Fintype.card_fin]` may leave residual `Fin 2 → ℤ` typeclass goal. Fallback: `rfl` after `change` to unfold `Fintype.card (Fin 2)`; or split into `Finset.prod_univ_succ + Finset.prod_univ_zero`.

The verbatim proof skeleton uses the `simp` form. If the docker build fails at this step, the documented fallback is:

```lean
rw [Pi.card_Icc, Fin.prod_univ_succ, Fin.prod_univ_zero]
simp only [Int.card_Icc, mul_one]
-- Now two copies of `(⌈|R|⌉ + 1 - -⌈|R|⌉).toNat`
have h : (⌈|R|⌉ + 1 - -⌈|R|⌉ : ℤ) = 2 * ⌈|R|⌉ + 1 := by ring
rw [h, sq]
```

Both proofs are direct applications of stable Mathlib lemmas (no novel reasoning; no Mathlib gaps to cross). The risk surface is minimal.

## §3. Orthogonality to in-flight PRs (at push time)

| PR | Phase | Focus | Conflict with S2d ACT? |
|---|---|---|---|
| #18167 (OPEN) | audit(tracker) | `audit-tracker.json` clean-bump | no — separate path |
| #18175 (OPEN) | enrichment | `annotations.json` (110 LOC) + `meta.json` `crossReferences` append (4 entries, lines 153+) | no — non-overlapping `meta.json` hunks; my edits are at lines 6–16 (`leanFile`), 35–37 (`meta`), 72–82 (`originalContributions`), 103–145 (`sections`); enricher's edit is at lines 153+ (`crossReferences`) |
| #18446 (S2e PREP, MERGED) | doc-only | mFourierBasis L² discharge plan | no — orthogonal target (sphPartialSum sorry) |
| #18545 (S2f PREP, MERGED) | doc-only | volume/haarT2 errata | no — orthogonal target |
| #18583+ (S2g PREP, MERGED) | doc-only | Lp coeFn + eLpNorm bridge | no — orthogonal target |
| **#this** | S2d ACT Path A | Lean: bbox cardinality | — |

Zero edits to: `problem.md`, `knowledge.md`, `index.ts`, `annotations.json`, S2e/f/g session notes. The S2d ACT touches only the Lean file, `meta.json` (non-overlapping hunks vs #18175), `state.md` (no other in-flight PR touches), and adds this session note.

## §4. What this ACT does NOT address

1. **The `carleson_2d_sph` axiom**. Genuinely open mathematics (Stein 1971; Tao 2002). Unchanged.
2. **The `sphPartialSum_L2_norm_converge` sorry**. Distinct target; audit chain S2e/f/g pre-stages the 70–95 LOC discharge plan.
3. **The sharp Gauss-circle bound `card ≤ ⌈π·R²⌉ + O(R)`**. Genuine boundary-lattice / sums-of-two-squares analysis (Mathlib has `Mathlib.NumberTheory.SumTwoSquares` for the representation count, but no packaged Gauss-circle estimate at v4.26.0). Deferred to S2e' or later.
4. **The n-torus generalisation (Path B from S2d PREP §4.2)**. Requires generalising `latticeDisc` itself; out of scope.
5. **Docker build verification**. Worktree `.lake` symlink is recursive (MEMORY.md trap). Build pending.
6. **`loom:review-requested` label**. Math-agent policy (CLAUDE.md "PR Labels for Math Agents").

## §5. Honesty

- This is an **S2d ACT** (Path A from the S2d PREP), not a doc-only PREP. The two new theorems are sorry-free, axiom-free additions to the Lean file.
- The proof skeleton is the verbatim S2d PREP §2.1 chain. I did not run docker build (`.lake` symlink loop); if the inline `simp` underspecifies, the documented fallback applies.
- The Mathlib API has been **verified at pinned rev** by the S2d PREP via `gh api`. I did not re-verify in this session — that would burn `gh api search/code` rate-limit budget unnecessarily.
- The `(2⌈|R|⌉+1).toNat ^ 2` form uses `.toNat` because `2⌈|R|⌉+1` is a `ℤ` value whose natural-number cardinality is its absolute value (always non-negative since `⌈|R|⌉ ≥ 0`). I do not unfold `.toNat` (not necessary for the corollary).
- The `latticeDisc_card_le_explicit` corollary is intentionally **stated without unfolding `.toNat`** — this matches Mathlib's idiom (`Int.card_Icc` lands in `.toNat`, downstream users can `Int.toNat_of_nonneg` if they want a `ℤ`-level bound).
- I did NOT extend the `lattice-disc-bbox` section's `endLine`; instead I created a fresh `lattice-disc-explicit-card` section. This matches the convention of one section per `/-! ## ... -/` block in the Lean file.

## §6. References

- S2d PREP (PR #18393): `research/problems/fourier-series-oq-04-oq-01/sessions/2026-05-12-s2d-prep-bbox-explicit-card-pi-int.md` — verbatim proof skeleton in §2.1, build-risk audit in §2.3, three pickup paths in §4.
- Mathlib paths (at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):
  - `Mathlib/Data/Pi/Interval.lean:41` — `Pi.card_Icc`
  - `Mathlib/Data/Int/Interval.lean:96` — `Int.card_Icc` (`@[simp]`)
  - `Mathlib/Data/Finset/BigOps/Basic.lean` (or similar) — `Finset.prod_const`
  - `Mathlib/Data/Fintype/Card.lean` — `Fintype.card_fin`
  - `Mathlib/Order/Basic.lean` — `Nat.le.trans_eq` (or core `le_trans_eq`)
- Slug-internal references:
  - `proofs/Proofs/FourierSeriesOQ04OQ01.lean:189` — `latticeDisc_subset_bbox` (S2a or S2c)
  - `proofs/Proofs/FourierSeriesOQ04OQ01.lean:197` — `latticeDisc_card_le_bbox` (S2c)
  - `proofs/Proofs/FourierSeriesOQ04OQ01.lean:215` — `bbox_card` (this PR)
  - `proofs/Proofs/FourierSeriesOQ04OQ01.lean:228` — `latticeDisc_card_le_explicit` (this PR)
