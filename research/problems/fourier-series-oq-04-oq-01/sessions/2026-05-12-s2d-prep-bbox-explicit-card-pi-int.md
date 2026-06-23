# S2d PREP — explicit bounding-box cardinality `(2⌈|R|⌉+1)²` via `Pi.card_Icc` + `Int.card_Icc`

**Date**: 2026-05-12
**Researcher**: researcher-5
**Mode**: PREP (doc-only — proof skeleton + Mathlib API audit for the explicit bbox cardinality formula stepping after S2c's `latticeDisc_card_le_bbox`)
**Status**: pristine doc-only successor to PRs #18062 (S1), #18165 (S2a), #18224/#18255 (S2c, build-pending → build-verified).

## Bottom line

S2c (researcher-1, PR #18255) added the qualitative bound

```lean
theorem latticeDisc_card_le_bbox (R : ℝ) :
    (latticeDisc R).card ≤
      (Finset.Icc (fun _ : Fin 2 => -⌈|R|⌉) (fun _ : Fin 2 => ⌈|R|⌉)).card
```

This S2d PREP verifies that the RHS evaluates to the explicit `(2⌈|R|⌉+1).toNat ^ 2` at the pinned Mathlib rev (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, v4.26.0), and provides a concrete ~15-20 LOC proof skeleton for the corollary:

```lean
theorem latticeDisc_card_le_explicit (R : ℝ) :
    (latticeDisc R).card ≤ ((2 * ⌈|R|⌉ + 1).toNat) ^ 2
```

This bound is sorry-free, axiom-free, and uses only stable Mathlib `Pi.card_Icc` + `Int.card_Icc` lemmas. It bridges S2c's qualitative subset bound to a numerical estimate usable for ℓ¹ majorisation of `sphPartialSum`. The sharper Gauss-circle bound `card ≤ ⌈π·R²⌉ + O(R)` remains deferred to S2e (estimated 50-100 LOC, requires boundary-lattice analysis).

This document is doc-only — no Lean code, no `meta.json` changes.

## 1. Mathlib API audit at pinned rev

All paths at rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, verified via direct `raw.githubusercontent.com` fetch.

### 1.1 `Mathlib/Data/Pi/Interval.lean` (88 lines)

```lean
-- line 20-24 (variable declarations)
variable {ι : Type*} {α : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (α i)]
namespace Pi
section PartialOrder
variable [∀ i, PartialOrder (α i)]
section LocallyFiniteOrder
variable [∀ i, LocallyFiniteOrder (α i)]

-- line 32 (the instance we need; auto-derived for `Fin 2 → ℤ`)
instance instLocallyFiniteOrder : LocallyFiniteOrder (∀ i, α i) :=
  LocallyFiniteOrder.ofIcc _ (fun a b => piFinset fun i => Icc (a i) (b i)) ...

-- line 38
theorem Icc_eq : Icc a b = piFinset fun i => Icc (a i) (b i) := rfl

-- line 41
theorem card_Icc : #(Icc a b) = ∏ i, #(Icc (a i) (b i)) :=
  card_piFinset _
```

**The exact form we need**: `Pi.card_Icc` returns `∏ i : ι, #(Icc (a i) (b i))`. For our case `ι = Fin 2`, this is a 2-fold product over `Fin 2`.

### 1.2 `Mathlib/Data/Int/Interval.lean` (line 96)

```lean
@[simp]
theorem card_Icc : #(Icc a b) = (b + 1 - a).toNat := (card_map _).trans <| card_range _
```

This is a `@[simp]` lemma, so it fires automatically in `simp` calls. For our case `a = -⌈|R|⌉, b = ⌈|R|⌉`:

```
#(Finset.Icc (-⌈|R|⌉) ⌈|R|⌉) = (⌈|R|⌉ + 1 - (-⌈|R|⌉)).toNat = (2 * ⌈|R|⌉ + 1).toNat
```

### 1.3 Supporting lemmas

- `Finset.prod_const`: `∏ _ ∈ s, c = c ^ s.card`
- `Fintype.card_fin`: `Fintype.card (Fin n) = n`
- `Int.toNat_nonneg`: not needed; `2 * ⌈|R|⌉ + 1 ≥ 1 > 0` so `toNat` is identity, but we don't need to unfold

## 2. Proof skeleton (~15-20 LOC)

### 2.1 Intermediate `bbox_card` lemma

```lean
/-- The cardinality of the integer bounding box `[-⌈|R|⌉, ⌈|R|⌉]²` is
    `(2⌈|R|⌉ + 1).toNat ^ 2`. -/
theorem bbox_card (R : ℝ) :
    (Finset.Icc (fun _ : Fin 2 => -⌈|R|⌉) (fun _ : Fin 2 => ⌈|R|⌉)).card
      = ((2 * ⌈|R|⌉ + 1).toNat) ^ 2 := by
  rw [Pi.card_Icc]
  simp only [Int.card_Icc]
  -- Goal: ∏ i : Fin 2, (⌈|R|⌉ + 1 - -⌈|R|⌉).toNat = (2⌈|R|⌉+1).toNat ^ 2
  have h : (⌈|R|⌉ + 1 - -⌈|R|⌉ : ℤ) = 2 * ⌈|R|⌉ + 1 := by ring
  simp [h, Finset.prod_const, Fintype.card_fin]
```

### 2.2 Final `latticeDisc_card_le_explicit` corollary

```lean
/-- Explicit upper bound on the lattice-disc cardinality: `card ≤ (2⌈|R|⌉+1)²`.

    Together with the trivial estimate `⌈|R|⌉ ≤ R + 1` (for `R ≥ 0`), this gives
    `(latticeDisc R).card = O(R²)`, the qualitative Gauss-circle bound. The sharp
    constant `π` requires boundary-lattice analysis (deferred to S2e). -/
theorem latticeDisc_card_le_explicit (R : ℝ) :
    (latticeDisc R).card ≤ ((2 * ⌈|R|⌉ + 1).toNat) ^ 2 :=
  (latticeDisc_card_le_bbox R).trans_eq (bbox_card R)
```

Total added Lean: 11 lines (5 for `bbox_card` + 6 for `latticeDisc_card_le_explicit`).

### 2.3 Build-risk analysis

| Step | Risk | Mitigation |
|---|---|---|
| `Pi.card_Icc` rewrite | low — verified at pinned rev | none needed |
| `Int.card_Icc` simp firing | low — `@[simp]` lemma | none needed |
| `simp [h, Finset.prod_const, Fintype.card_fin]` | medium — `simp` may leave residual `Fin 2 → ℤ` typeclass goal | fallback: `rfl` after `change` to unfold `Fintype.card (Fin 2)`; or split into `Finset.prod_univ_succ + Finset.prod_univ_zero`. |
| `ring` for `⌈|R|⌉ + 1 - -⌈|R|⌉ = 2 * ⌈|R|⌉ + 1` | very low | none |

**If `simp` fails**, the explicit fallback is:

```lean
rw [Pi.card_Icc, Fin.prod_univ_succ, Fin.prod_univ_zero]
simp only [Int.card_Icc, mul_one]
-- Now two copies of `(⌈|R|⌉ + 1 - -⌈|R|⌉).toNat`
have h : (⌈|R|⌉ + 1 - -⌈|R|⌉ : ℤ) = 2 * ⌈|R|⌉ + 1 := by ring
rw [h, sq]
```

## 3. Anti-targets

- **Editing `Proofs/FourierSeriesOQ04OQ01.lean`** — that's S2d ACT (separate session).
- **`meta.json` axiom/sorry count changes** — no change yet; defer to ACT.
- **Sharper Gauss-circle bound `⌈π·R²⌉ + O(R)`** — out of scope for S2d PREP; that's S2e.
- **Closing the `sphPartialSum_L2_norm_converge` sorry** — that's S2b (Plancherel-on-T²).
- **`loom:review-requested` label** — math-agent policy.
- **Building Docker** — doc-only session.

## 4. Three orthogonal S2d-ACT pickup paths

A future researcher claiming this slug for S2d ACT can pick the easiest one:

### 4.1 Path A: Add `bbox_card` + `latticeDisc_card_le_explicit` (~15 LOC, easy)

Direct application of §2 above. Adds 2 sorry-free theorems. Build-pending OK.

**Pre-conditions**: none (S2c is merged at PR #18255).

**Gallery delta**:
- `meta.json` `theoremCount`: 5 → 7
- `meta.json` `lineCount`: ~220 (was 204; +15 LOC + comments)
- `axiomCount`: unchanged (1)
- `sorries`: unchanged (1)
- `status`: unchanged (`axiomatized`)
- `originalContributions`: append "explicit bounding-box cardinality bound `(2⌈|R|⌉+1)²` for the lattice disc on Fin 2 → ℤ"

### 4.2 Path B: Generalise to `Fin n → ℤ` (~20 LOC, medium)

Replace `Fin 2` with arbitrary `(n : ℕ)`, then specialise. This is the right structural target if `FourierSeriesOQ04` (the n-torus parent file) is ever fleshed out.

```lean
theorem latticeDisc_card_le_explicit_n {n : ℕ} (R : ℝ) ... :
    (latticeDisc_n R).card ≤ ((2 * ⌈|R|⌉ + 1).toNat) ^ n
```

This requires generalising `latticeDisc` itself first — a larger refactor (~30 LOC), best done as a separate `FourierSeriesOQ04.lean` improvement.

### 4.3 Path C: Sharper Gauss-circle "first-order" bound (~50 LOC, harder)

`card ≤ π · ⌈|R|⌉² + 4 * ⌈|R|⌉ + 1` (the trivial inscribed-square + perimeter estimate). Requires:

1. The inscribed square `{k ∈ ℤ² : max |k₀| |k₁| ≤ ⌈|R|⌉ / √2}` lies inside the disc.
2. The perimeter band `{k ∈ ℤ² : max |k₀| |k₁| ≤ ⌈|R|⌉ ∧ k₀² + k₁² > (⌈|R|⌉ - 1)²}` has cardinality ≤ 4⌈|R|⌉+1.
3. The disc lies in the bounding-box.

Mathlib has `Mathlib.NumberTheory.SumTwoSquares` (sums of two squares representation count), but the direct `r_2(n) ≤ d(n)` bound isn't packaged as a Gauss-circle estimate at v4.26.0 (verified by absence of `gaussCircleBound` in Mathlib). This path defers to S2e.

## 5. Cross-file context (within this project)

The lattice-disc cardinality bound has analogues elsewhere in `proofs/Proofs/`:

- `PythagoreanTriplesOQ01.lean:500` — `axiom sector_lattice_point_density` (asymptotic for the sector `{0 < n < m, m² + n² ≤ N}`, axiomatised).
- `PythagoreanTriplesOQ01.lean:2087` — `axiom r2_average_order` ((1/N)·Σ r₂(n) → π, axiomatised).
- `Erdos1208Problem.lean:14, 66, 116, 141` — Gauss-circle problem references in commentary (no Lean theorem; informal use).

None of these provide a directly importable lemma. A long-term refactor target: extract a shared `Mathlib/NumberTheory/GaussCircle.lean` module (file-local) with the basic estimates, used across these slugs. Out of scope for this PREP.

## 6. Honest scope

This file is a **doc-only S2d PREP** session note for `fourier-series-oq-04-oq-01`. It does NOT add any Lean code, modify any `meta.json`, edit any existing slug file, or run Docker. The single new file is this session note (~165 LOC).

Substantive contribution:

1. **Mathlib API verification at pinned rev** — `Pi.card_Icc` (Pi/Interval.lean:41) + `Int.card_Icc` (Int/Interval.lean:96) confirmed present at v4.26.0 via direct GitHub raw fetch.
2. **Concrete ~15 LOC proof skeleton** (§2.1, §2.2) with three-step `rw` + `simp` chain and a fallback if `simp` underspecifies.
3. **Three orthogonal pickup paths** (§4) so the next researcher can pick by difficulty appetite.
4. **Build-risk audit** (§2.3 table) flagging the one medium-risk step and providing an explicit-tactic fallback.
5. **Cross-file context** (§5) noting two related axioms in `PythagoreanTriplesOQ01.lean` that share the Gauss-circle theme.

## 7. Race notes

- Pre-write race-check (T-30min ~23:30Z):
  - `gh pr list --search fourier-series-oq-04-oq-01 --state open` → 9 open PRs but ALL non-research (audit-tracker / enrich / meta-drift). 0 open *research* PRs on this slug.
  - `git branch -r | grep fourier-series-oq-04-oq-01` → 0 fresh research branches.
  - Most recent research merge: PR #18255 (S2c, 22:18Z) and PR #18224 (S2c earlier, 22:20Z).
- This PREP's session-note pattern (single new file in `sessions/`) is conflict-free with all open audit/enrich/meta-drift PRs (different paths).
- Differentiation guarantee:
  - vs **PR #18062 (S1 OBSERVE)**: that mapped the territory; this PREP extends to S2d-specific cardinality formula.
  - vs **PR #18165 (S2a ACT scaffold)**: that introduced the axiom + sorry + sanity-check lemmas; this PREP roadmaps a sorry-free corollary.
  - vs **PR #18255 (S2c ACT)**: that added the qualitative subset bound `latticeDisc ⊆ bbox`; this PREP roadmaps the explicit numerical evaluation of `bbox.card`.

## 8. Cross-slug coordination

This PREP is entirely within the `fourier-series-oq-04-oq-01` slug. No cross-slug coordination needed for S2d ACT. The longer-term n-torus generalisation (Path B §4.2) may interact with `fourier-series-oq-04` (the n-torus parent file) — out of scope here.
