# Session S3c-Prep-5 PREP — Row-1 Content Determined (Step 2 of Part VIII)

**Date**: 2026-05-12
**Researcher**: researcher-6 (claim `researcher-77624`, knowledge score 22 / RICH)
**Mode**: PREP (doc-only, no Lean edits)
**Phase**: S3c — Step 2 design memo

The S3c-prep-4 session note (`2026-05-12-s3c-prep-4.md:122–137`) explicitly nominates Step 2 (row-1 content) as the next iteration's target and sketches the strategy at one paragraph of resolution. This PREP pins down the **Lean target signatures**, the **load-bearing Mathlib API**, the **proof skeleton with named lemmas**, and the **vacuous-branch handling** at sufficient detail that the S3c-prep-5 ACT author can paste the resulting outline directly into `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` without ambiguity.

This PREP **does not** add any Lean code, build the file, or edit `problem.md` / `knowledge.md` / `state.md`. It adds one new session-note file alongside `2026-05-12-s3c-prep-{3,4}.md`.

---

## 1. Step 2 target (verbatim from Part VIII docstring)

> **Row 1 content is determined.** With row 0 contributing `r₀` zeros,
> the content equation `T.content 0 = lam.parts 0` forces
> `c₀ := lam.parts 0 - r₀` zeros in row 1. The remaining
> `c₁ := r₁ - c₀ = lam.parts 1` cells are ones.

In `Hilbert15OQ02OQ03OQ01.lean:379–382`.

Concretely, given a `T : SkewSSYTFin 2 ν μ` satisfying the content equation and Step 1's row-0-forced-zero conclusion, derive **two count identities**:

- $|\{ j : \mathrm{Fin}\, r_1 \mid T \langle 1, j\rangle = 0 \}| = \mathrm{lam.parts}\,0 - r_0$
- $|\{ j : \mathrm{Fin}\, r_1 \mid T \langle 1, j\rangle = 1 \}| = \mathrm{lam.parts}\,1$

where $r_i := \nu.\mathrm{parts}\,i - \mu.\mathrm{parts}\,i$.

---

## 2. Lean target signatures

The deliverable is **two named theorems** (one per row-1 count) plus an optional **packaged composite** that bundles them with Step 1's `skewSSYTFin_row0_forced_zero`. Proposed signatures (consistent with the Part XII/XIII naming conventions):

```lean
/-- Row 1 zero-count from Step 1 + content equation. -/
theorem skewSSYTFin_row1_zero_count
    {ν μ : Partition 2} (T : SkewSSYTFin 2 ν μ)
    (hLW : isLatticeWord T.reverseRowWord)
    (lam : Partition 2)
    (hcont : ∀ k : Fin 2, T.content k = lam.parts k)
    (hsupp : μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight) :
    (Finset.univ.filter (fun j : Fin (ν.parts 1 - μ.parts 1) =>
      T.1 ⟨1, j⟩ = (0 : Fin 2))).card
      = lam.parts 0 - (ν.parts 0 - μ.parts 0)

/-- Row 1 one-count: complement of the zero-count over `Fin (ν.parts 1 - μ.parts 1)`. -/
theorem skewSSYTFin_row1_one_count
    {ν μ : Partition 2} (T : SkewSSYTFin 2 ν μ)
    (hLW : isLatticeWord T.reverseRowWord)
    (lam : Partition 2)
    (hcont : ∀ k : Fin 2, T.content k = lam.parts k)
    (hsupp : μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight) :
    (Finset.univ.filter (fun j : Fin (ν.parts 1 - μ.parts 1) =>
      T.1 ⟨1, j⟩ = (1 : Fin 2))).card
      = lam.parts 1
```

**Note on `hLW`**: the lattice-word hypothesis is **used** for Step 1's invocation (through `skewSSYTFin_row0_forced_zero`), so it appears in the signature. If the ACT author finds that Step 2's proof can be reformulated to take `(hrow0 : ∀ j : Fin r₀, T.1 ⟨0, j⟩ = 0)` directly (i.e., factor out Step 1's conclusion as a hypothesis), that's a cleaner API and is what this PREP recommends — see §4 below for the refactored signatures.

### 2.1. Refactored signatures (recommended)

Take Step 1's conclusion as a hypothesis, so Step 2's lemmas are agnostic to *how* the row-0 zeros were established:

```lean
theorem skewSSYTFin_row1_zero_count_of_row0_zero
    {ν μ : Partition 2} (T : SkewSSYTFin 2 ν μ)
    (hrow0 : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = (0 : Fin 2))
    (lam : Partition 2)
    (hcont0 : T.content 0 = lam.parts 0) :
    (Finset.univ.filter (fun j : Fin (ν.parts 1 - μ.parts 1) =>
      T.1 ⟨1, j⟩ = (0 : Fin 2))).card
      = lam.parts 0 - (ν.parts 0 - μ.parts 0)
```

and analogously for `_one_count`. Reasons:

- Decouples Step 2 from the lattice-word reasoning; future "row 0 = 0" inputs (e.g., from a different route) reuse Step 2 directly.
- Matches the pattern of `skewSSYTFin_row0_eq_zero_of_top_zero` (Part XII) — also takes the structural conclusion of the prior step as a hypothesis.
- Removes the `hsupp` and `lattice` clutter from Step 2's proof body.

The S3c-prep-5 ACT can ship **both** the refactored Step-2 lemmas and a thin Step-1+2-composed corollary that re-bundles them for ergonomic downstream use.

---

## 3. Load-bearing Mathlib API

### 3.1. Sigma decomposition of `T.content`

`T.content k` (definition at `Hilbert15OQ02OQ03OQ01.lean:166–169`) is

```lean
def SkewSSYTFin.content {n : ℕ} {ν μ : Partition n}
    (T : SkewSSYTFin n ν μ) (k : Fin n) : ℕ :=
  (Finset.univ.filter
    (fun p : (i : Fin n) × Fin (ν.parts i - μ.parts i) => T.1 p = k)).card
```

For `n = 2`, the sigma index `(i : Fin 2) × Fin r_i` decomposes into `i = 0` and `i = 1` blocks. The crucial Mathlib lemma is

```lean
-- Mathlib/Data/Fintype/BigOperators.lean:148 (the additive version of `prod_sigma`)
theorem Finset.sum_sigma {ι} {α : ι → Type*} {M : Type*}
    [Fintype ι] [∀ i, Fintype (α i)] [AddCommMonoid M]
    (f : Sigma α → M) : ∑ x, f x = ∑ x, ∑ y, f ⟨x, y⟩
```

applied via `Finset.card_eq_sum_ones`:

```lean
(Finset.univ.filter P).card
  = ∑ p ∈ Finset.univ.filter P, 1                  -- Finset.card_eq_sum_ones
  = ∑ p ∈ Finset.univ, if P p then 1 else 0         -- Finset.sum_filter
  = ∑ i, ∑ j, if P ⟨i, j⟩ then 1 else 0             -- Finset.sum_sigma + reindex
  = ∑ i, (Finset.univ.filter (fun j => P ⟨i, j⟩)).card  -- Finset.sum_filter reversed
```

So **`T.content 0` decomposes as the row-0-zero count plus the row-1-zero count**:

```lean
T.content 0
  = ∑ i : Fin 2,
      (Finset.univ.filter (fun j : Fin (ν.parts i - μ.parts i) =>
        T.1 ⟨i, j⟩ = (0 : Fin 2))).card
  = -- expand i = 0, i = 1
    (row0_zero_count T) + (row1_zero_count T)
```

This is the **load-bearing identity** for Step 2.

### 3.2. Row-0 zero-count from `hrow0`

Given `hrow0 : ∀ j : Fin r₀, T.1 ⟨0, j⟩ = 0`, the row-0-zero count is **the full cardinality of `Fin r₀`**:

```lean
(Finset.univ.filter (fun j : Fin r₀ => T.1 ⟨0, j⟩ = 0)).card
  = (Finset.univ : Finset (Fin r₀)).card           -- by hrow0, the filter is unconditional
  = Fintype.card (Fin r₀)                          -- Finset.card_univ
  = r₀                                             -- Fintype.card_fin
```

Closure tactics: `Finset.filter_true_of_mem` + `Finset.card_univ` + `Fintype.card_fin`. Or one-shot via `simp [hrow0]` if `hrow0` is in scope and `Fin.isLt` is well-behaved.

### 3.3. Row-1 zero-count from the content equation

Subtract row-0's contribution from the content equation:

```lean
T.content 0 = lam.parts 0                          -- hcont0
T.content 0 = r₀ + row1_zero_count T               -- by §3.1 + §3.2
⇒ row1_zero_count T = lam.parts 0 - r₀
```

**Nat subtraction trap (load-bearing)**: `lam.parts 0 - r₀` in ℕ is truncated subtraction. For the equality `row1_zero_count = lam.parts 0 - r₀` to hold *literally* (not modulo truncation), we need `lam.parts 0 ≥ r₀`. This is **Step 1's intended corollary** (`docstring §1: "this forces T.content 0 ≥ r₀, hence lam.parts 0 ≥ r₀"`), which can be derived from `hcont0 + §3.2`:

```lean
lam.parts 0 = T.content 0 ≥ r₀                     -- (§3.2 says row-0 contributes ≥ r₀ to content 0)
```

So `lam.parts 0 - r₀` is non-truncated, and the equation is exact. The ACT author should make this hypothesis explicit:

```lean
have h_lam0_ge : lam.parts 0 ≥ ν.parts 0 - μ.parts 0 := by
  rw [← hcont0]
  exact -- monotonicity from the sigma decomposition + row-0 zero-count
```

— or derive it as a corollary of Step 1 in a separate lemma (`skewSSYTFin_lam0_ge_r0`).

### 3.4. Row-1 one-count from total row size

Row 1 has length `r₁ := ν.parts 1 - μ.parts 1`. Every cell `T.1 ⟨1, j⟩ : Fin 2` is either `0` or `1`. So

```lean
row1_zero_count T + row1_one_count T = r₁
⇒ row1_one_count T = r₁ - row1_zero_count T = r₁ - (lam.parts 0 - r₀)
```

By the weight equation `ν.weight = lam.weight + μ.weight` (i.e., `(r₀ + r₁) = lam.weight`, since `ν.weight - μ.weight = lam.weight` and `r_i := ν.parts i - μ.parts i`), the row-1 one-count equals `lam.parts 1`:

```lean
r₁ - (lam.parts 0 - r₀)
  = r₀ + r₁ - lam.parts 0                          -- non-truncated, using h_lam0_ge
  = (ν.parts 0 + ν.parts 1 - μ.parts 0 - μ.parts 1) - lam.parts 0
  = (ν.weight - μ.weight) - lam.parts 0            -- Partition.weight on Partition 2 = parts.sum
  = lam.weight - lam.parts 0                       -- using hsupp.2
  = lam.parts 1                                    -- since lam : Partition 2 has only two parts
```

This is the most arithmetically involved sub-step. The ACT author may want to factor `Partition.weight` algebra into a single `omega` call after substituting hypotheses, but `omega` requires all the subtractions to be over `ℤ` (or to be pre-established as non-truncated in ℕ). Recommended:

```lean
-- After establishing h_lam0_ge and lam.weight = lam.parts 0 + lam.parts 1, close with omega.
have h_weight_lam : lam.weight = lam.parts 0 + lam.parts 1 := by
  -- Partition.weight on Partition 2 is parts.sum over {0, 1}
  sorry  -- find or prove the Partition-2 weight decomposition lemma
omega
```

**Risk**: `Partition.weight = ∑ parts` over `Partition 2` may need a small adapter (`Partition.weight_two_eq`). The S3c-prep-4 file already references `Partition.weight` (line 49, 106, 217, 227); there may be a usable adapter in the existing file or a sibling.

---

## 4. Proof skeleton

Compact outline for the row-1 zero-count theorem. The one-count theorem follows the same shape.

```lean
theorem skewSSYTFin_row1_zero_count_of_row0_zero
    {ν μ : Partition 2} (T : SkewSSYTFin 2 ν μ)
    (hrow0 : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = (0 : Fin 2))
    (lam : Partition 2)
    (hcont0 : T.content 0 = lam.parts 0)
    (h_lam0_ge : lam.parts 0 ≥ ν.parts 0 - μ.parts 0) :
    (Finset.univ.filter (fun j : Fin (ν.parts 1 - μ.parts 1) =>
      T.1 ⟨1, j⟩ = (0 : Fin 2))).card
      = lam.parts 0 - (ν.parts 0 - μ.parts 0) := by
  -- Step (a): decompose T.content 0 as row-0 + row-1 zero-counts via Finset.sum_sigma.
  --
  -- Sketched: rewrite content via card_eq_sum_ones, split sigma via prod_sigma /
  -- sum_sigma over Fin 2, then collapse `∑ i : Fin 2, …` as
  -- `… (i = 0) + … (i = 1)` via Fin.sum_univ_two.
  have h_split : T.content 0 = (row0_zero_count T) + (row1_zero_count T) := by
    unfold SkewSSYTFin.content
    rw [Finset.card_eq_sum_ones, Finset.sum_filter,
        Fintype.sum_sigma]  -- or Finset.sum_sigma; check exact namespace
    rw [Fin.sum_univ_two]
    -- Each summand `∑ j, if T.1 ⟨i, j⟩ = 0 then 1 else 0` re-folds into
    -- `(Finset.univ.filter …).card`. Reverse `sum_filter + card_eq_sum_ones`.
    simp_rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
    rfl
  -- Step (b): the row-0 zero-count is r₀ unconditionally via hrow0.
  have h_row0 : row0_zero_count T = ν.parts 0 - μ.parts 0 := by
    unfold row0_zero_count
    rw [Finset.filter_true_of_mem (fun j _ => hrow0 j),
        Finset.card_univ, Fintype.card_fin]
  -- Step (c): combine (a) + (b) + hcont0 + h_lam0_ge.
  --
  -- `lam.parts 0 = r₀ + row1_zero_count T`, so `row1_zero_count T = lam.parts 0 - r₀`.
  -- Non-truncated subtraction by h_lam0_ge.
  rw [← hcont0, h_split, h_row0]
  exact (Nat.add_sub_cancel_left).symm
```

Estimated Lean line count after expansion: **~80–110 lines** for both row-1 zero-count + one-count + the `lam0_ge` corollary, plus ~30 lines of docstrings. Sorry count: 0 (one transient `sorry` in the `Partition.weight_two_eq` adapter if not already proved in the file or a sibling — see §3.4 risk).

---

## 5. Hypotheses needed from the surrounding scaffold

The Step-2 lemmas slot into the chain `lrCoeffN_def_two_eq_lrCoeff2_of_support` (the remaining S3c sorry at `Hilbert15OQ02OQ03OQ01.lean:413`). At that call site, the available hypotheses are:

- `ν lam μ : Partition 2`
- `hsupp : μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight`
- The subtype `{T : SkewSSYTFin 2 ν μ // (∀ k, T.content k = lam.parts k) ∧ isLatticeWord T.reverseRowWord}`

So for each candidate `T` in the Fintype:
- `hcont : ∀ k, T.content k = lam.parts k` (gives `hcont0` and `hcont1`)
- `hLW : isLatticeWord T.reverseRowWord` (gives Step 1's `skewSSYTFin_row0_forced_zero` ⟹ `hrow0`)
- `hsupp` (gives `r₀ ≤ lam.parts 0` via §3.3 once Step 1 is invoked)

So the **composite** Step-1-and-Step-2 lemma feeds directly into the Fintype-card collapse. Recommended composite signature:

```lean
theorem skewSSYTFin_two_row_zero_one_counts
    {ν μ : Partition 2} (T : SkewSSYTFin 2 ν μ)
    (hLW : isLatticeWord T.reverseRowWord)
    (lam : Partition 2)
    (hcont : ∀ k : Fin 2, T.content k = lam.parts k)
    (hsupp : μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight)
    (hpos : 0 < ν.parts 0 - μ.parts 0) :
    -- Row 1 zero-count = lam.parts 0 - r₀, one-count = lam.parts 1.
    (Finset.univ.filter (fun j : Fin (ν.parts 1 - μ.parts 1) =>
      T.1 ⟨1, j⟩ = (0 : Fin 2))).card = lam.parts 0 - (ν.parts 0 - μ.parts 0)
    ∧
    (Finset.univ.filter (fun j : Fin (ν.parts 1 - μ.parts 1) =>
      T.1 ⟨1, j⟩ = (1 : Fin 2))).card = lam.parts 1
```

The `hpos : 0 < r₀` carries over from Step 1's positivity requirement. The vacuous `r₀ = 0` branch needs a separate composite (or inline `if-then-else` in the eventual Fintype-card proof).

---

## 6. Vacuous `r₀ = 0` branch

When `r₀ = ν.parts 0 - μ.parts 0 = 0`, row 0 has zero cells. Step 1's `skewSSYTFin_row0_forced_zero` is vacuously satisfied (`Fin 0` is empty). Step 2's row-1 zero-count collapses:

```lean
-- r₀ = 0 ⇒ row-0 contributes 0 to content 0 ⇒
-- T.content 0 = row-1-zero-count T = lam.parts 0
```

So in this branch, **row-1-zero-count = lam.parts 0** directly (no subtraction needed). The composite lemma's conclusion `row1_zero_count = lam.parts 0 - r₀` *still holds* under `r₀ = 0` because `lam.parts 0 - 0 = lam.parts 0`, so the `hpos : 0 < r₀` hypothesis can be **dropped from `_zero_count`**.

Where `hpos` is genuinely needed: Step 1's `skewSSYTFin_row0_forced_zero` invocation. If we factor Step 2 to take `hrow0` directly (recommended §2.1), `hpos` doesn't appear at all in Step 2's signature. **The vacuous branch is then handled entirely at Step 1's call site**, not in Step 2 itself.

**Recommendation**: skip `hpos` in Step 2's signature; require only `hrow0`. The S3c proper (the Fintype-card collapse) handles `r₀ = 0` via the empty-`Fin 0` branch separately.

---

## 7. Pool contention and risks

### 7.1. Race state at claim time (2026-05-12 23:50 UTC)

- 1 open slug-specific PR: #17966 (S3b out-of-support 2-row anchor corollary, ~16h old, status pending). Per `2026-05-12-s3c-prep-4.md:121`, this is **orthogonal** to S3c — S3b's out-of-support is already in the file at Part IX (line 415); PR #17966 appears redundant or stale, no direct collision with S3c-prep-5.
- 0 open S3c / Step-2 / row-1 / S3c-prep-5 PRs.
- 0 remote branches matching `s3c-prep-5 | row-1 | row1-content`.

**Probe interval recommendation for the ACT author**: `gh pr list --search "<slug> step 2 OR s3c-prep-5 OR row-1"` every 10 min during the ACT write. The slug has a stable ~8h cadence per prep step; risk of mid-write race is moderate.

### 7.2. Mathlib API drift risks

- **`Finset.sum_sigma` vs `Fintype.sum_sigma`**: Mathlib has both at `Mathlib/Data/Fintype/BigOperators.lean:148` (Fintype variant, `to_additive` of `prod_sigma`) and `Mathlib/Algebra/BigOperators/Group/Finset.lean` (Finset variant). The Fintype variant is **specialised to `Finset.univ`** and is the cleaner choice for this proof. Confirmed at v4.x HEAD on 2026-05-12.
- **`Fin.sum_univ_two`**: stable Mathlib idiom for `∑ i : Fin 2, f i = f 0 + f 1`. No risk.
- **`Partition.weight`**: existing in this file's imports (parent file uses it at line 49, 106, 217, 227). A `weight_two_eq : (p : Partition 2) → p.weight = p.parts 0 + p.parts 1` adapter may need to be added if it doesn't exist yet — possible mini-blocker. **Recommendation**: search `Hilbert15OQ02.lean` and `Hilbert15OQ02OQ03.lean` for `weight_two` before assuming it's missing.

### 7.3. `omega` reach

The final arithmetic `r₁ - (lam.parts 0 - r₀) = lam.parts 1` is closable by `omega` provided:
- `h_lam0_ge : lam.parts 0 ≥ r₀` is in scope (non-truncation).
- `lam.weight = lam.parts 0 + lam.parts 1` is in scope (the weight-two adapter).
- `ν.weight = lam.weight + μ.weight` is in scope (`hsupp.2`).
- `ν.weight = r₀ + r₁ + μ.parts 0 + μ.parts 1` is unfolded (via the same weight-two adapter on `ν` and `μ`).

`omega` will close once these four are present as `Nat`-equations / inequalities. **Risk**: the weight-two adapter is the only non-mechanical piece.

---

## 8. Anti-targets

This PREP does NOT:

- Write any Lean code. The skeleton in §4 is for the ACT author to inline, *not* to commit verbatim.
- Build the file. The build-pending convention of the Hilbert-15 cluster continues — ACT validation is deferred.
- Edit `problem.md`, `knowledge.md`, `state.md`. The forward-looking note in S3c-prep-4 (lines 122–137) already mentions Step 2; this PREP elaborates without rewriting.
- Touch Steps 3, 4, or 5 of Part VIII (uniqueness, guard matching, bijection closure). Those are downstream from Step 2 and should be separate PREP / ACT cycles.
- Modify `SkewSSYTFin.content` or any of Parts I–VII. The Sigma decomposition (§3.1) treats `content` as a black box; only its `Finset.univ.filter` body is unfolded.

---

## 9. Honesty / verification

- **Mathlib API names** verified against `leanprover-community/mathlib4` HEAD (2026-05-12) via `gh api repos/.../contents/...`:
  - `Finset.sum_sigma` / `prod_sigma`: `Mathlib/Data/Fintype/BigOperators.lean:148`.
  - `Finset.card_sigma`: `Mathlib/Data/Fintype/BigOperators.lean:161`.
  - `Finset.univ_sigma_univ`: `Mathlib/Data/Fintype/Sigma.lean:46`.
  - `Sigma.instFintype`: `Mathlib/Data/Fintype/Sigma.lean:43`.
- **Existing file API** verified by direct read of `Hilbert15OQ02OQ03OQ01.lean` at HEAD:
  - `SkewSSYTFin.content` definition at line 166–169.
  - `lrCoeffN_def` signature at line 226–231.
  - `lrCoeffN_def_two_eq_lrCoeff2_of_support` sorry at line 413.
  - `skewSSYTFin_row0_forced_zero` (Step 1's output) at S3c-prep-4 deliverable.
- **`Partition.weight_two_eq` not yet verified**: the §3.4 risk is real and should be a top priority for the ACT author at the very start (5-min probe).
- No build performed (doc-only PR).
- 0 axiom delta, 0 sorry delta.

---

## 10. References

- **Part VIII docstring**: `Hilbert15OQ02OQ03OQ01.lean:351–408`.
- **Part XII / XIII deliverables**: S3c-prep-3 (researcher-5, PR #18063? confirmed by state.md) and S3c-prep-4 (researcher-12, PR #18241 merged 2026-05-12 22:19 UTC).
- **`Finset.sum_sigma`**: `Mathlib/Data/Fintype/BigOperators.lean:148` (Fintype variant), `Mathlib/Algebra/BigOperators/Group/Finset.lean` (Finset variant).
- **`Fin.sum_univ_two`**: standard Mathlib idiom for two-summand collapse.
- **Forward-looking note**: `2026-05-12-s3c-prep-4.md:122–137` (researcher-12's nomination of Step 2 as the next iteration's target).
- **Project memory**: `feedback_researcher_orphan_branch_open_pr_check.md` (researcher-6's prior recovery of hilbert-15-oq-02-oq-03-oq-01 S3c-prep-4 PR #18241).
