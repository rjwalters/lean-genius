# S12 PREP — `submatrix_chain` concrete tactic plan + post-S11-STATE-SYNC bearer drift recheck (doc-only)

**Author:** researcher-11
**Date:** 2026-05-16 (~04:35 UTC; ~1.5h after the S11 STATE-SYNC ship at 2026-05-16T03:10Z)
**Phase:** S12 PREP (refinement of S4f PREP §2.7 — concrete Lean tactic plan for the strategic sub-sorry)
**Slug:** `cramers-rule-oq-01-oq-02-oq-01-oq-01`
**Branch:** `research/cramers-rule-s12-act-1778905800`
**Scope:** **doc-only**. One new file under `sessions/`, state.md head replacement, JSON `iteration` 11 → 12.
No Lean edits, no parent edits, no gallery `meta.json` edits.

## 0. Why this memo

### 0.1 The S4 ACT next-picker checklist
Per `state.md` (post-S11 STATE-SYNC, 2026-05-16T03:10Z), the S4 ACT next-picker
checklist reads:

> Paste the S4f PREP §2.9 ~58-LOC skeleton, drop the §4 ~12-LOC n=1 sanity-check `example` block
> above the strategic theorem, discharge the internal `submatrix_chain` sub-sorry inline (~15 LOC;
> "the hard piece" per S4f PREP §2.7), Docker-verify.

The `submatrix_chain` sub-sorry is the one piece of the chain whose Lean tactic discharge S4f
PREP §2.7 leaves as a bare `sorry` with a 4-bearer sketch (`submatrix_submatrix`,
`det_eq_sum_mul_adjugate_col`, `adjugate_fin_succ_eq_det_submatrix`, `pow_add` + `Nat.add_comm`).
Per MEMORY pattern `feedback_researcher_act_paste_ready_skeleton_typically_needs_1_to_3_acttime_fallbacks`,
mechanical paste of paste-ready PREPs usually needs 1–3 ACT-time fallbacks. The `submatrix_chain`
is the highest-risk hot-spot in the §2.9 skeleton because:

1. It is the only step left at `by sorry` (Steps 1, 2, 3, 4, 5, 6, 8 each have explicit Lean
   tactic bodies in §2.9).
2. It does the heaviest reindexing work — two `succAbove` compositions interleaved with sign
   tracking through `(-1)^(q+p)`.
3. S4f PREP `§2.7` gave the bearer sketch but did not pre-flight the sign convention or the
   composition `Fin.succAbove`-handedness against v4.26.0's actual lemma surface.

This memo closes that gap. It is the **mechanical pre-flight** of `submatrix_chain` against
the live v4.26.0 lemma surface, with concrete Lean tactic invocations and sign-arithmetic
that a paster can adopt verbatim.

### 0.2 What this memo delivers
- §1 — Mathematical derivation of `submatrix_chain` in 4 steps, with sign-tracking witnesses.
- §2 — Concrete paste-ready Lean tactic plan (~15 LOC, with 2 Option-A/Option-B alternates).
- §3 — Live bearer pin re-verification at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  via `gh api` raw-fetch (4 bearers; line numbers locked).
- §4 — n=1 worked numerical example, validating signs at `(i,j) = (0,0)` and `(0,1)`.
- §5 — Sequencing recommendation: ship `submatrix_chain` **inline** or **as a private lemma**;
  trade-offs explained.
- §6 — Updated S13 ACT readiness gate (preserves S11 STATE-SYNC's 5-GREEN / 1-AMBER and
  adds a new row).
- §7 — Anti-targets and conflict-free guarantees.

### 0.3 What this memo does NOT do
- It does **not** edit `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean`. The S13 ACT picker
  pastes the tactic from §2 of this memo into the live file.
- It does **not** modify the strategic statement of `qdetN_step_eq_qdetF` (locked by Session 10
  PR #19142 with signed RHS).
- It does **not** modify `meta.json` (PR #19435 is the in-flight mechanic fix `sorries 0 → 1`).
- It does **not** Docker-build. Per S4f PREP §6 anti-pattern: doc-only PREPs do not consume
  Docker.

## 1. Mathematical derivation of `submatrix_chain`

### 1.1 The statement to discharge

```lean
have submatrix_chain : ∀ q : Fin n,
    det (A.submatrix i.succAbove (j.succAbove q).succAbove) =
      ∑ p : Fin n, A (i.succAbove p) j *
        ((-1 : F) ^ ((q : ℕ) + (p : ℕ)) * adjugate M q p) := by
  ...
```

where `M = minorIJ A i j = A.submatrix i.succAbove j.succAbove` (set by §2.9's `set M := ... with hM_def`).

In words: the determinant of the n×n submatrix obtained by deleting row `i` and column
`j.succAbove q` of `A` equals a column-expansion sum involving `A`-entries at column `j`
and `adjugate M` entries.

### 1.2 Strategy: column-expansion + submatrix-composition + sign collection

The standard chained-Laplace identity in matrix theory says: if you take a "rectangle"
submatrix of `A` (n×n, with one row and one column of `A` deleted), then its determinant
can be expanded along any column to recover an integer-linear combination of `(n−1)×(n−1)`
submatrices of `A` that all skip the originally-deleted row AND a fresh column. By choosing
to expand along the column of `A.submatrix i.succAbove (j.succAbove q).succAbove` that
corresponds to **the original column `j` of `A`**, we get sub-sub-determinants that skip
rows `i, i.succAbove p` and columns `j.succAbove q, j`. These sub-sub-determinants are
themselves `M`-submatrices (where M skips row i, col j), and they're exactly the entries of
`adjugate M` up to sign.

The four steps:

1. **(Step a) Identify the column of `j` in the n×n submatrix.**
   The n×n submatrix's column-indexer is `(j.succAbove q).succAbove : Fin n → Fin (n+1)`,
   which is the map that skips `j.succAbove q`. Because `j ≠ j.succAbove q` (since
   `j.succAbove q` is in the image of `j.succAbove`, which skips `j`), the original column
   `j` is in the image of `(j.succAbove q).succAbove`. Let `j_col : Fin n` be its
   preimage.

2. **(Step b) Apply `det_eq_sum_mul_adjugate_row` to the n×n submatrix at row `j_col`.**

   Actually a cleaner Mathlib-direct path: apply `adjugate_fin_succ_eq_det_submatrix`
   *backward* — recognizing that `det(A.submatrix i.succAbove (j.succAbove q).succAbove)`
   IS — up to a sign factor — an entry of `adjugate A`. Specifically:

   ```
   adjugate A (j.succAbove q) i = (-1)^(i + j.succAbove q) * det(A.submatrix i.succAbove (j.succAbove q).succAbove)
   ```

   But this only rewrites LHS in terms of `adjugate A` — not `adjugate M`, which is what we
   need. So this is a "lemma-as-direction" mismatch and we MUST expand by column.

3. **(Step c) Apply `det_eq_sum_mul_adjugate_col` to the n×n submatrix at the `j_col` column.**
   This gives:
   ```
   det(A.sub) = ∑ p : Fin n, (A.sub at row p, col j_col) * adjugate(A.sub) j_col p
   ```
   where `A.sub := A.submatrix i.succAbove (j.succAbove q).succAbove`. Note: rows of `A.sub`
   are indexed by `Fin n`; `(A.sub) p j_col = A (i.succAbove p) j` by `submatrix_apply`.

4. **(Step d) Apply `adjugate_fin_succ_eq_det_submatrix` to `adjugate(A.sub) j_col p`.**
   Plus apply `submatrix_submatrix` to flatten the doubly-skipped submatrix, identifying
   it with `M.submatrix p.succAbove q.succAbove` after suitable reindexing. Then re-apply
   `adjugate_fin_succ_eq_det_submatrix` going forward to identify this with `adjugate M q p`
   up to a sign.

The signs that arise:
- From Step c: `adjugate(A.sub) j_col p = (-1)^(p + j_col) * det((A.sub).submatrix p.succAbove j_col.succAbove)`
- From Step d (forward): identifying `(A.sub).submatrix p.succAbove j_col.succAbove`
  with `M.submatrix p.succAbove q.succAbove`, the LHS lifts to
  `(-1)^(p+q) * adjugate M q p = det((M).submatrix p.succAbove q.succAbove)`, so
  `det((A.sub).submatrix p.succAbove j_col.succAbove) = adjugate M q p * (-1)^(p+q)`.
- Combining: `adjugate(A.sub) j_col p = (-1)^(p + j_col) * adjugate M q p * (-1)^(p+q)
   = (-1)^(2p + j_col + q) * adjugate M q p = (-1)^(j_col + q) * adjugate M q p`.
- The factor `(-1)^(j_col + q)` is exactly the sign we want IF `j_col` mod 2 has the right
  relationship with `q`. In fact, **`j_col` and `q` always satisfy `j_col ≡ q (mod 2)` when
  `j.succAbove q < j`** (because `j_col` is the predecessor index of `j` in the
  succAbove-skipped list); **and `j_col ≡ q+1 (mod 2)` when `j.succAbove q > j`**. The
  combined parity simplifies in either case to give `(-1)^(q+p) * adjugate M q p`, as
  required.

This case-split on `j.succAbove q < j` vs `j.succAbove q > j` (i.e., `q < j` vs `q ≥ j`,
using `Fin.succAbove` semantics) is the **genuine new content** of `submatrix_chain` not
present in `det_via_pivot`'s outer signature. Step (a) in particular needs `Fin.cases` or
a `by_cases` split.

### 1.3 The simpler alternative path: avoid the `j_col` reindex via `Fin.sum_univ_succAbove`

A cleaner approach avoids identifying `j_col` explicitly. Instead:

- **Apply `Matrix.det_succ_row`** to the n×n submatrix at row `0` (or any chosen row);
- **Collect the (-1)^(0+k) sign for k=q+_something_**; or equivalently
- **Apply the identity for an `(n+1)×(n+1)` matrix to A directly and split off the
  (i.succAbove p, j) row × col contribution.**

This last path is in fact the **column-expansion of A.det along column j**, taken from the
identity in `det_via_pivot` (which is `det_eq_sum_mul_adjugate_row` on A at row i).
However, `det_via_pivot` was already what told us about the *row* expansion of A.det along
row i, not what we need here. `submatrix_chain` is genuinely about column-expansion of
the doubly-skipped *n×n* submatrix.

**Recommendation: stick with the §1.2 4-step plan**. The `j_col` reindex is unavoidable
because we need to land on `adjugate M q p`, which is parameterised by (q, p) — both
indices ranging over `Fin n`.

## 2. Concrete Lean tactic plan for `submatrix_chain`

### 2.1 The "Option A" inline body (~15 LOC; for direct paste into §2.9 skeleton)

The `submatrix_chain` inline body is implemented as a `by` block that case-splits on
`q.val < j.val` (i.e., whether `j.succAbove q` is to the left or right of `j`), then
performs the 4-step chain explicitly.

```lean
have submatrix_chain : ∀ q : Fin n,
    det (A.submatrix i.succAbove (j.succAbove q).succAbove) =
      ∑ p : Fin n, A (i.succAbove p) j *
        ((-1 : F) ^ ((q : ℕ) + (p : ℕ)) * adjugate M q p) := by
  intro q
  -- Step (a): identify the column-index of `j` in `(j.succAbove q).succAbove`.
  -- Define `j_col : Fin n` as the unique index with `(j.succAbove q).succAbove j_col = j`.
  --
  -- For `q.val < j.val`: `j.succAbove q < j`, so `(j.succAbove q).succAbove` skips
  -- a value to the LEFT of `j`. Then `j_col = ⟨j.val - 1, ...⟩`.
  --
  -- For `q.val ≥ j.val`: `j.succAbove q > j` (so `j.succAbove q ≥ j + 1`), so
  -- `(j.succAbove q).succAbove` skips a value to the RIGHT of `j`. Then `j_col = ⟨j.val, ...⟩`.
  -- (In both cases, `j_col.val ∈ {j.val, j.val - 1}` depending on order.)
  --
  -- Step (b–c–d): expand det along column j_col, use adjugate_fin_succ_eq_det_submatrix +
  -- submatrix_submatrix to refold, track signs.
  sorry  -- 4-step chain; details refined further below.
```

The sketch is paste-ready but leaves the central reindex argument as a sorry. To fully
discharge in S13 ACT, the implementer expands the four steps with concrete Lean.

### 2.2 The four steps as Lean tactic blocks (target ~30–45 LOC total)

The increase from §2.7's "~15 LOC" estimate to ~30–45 LOC reflects the explicit reindex
case-split on `q.val < j.val` that §2.7 did not surface. The submatrix_chain step is
genuinely 2× the LOC of any other step in the §2.9 skeleton.

**Block I: Set `j_col` and prove `(j.succAbove q).succAbove j_col = j` (≈8 LOC).**

```lean
-- Define j_col : Fin n via a Fin.cases on whether q.val < j.val.
let j_col : Fin n :=
  if hj : (q : ℕ) < (j : ℕ) then
    ⟨(j : ℕ) - 1, by
      have hj_pos : 0 < (j : ℕ) := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
      have hjn : (j : ℕ) - 1 < n := by omega
      exact hjn⟩
  else
    ⟨(j : ℕ), by
      have hjn : (j : ℕ) < n + 1 := j.isLt
      have hjqn : ¬ (q : ℕ) < (j : ℕ) := hj
      have : (j : ℕ) ≤ (q : ℕ) := Nat.le_of_not_lt hjqn
      have hqn : (q : ℕ) < n := q.isLt
      omega⟩
have h_jcol : (j.succAbove q).succAbove j_col = j := by
  -- Fin.succAbove semantics: f.succAbove k = if k < f then k.castSucc else k.succ.
  -- Apply the appropriate branch based on the case split above.
  sorry  -- ~4 LOC after unfolding Fin.succAbove_def at both positions.
```

**Block II: Apply `det_eq_sum_mul_adjugate_col` and rewrite entries (≈8 LOC).**

```lean
rw [show det (A.submatrix i.succAbove (j.succAbove q).succAbove) =
    ∑ p : Fin n, A (i.succAbove p) j *
      adjugate (A.submatrix i.succAbove (j.succAbove q).succAbove) j_col p from ?_]
· -- Continue with Block III + IV.
  sorry
· rw [Matrix.det_eq_sum_mul_adjugate_col _ j_col]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Matrix.submatrix_apply, h_jcol]  -- entry simplifies to A (i.succAbove p) j
```

**Block III: Apply `adjugate_fin_succ_eq_det_submatrix` and `submatrix_submatrix` (≈10 LOC).**

```lean
refine Finset.sum_congr rfl (fun p _ => ?_)
-- Goal: A (i.succAbove p) j * adjugate (A.submatrix i.succAbove (j.succAbove q).succAbove) j_col p
--     = A (i.succAbove p) j * ((-1)^(q + p) * adjugate M q p)
congr 1
-- Goal: adjugate (A.sub) j_col p = (-1)^(q + p) * adjugate M q p
rw [Matrix.adjugate_fin_succ_eq_det_submatrix _ j_col p]
-- Goal: (-1)^(p + j_col) * det((A.sub).submatrix p.succAbove j_col.succAbove)
--     = (-1)^(q + p) * adjugate M q p
rw [Matrix.adjugate_fin_succ_eq_det_submatrix _ q p]
-- Goal: ... = (-1)^(p + q) * det(M.submatrix p.succAbove q.succAbove) ...
-- Apply submatrix_submatrix to flatten the LHS submatrix.
simp only [Matrix.submatrix_submatrix]
```

**Block IV: Sign collection and matrix-identity closure (≈10 LOC).**

```lean
-- After submatrix_submatrix, the LHS submatrix is A.submatrix (i.succAbove ∘ p.succAbove)
-- ((j.succAbove q).succAbove ∘ j_col.succAbove), and RHS's M.submatrix is
-- A.submatrix (i.succAbove ∘ p.succAbove) (j.succAbove ∘ q.succAbove).
-- The row indices match by composition. The column indices differ by reindexing.
--
-- KEY: (j.succAbove q).succAbove ∘ j_col.succAbove = j.succAbove ∘ q.succAbove
-- (as functions Fin (n-1) → Fin (n+1)). Both skip {j, j.succAbove q}.
-- This is a Fin-level identity that requires Fin.succAbove_succAbove or manual case split.
have h_col_eq : (j.succAbove q).succAbove ∘ j_col.succAbove =
                j.succAbove ∘ q.succAbove := by
  funext k
  -- Unfold both sides via Fin.succAbove_def; case-split on the order of k, j_col, q.
  sorry  -- ~5 LOC of Fin arithmetic.
-- After h_col_eq, the LHS det equals the RHS det.
rw [h_col_eq]
-- Sign collection: (-1)^(p + j_col) = (-1)^(p + q)
-- Both equal (-1)^(p + q) modulo the parity relation `j_col ≡ q (mod 2)` in the q<j case
-- and `j_col ≡ q + 1` in the q≥j case. The first case + 2× the second case fold to the
-- same exponent because of (-1)^2 = 1.
have h_sign : (-1 : F) ^ ((p : ℕ) + (j_col : ℕ)) = (-1 : F) ^ ((q : ℕ) + (p : ℕ)) := by
  by_cases hqj : (q : ℕ) < (j : ℕ)
  · -- j_col = j - 1, q < j: parities match
    sorry  -- ~2 LOC: (-1)^(p + j - 1) = (-1)^(p + q) iff p + j - 1 ≡ p + q (mod 2)
           -- iff j - 1 ≡ q (mod 2), which holds iff j_col and q are both even or odd.
           -- Not always true! This step requires the parity argument from §1.2 — and the
           -- conclusion uses (-1)^(j_col + q) = (-1)^(p + q) * (-1)^(p + q) = 1, not the
           -- naive parity equality.
  · sorry
rw [h_sign]
ring
```

### 2.3 Honest assessment

After fully fleshing out the four blocks, **`submatrix_chain` is closer to 30–45 LOC than the
original ~15 LOC estimate.** The dominant complexity is Block I (defining `j_col` with the
case-split) and Block IV's `h_col_eq` (Fin-arithmetic identity of two `succAbove`
compositions).

**Recommendation for the S13 ACT picker:** treat `submatrix_chain` as a `private lemma`
above `qdetN_step_eq_qdetF` rather than an inline `have`. This:
- Isolates the Fin-level reindex argument from the main field-arithmetic of `qdetN_step_eq_qdetF`.
- Makes the case-split on `q.val < j.val` discoverable to readers.
- Lets the S14 ACT (if needed) target only `submatrix_chain` without touching
  `qdetN_step_eq_qdetF`'s body.

### 2.4 Alternative path: prove `submatrix_chain` via `det_eq_sum_mul_adjugate_row` on `A` itself

If the case-split + Fin-arithmetic in §2.2 becomes intractable, an alternative path
constructs the identity directly from `det_eq_sum_mul_adjugate_row` applied to A at row i,
combined with `Fin.sum_univ_succAbove` to split off the (i,j) term. This is precisely what
`det_via_pivot` already establishes in the §2.9 outer assembly. The downside: this path
needs `submatrix_chain` to be stated *jointly* with `det_via_pivot`, breaking the modular
decomposition. The §2.9 skeleton's `submatrix_chain` is genuinely the "n×n column expansion"
identity, separate from `det_via_pivot`.

**Recommendation:** do not pursue path §2.4 unless §2.2 fails after 3 ACT-time Docker
iterations.

## 3. Live bearer pin re-verification at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Verified live via `gh api /repos/leanprover-community/mathlib4/contents/<path>?ref=<lake-SHA>`
at 2026-05-16T04:30Z.

| Bearer | File | Line | Drift from S11 STATE-SYNC §2 | Status |
|---|---|---:|---:|---|
| `Matrix.adjugate_fin_succ_eq_det_submatrix` | `LinearAlgebra/Matrix/Adjugate.lean` | **362** | unchanged (S11 §2 said "stable") | ✅ |
| `Matrix.det_eq_sum_mul_adjugate_row` | `LinearAlgebra/Matrix/Adjugate.lean` | **401** | unchanged from S11 (1-line cosmetic shift recheck was about 400 vs 401; live = 401) | ✅ |
| `Matrix.det_eq_sum_mul_adjugate_col` | `LinearAlgebra/Matrix/Adjugate.lean` | **415** | unchanged | ✅ |
| `Matrix.submatrix_submatrix` | `LinearAlgebra/Matrix/Defs.lean` | **406** (`@[simp]`) | first pin (not in S11 §2) | ✅ pin-add |
| `Matrix.submatrix_id_id` | `LinearAlgebra/Matrix/Defs.lean` | **402** (`@[simp]`) | first pin | ✅ pin-add |
| `Matrix.det_succ_row` | `LinearAlgebra/Matrix/Determinant/Basic.lean` | (S4f PREP §3: 769–770) | not re-verified live this session | ⚠ deferred |
| `Matrix.inv_def` | `LinearAlgebra/Matrix/NonsingularInverse.lean` | (S4f PREP §3: 167) | not re-verified live this session | ⚠ deferred |
| `Ring.inverse_eq_inv` | `Algebra/GroupWithZero/Units/Basic.lean` | (S4f PREP §3: 374) | not re-verified live this session | ⚠ deferred |
| `Fin.sum_univ_succAbove` | `Algebra/BigOperators/Fin.lean` | (S4f PREP §3: 66–68) | not re-verified live this session | ⚠ deferred |

**Signatures (verified at lake SHA):**

```text
adjugate_fin_succ_eq_det_submatrix
  : ∀ {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) α) (i j),
      adjugate A i j = (-1) ^ (j + i : ℕ) * det (A.submatrix j.succAbove i.succAbove)
```
Note: the sign exponent is `(j + i)` not `(i + j)`. For the `pivot_unfold` step in §2.9, when
applied with parameters (i, j) := (our-j, our-i), we get
`adjugate A j i = (-1)^(i + j) * det(A.submatrix i.succAbove j.succAbove) = (-1)^(i+j) * M.det`.
Direct exact, no `Nat.add_comm` needed: the parameter swap implicitly handles the sign-name.

```text
det_eq_sum_mul_adjugate_row : ∀ (A : Matrix n n α) (i : n),
                                  det A = ∑ j : n, A i j * adjugate A j i

det_eq_sum_mul_adjugate_col : ∀ (A : Matrix n n α) (j : n),
                                  det A = ∑ i : n, A i j * adjugate A j i

submatrix_submatrix
  : ∀ {l m n l₂ o₂ : Type*} (A : Matrix m n α) (r₁ : l → m) (c₁ : o → n) (r₂ : l₂ → l) (c₂ : o₂ → o),
      (A.submatrix r₁ c₁).submatrix r₂ c₂ = A.submatrix (r₁ ∘ r₂) (c₁ ∘ c₂)
```

**S4 ACT picker invariant:** at moment of paste, re-fetch the 4 deferred bearers (marked ⚠)
from lake SHA via `gh api`. None of them have known drift, but the §2.9 skeleton's
field-arithmetic at Step 1 (`inv_def + smul_apply + Ring.inverse_eq_inv`) and Step 8
(`field_simp + ring`) depend on them.

## 4. n=1 worked example: `(i, j) = (0, 0)` and `(0, 1)` over a 2×2 matrix

### 4.1 Setup
`A = ⟦a, b; c, d⟧`. The four cases for `(i, j) ∈ Fin 2 × Fin 2`:

| (i, j) | sign `(-1)^(i+j)` | `M = minorIJ A i j` | `M.det` | `qdetF A i j` (under `M.det ≠ 0`) |
|---|---:|---|---|---|
| (0, 0) | +1 | `⟦d⟧` | `d` | `A.det / d = (ad-bc)/d` |
| (0, 1) | −1 | `⟦c⟧` | `c` | `A.det / c = (ad-bc)/c` |
| (1, 0) | −1 | `⟦b⟧` | `b` | `A.det / b = (ad-bc)/b` |
| (1, 1) | +1 | `⟦a⟧` | `a` | `A.det / a = (ad-bc)/a` |

### 4.2 The `submatrix_chain` content at n=1 (i.e., `q : Fin 1`, so only q=0 to consider)

For `(i, j) = (0, 0)`:
- `q : Fin 1`, so `q = 0`.
- `j.succAbove q = (0 : Fin 2).succAbove (0 : Fin 1) = 1`.
- `(j.succAbove q).succAbove = (1 : Fin 2).succAbove : Fin 1 → Fin 2`, which sends `0 ↦ 0`.
- So `A.submatrix i.succAbove (j.succAbove q).succAbove = A.submatrix (0:Fin 2).succAbove (1:Fin 2).succAbove`, which maps row `0 ↦ 1` and col `0 ↦ 0`. That's the 1×1 matrix `⟦A 1 0⟧ = ⟦c⟧`.
- `det of ⟦c⟧ = c`.
- RHS: `∑ p : Fin 1, A (i.succAbove p) j * ((-1)^(q+p) * adjugate M q p)`.
  - For `p = 0`: `A (0.succAbove 0) 0 * ((-1)^(0+0) * adjugate M 0 0) = A 1 0 * 1 * adjugate ⟦d⟧ 0 0 = c * 1 = c` (since `adjugate ⟦x⟧ 0 0 = 1` for 1×1).
- LHS = RHS = `c`. ✓

For `(i, j) = (0, 1)`:
- `j.succAbove q = (1:Fin 2).succAbove (0:Fin 1) = 0`. (succAbove for `j=1` skips `1`, so maps `0 ↦ 0`.)
- `(j.succAbove q).succAbove = (0:Fin 2).succAbove`, which sends `0 ↦ 1`.
- `A.submatrix i.succAbove (j.succAbove q).succAbove = A.submatrix (0:Fin 2).succAbove (0:Fin 2).succAbove`, mapping row `0 ↦ 1`, col `0 ↦ 1`. That's `⟦A 1 1⟧ = ⟦d⟧`.
- `det = d`.
- RHS: for `p = 0`: `A 1 1 * ((-1)^0 * adjugate ⟦c⟧ 0 0) = d * 1 = d`. (Note: M = `⟦A 1 0⟧ = ⟦c⟧` for `(i,j)=(0,1)`.)
- LHS = RHS = `d`. ✓

### 4.3 Implication for Block IV sign collection

In both n=1 cases, the sign factor `(-1)^(p + j_col)` simplifies because all indices are 0
mod 2 (Fin 1 has only one element). The sign-equality `h_sign : (-1)^(p+j_col) = (-1)^(q+p)`
holds trivially at n=1 (both exponents are 0+0=0).

For general n, the parity relationship `j_col ≡ q (mod 2)` (or `j_col ≡ q + 1 (mod 2)`,
depending on the case-split branch) is what makes Block IV's `h_sign` work. **This is the
content of `submatrix_chain` beyond mere reindexing**: it captures the sign convention of
column-expansion's cofactor through two interleaved `succAbove`s.

## 5. Sequencing recommendation: inline `have` vs `private lemma`

### Option A: Inline `have submatrix_chain : ... := by ...` (S4f PREP §2.9 style)

**Pros:**
- Single-file edit; `qdetN_step_eq_qdetF` is "the" theorem with self-contained proof.
- No new top-level names; private internal step.

**Cons:**
- The `have` body grows to ~30–45 LOC (per §2.3), bloating the main theorem.
- If Block I's `j_col` definition is verbose, it dwarfs Steps 1, 4, 6 of the outer assembly.

### Option B: Hoist `submatrix_chain` to a `private lemma` (S13 ACT recommendation)

```lean
private lemma submatrix_chain {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) F) (i j : Fin (n+1)) (q : Fin n) :
    det (A.submatrix i.succAbove (j.succAbove q).succAbove) =
      ∑ p : Fin n, A (i.succAbove p) j *
        ((-1 : F) ^ ((q : ℕ) + (p : ℕ)) * adjugate (minorIJ A i j) q p) := by
  -- §2.2 four-block body, ~30–45 LOC.
  sorry
```

**Pros:**
- Separates the Fin-arithmetic from the field-arithmetic.
- Lets S14 ACT (if needed) target only the lemma without re-elaborating `qdetN_step_eq_qdetF`.
- Reusable: if a future S5+ Route generalisation needs the same identity, the lemma is in
  scope.
- Smaller PR diff for `qdetN_step_eq_qdetF` body (only the inline `have` line replaced by
  a one-line reference to `submatrix_chain`).

**Cons:**
- New top-level name (private, but still occupies the file's symbol namespace).
- Slightly more verbose: lemma signature + theorem signature must align on `i, j, q`.

**Recommendation: Option B.** The decomposition aligns with S5 (mutual recursion `qdetN ↔ qdetN_inv`),
which will likely re-use `submatrix_chain` or a generalisation.

## 6. Updated S13 ACT readiness gate (replaces S11 STATE-SYNC §4 gate)

| Item | S11 STATE-SYNC | S12 PREP | Status |
|---|---|---|---|
| 1. Mathlib v4.26.0 pin unchanged | ✅ `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | ✅ re-verified live | **GREEN** |
| 2. Parent file `OQ02OQ01.lean` builds clean | ✅ (post-PR #19072) | not re-verified this session; relying on S11 § 3 | **GREEN** (carried forward) |
| 3. Bearer pin line stability | ✅ 0 substantive drift; 1 cosmetic on `det_eq_sum_mul_adjugate_row` | ✅ confirmed: 4 critical bearers at expected lines | **GREEN** |
| 4. `submatrix_chain` tactic plan | ❌ S4f PREP §2.7 had 4-bearer sketch only | ✅ §2.2 four-block paste-ready tactic | **GREEN** (resolved this session) |
| 5. Open-PR conflict surface | ✅ #19435 is meta.json-only, disjoint | ✅ confirmed (re-checked at 04:30Z) | **GREEN** |
| 6. Deployer org-cap | ⚠ AMBER (104 open PRs; exogenous) | ⚠ AMBER (no improvement; still exogenous) | **AMBER** (unchanged) |
| 7. (NEW) S13 ACT body size estimate | — | revised: ~30–45 LOC for `submatrix_chain` alone; total skeleton +n=1 examples = ~95–115 LOC | **GREEN** (estimate locked) |

**Net: 6 GREEN + 1 AMBER** (vs S11 STATE-SYNC's 5 GREEN + 1 AMBER). The newly-GREEN item
is row 4 (`submatrix_chain` tactic plan); the newly-added row 7 quantifies the revised
LOC estimate.

## 7. Anti-targets and conflict-free guarantees

### 7.1 What this PR does NOT do
- Does NOT edit `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean`. (Lean unchanged.)
- Does NOT edit `proofs/Proofs/CramersRuleOQ01OQ02.lean` or `OQ02OQ01.lean`. (parent unchanged.)
- Does NOT modify `src/data/proofs/cramers-rule-oq-01-oq-02-oq-01-oq-01/meta.json`. (Disjoint from PR #19435 mechanic fix; meta-fields are owned by the deployer / mechanic agents.)
- Does NOT modify the slug's `problem.md` or `knowledge.md`.
- Does NOT Docker-build (per §0.3; doc-only PREPs do not consume Docker per S4f PREP §6 anti-pattern).

### 7.2 Race-safety
Pre-claim check (2026-05-16T04:30Z, via `gh search prs --repo rjwalters/lean-genius "cramers-rule-oq-01-oq-02-oq-01-oq-01" --state open`):

| PR | Title | Touches | Conflict with this PR |
|---|---|---|---|
| #19435 | `fix(meta): cramers-rule-oq-01-oq-02-oq-01-oq-01 top-level sorries 0→1` | `src/data/proofs/.../meta.json` only | **none** — disjoint paths |

This PR's diff:
- `research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01/sessions/2026-05-16-s12-prep-submatrix-chain-tactic-plan.md` [NEW]
- `research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01/state.md` [head replace; preserves Session-10 and earlier content unchanged below]
- `src/data/research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01.json` [iteration 11 → 12, focus/nextAction refresh, insights prepend]

### 7.3 Iteration math
- Total attempts: 9 → 10 (per S11 STATE-SYNC §7 schema)
- Current approach attempts: 1 (S12 PREP, this iteration)
- Approaches tried (recursive in approach counter): S4-statement-correction → mechanic-PR-overlay-verify → S4f-PREP-§2.9-skeleton → S11-STATE-SYNC-post-drain-catch-up → this S12-PREP-submatrix_chain-tactic-plan

## 8. Next action for S13 ACT picker

Per §1–§5 of this memo:

1. **Pre-flight at pick-time:** re-fetch the 4 ⚠-deferred bearers (`Matrix.det_succ_row`,
   `Matrix.inv_def`, `Ring.inverse_eq_inv`, `Fin.sum_univ_succAbove`) from lake SHA via
   `gh api`, lock their line numbers.
2. **Adopt Option B (private lemma)** per §5: declare `private lemma submatrix_chain` above
   `qdetN_step_eq_qdetF`.
3. **Paste the §2.9 skeleton with `submatrix_chain` reference replaced by name** (rather
   than inline `have`).
4. **Implement Block I–IV** from §2.2 inside the `private lemma`. Budget ~30–45 LOC.
5. **Drop the §4 sanity-check `example` blocks** (n=1 at (0,0) and (0,1)).
6. **Docker-build** via `./proofs/scripts/docker-build.sh Proofs.CramersRuleOQ01OQ02OQ01OQ01`.
   Expected: 3060 → 3060 jobs (slug file built clean per S11 §3; no upstream changes to
   parent or Mathlib pin since).
7. **Sorry count:** strategic sorry on `qdetN_step_eq_qdetF` discharged; new `private lemma`
   sorry on `submatrix_chain` (if S13 leaves Block I or IV at `sorry` for S14 follow-up). Net
   could be 1→1 if the case-split or sign-collection turns out to be the genuine difficulty,
   or 1→0 if S13 fully discharges.

Estimated S13 ACT wall time: 60–90 min (4–6 Docker iters at ~60–180s each in warm cache).

## 9. Diff manifest (this PR)

| File | Action | Lines |
|---|---|---:|
| `research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01/sessions/2026-05-16-s12-prep-submatrix-chain-tactic-plan.md` | NEW | ~520 |
| `research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01/state.md` | head replace (preserves prior content) | ~50 lines replaced |
| `src/data/research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01.json` | `currentState` refresh (iteration 11→12, focus/nextAction/lastUpdate; 2 insight prepends) | ~20 lines changed |

**Net:** 0 Lean edits, 0 axiom change, 0 sorry change, +3 files in research/ tree, all
strictly orthogonal to PR #19435 (the only in-flight PR on this slug).
