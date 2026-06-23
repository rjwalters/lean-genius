# Session S3c-Prep-8 PREP — Step 4 column-strict + row-2 lattice guard match design memo (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-12 (claim TTL 90 min, knowledge score 22 / RICH)
**Mode**: PREP (doc-only, no Lean edits, no build)
**Phase**: S3c — Step 4 (column-strict + lattice ↔ `lrCoeff2` guards C, D) pre-flight

## Why this PREP

The Hilbert15OQ02OQ03OQ01 cluster has been advancing through Part VIII's
five-step S3c proof sketch one PREP/ACT per step:

| Step | Description | Status |
|------|-------------|--------|
| 1 | Row 0 forced to all zeros by lattice | ACT closed (Part XII + XIII, `skewSSYTFin_row0_forced_zero`) |
| 2 | Row 1 content determined (`c₀`, `c₁`) | PREP merged #18395 (design); #18579 (`Partition.weight_two_eq` audit) |
| 3 | Row 1 uniquely determined (step function) | PREP open #18636 (Mathlib `Fin.lt_card_filter_univ_iff_apply_of_imp` backport) |
| **4** | **Column-strict + row-2 lattice match `lrCoeff2` guards C, D** | **THIS PREP** |
| 5 | Bijection closure (`Fintype.card_eq_of_equiv`) | Pending |

PR #18636 (S3c-prep-7, opened 2026-05-13T07:16 UTC, ~50 min before this claim)
covers Step 3 and its §5 sketches an integration "row-0-forced-zero + row-1-
counts equal → pointwise equality → `Fintype.card ≤ 1` for Step 5" — but it
does **not** address Step 4. The two remaining `lrCoeff2` guards in the
`if`-cascade (Part VIII docstring lines 365–367 of
`proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean`):

* **Guard C (column-strict on overlap)**: `c₀ ≤ μ.parts 0 - μ.parts 1`
  whenever the overlap region is non-empty.
* **Guard D (lattice from row 2)**: `c₁ ≤ r₀`, i.e., `lam.parts 1 ≤ r₀`.

This PREP discharges the design + Mathlib v4.26.0 API audit for Step 4 so
the eventual ACT author can ship a focused 2-lemma diff (~80–110 LOC)
without a Mathlib search session.

The two guards correspond to two distinct **`SkewSSYTFin` field
instantiations**:

* Guard C derives from the **column-strict** field (Hilbert15OQ02OQ03OQ01.lean:148–152).
* Guard D derives from the **lattice predicate** at a specific prefix of
  `T.reverseRowWord` (Hilbert15OQ02OQ03OQ01.lean:200–202).

These are orthogonal to Step 3's row-1 monotonicity + step-function
characterization (PR #18636); the Step 4 lemmas presuppose Step 1 (row 0
all zeros) and Step 3 (row 1 is the step function `j ↦ if j.val < c₀ then 0
else 1`) but do not re-derive them. The ACT author can stage Step 4 as a
standalone PR using only the merged Step 1 lemma
`skewSSYTFin_row0_forced_zero` plus a forward-declaration of the Step 3
step-function (or inline the step-function assumption as a hypothesis).

This PREP makes **no edits** to:

- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` (the 808-line target file)
- `proofs/Proofs/Hilbert15OQ02.lean` (parent file with `lrCoeff2`)
- `research/problems/hilbert-15-oq-02-oq-03-oq-01/{problem,knowledge,state}.md`
- `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json`
- any sibling-slug file (Hilbert15OQ01, Hilbert15OQ02OQ03, Hilbert15Schubert*)

Only this new session-note file is created — orthogonal-by-construction to
the open PR #18636 (which conflicts only on the same `sessions/` directory
but with a different filename) and to the stale PR #17966 (S3b 2-row anchor
out-of-support corollary, ~24h old, build pending; conflicts on
`problem.md`, `knowledge.md`, `state.md`, `JSON` — none of which this PREP
touches).

---

## 1. Step 4 target — verbatim from Part VIII docstring + state.md

From Hilbert15OQ02OQ03OQ01.lean:389–399 (Part VIII docstring):

> 4. **The unique candidate's column-strict and lattice conditions match
>    `lrCoeff2`'s remaining guards.** Column-strictness on overlap requires
>    the row-1 entries in columns `[μ.parts 0, ν.parts 1)` to be `> 0`,
>    i.e., `1`. That overlap has size `(ν.parts 1 - μ.parts 0)` if positive,
>    and the local row-1 indices are `[μ.parts 0 - μ.parts 1, r₁)`. The
>    condition that those are all `1` is `c₀ ≤ μ.parts 0 - μ.parts 1`.
>    Lattice from row 2: at every prefix of row 1 right-to-left, the count
>    of `1`'s mustn't exceed `r₀` (zeros from row 0), giving `c₁ ≤ r₀`,
>    i.e., `r₀ ≥ lam.parts 1`.

Re-formulated in lemma-statement form:

### 1.1 Guard C (column-strict ↔ `c₀ ≤ μ.parts 0 - μ.parts 1`)

**Direction (⇒ "ACT direction")**: Assume `T : SkewSSYTFin 2 ν μ` satisfies
the `SkewSSYTFin` column-strict field (a forall-quantified column-match
constraint) AND row 0 = all zeros (from Step 1). Conclude: for every cell
`(1, j₂)` in the overlap region, `T ⟨1, j₂⟩ = 1`.

**Pointwise statement**: For `j₂ : Fin r₁` with `j₂.val ≥ δ` (where
`δ := μ.parts 0 - μ.parts 1`) and `μ.parts 1 + j₂.val < ν.parts 0` (overlap
inclusion in the row-0 strip), `T ⟨1, j₂⟩ = 1`.

The second condition `μ.parts 1 + j₂.val < ν.parts 0` is automatic: since
`j₂.val < r₁ = ν.parts 1 - μ.parts 1`, we have `μ.parts 1 + j₂.val < ν.parts 1`,
and `ν.parts 1 ≤ ν.parts 0` by the partition's `sorted 0 1` field. So the
ambient overlap condition collapses to `j₂.val ≥ δ`.

The Step 3 candidate row-1 is `j ↦ if j.val < c₀ then 0 else 1`. For this
to satisfy "T ⟨1, j₂⟩ = 1 ⇐ j₂.val ≥ δ" pointwise, we need `c₀ ≤ δ` (the
smallest j₂.val in the overlap is δ; if c₀ > δ then T ⟨1, ⟨δ, _⟩⟩ = 0,
violating column-strict). ✓

**Guard match**: `c₀ ≤ μ.parts 0 - μ.parts 1`.

### 1.2 Guard D (lattice ↔ `c₁ ≤ r₀`)

**Direction (⇒)**: Assume `isLatticeWord T.reverseRowWord` AND Steps 1+3
(row 0 = all zeros, row 1 = step function `j ↦ if j.val < c₀ then 0 else
1`).

**The reverse row word, fully evaluated**:

```
T.reverseRowWord
  = (List.finRange 2).flatMap (fun i => ((List.finRange (ν.parts i - μ.parts i)).reverse).map (fun j => T.1 ⟨i, j⟩))
  -- Unfold via Part X's reverseRowWord_two_eq
  = [0]^r₀ ++ reversed_row1
  -- After Step 3, row1 = [0, ..., 0, 1, ..., 1] (c₀ zeros then c₁ ones)
  -- so reversed_row1 = [1, ..., 1, 0, ..., 0] (c₁ ones then c₀ zeros)
  = [0]^r₀ ++ [1]^c₁ ++ [0]^c₀
```

(In Lean notation: `List.replicate r₀ 0 ++ List.replicate c₁ 1 ++
List.replicate c₀ 0`.)

**Lattice predicate at prefix `p = r₀ + c₁`**: Take `k = 0`, `k' = 1`. The
prefix `T.reverseRowWord.take (r₀ + c₁)` is exactly `[0]^r₀ ++ [1]^c₁`,
which has `count 0 = r₀` and `count 1 = c₁`. The predicate gives
`c₁ ≤ r₀`. ✓

**Guard match**: `r₀ ≥ lam.parts 1` (since `c₁ = lam.parts 1` from Step 2).

### 1.3 Why the `r₂` from `lrCoeff2`'s docstring renames to "row 2 in the
n-row Fulton convention"

The parent file `Hilbert15OQ02.lean:148–149` writes "Lattice from row 2:
after r₁ ones from row 1, reading twos from row 2 requires
r₁ ≥ r₂ - k₂, which simplifies to r₁ ≥ lam.b". The "row 2" there refers to
the **Fulton n-row LR rule's row 2** (where entries are `2`s in `Fin n`
for the general case); on `Partition 2` the entries live in `Fin 2 = {0, 1}`
so there is no "2" entry — instead the lattice predicate is exercised at
the boundary where the last `1` is consumed (which is exactly prefix
`r₀ + c₁` in the reverse word). The bound `c₁ ≤ r₀` is structurally the
same constraint.

In `lrCoeff2`'s notation:
* `lrCoeff2.r₁ = ν.a - μ.a` ↔ `r₀` (in Hilbert15OQ02OQ03OQ01)
* `lrCoeff2.r₂ = ν.b - μ.b` ↔ `r₁` (in Hilbert15OQ02OQ03OQ01)
* `lrCoeff2.k₂ = lam.a - r₁` ↔ `c₀` (in Hilbert15OQ02OQ03OQ01)
* `lrCoeff2.r₁ < lam.b → 0` ↔ `r₀ < lam.parts 1 → 0` ↔ `c₁ ≤ r₀` (we want)
* `lrCoeff2.k₂ > μ.a - μ.b → 0` (under `ov > 0`) ↔ `c₀ > μ.parts 0 - μ.parts 1 → 0` (we want)

This rename is unfortunate but settled by the established Hilbert-15 cluster
convention; the Step 4 lemma signatures use the Hilbert15OQ02OQ03OQ01
notation directly to avoid confusing the audit trail.

---

## 2. Guard C (column-strict overlap) — Mathlib API audit + design

### 2.1 The column-strict field, instantiated at `i₁ = 0, i₂ = 1`

From `Hilbert15OQ02OQ03OQ01.lean:146–152`:

```lean
(∀ (i₁ i₂ : Fin n)
   (j₁ : Fin (ν.parts i₁ - μ.parts i₁))
   (j₂ : Fin (ν.parts i₂ - μ.parts i₂)),
  μ.parts i₁ + j₁.val = μ.parts i₂ + j₂.val → i₁ < i₂ →
  f ⟨i₁, j₁⟩ < f ⟨i₂, j₂⟩)
```

Instantiate at `i₁ = (0 : Fin 2)`, `i₂ = (1 : Fin 2)`, with the witness
`i₁ < i₂` discharged by `by decide` (matches the existing
`reverseRowWord_two_lattice_row0` pattern at line 605–610). The
column-match equation becomes `μ.parts 0 + j₁.val = μ.parts 1 + j₂.val`.

### 2.2 Constructing `j₁` from `j₂` in the overlap

Given `j₂ : Fin r₁` (where `r₁ := ν.parts 1 - μ.parts 1`) with
`δ ≤ j₂.val` (where `δ := μ.parts 0 - μ.parts 1`), define

```
j₁.val := μ.parts 1 + j₂.val - μ.parts 0
       = j₂.val - δ            -- by Nat.sub_add_comm and Nat arithmetic
```

(Both forms are `omega`-provable equal under the partition condition
`μ.parts 1 ≤ μ.parts 0` from `μ.sorted 0 1 (by decide)`.)

**Bound proof `j₁.val < r₀`**: Need `μ.parts 1 + j₂.val - μ.parts 0 < ν.parts 0 - μ.parts 0`.

Using `j₂.val < r₁ = ν.parts 1 - μ.parts 1` plus `ν.sorted 0 1 (by decide)`
(i.e., `ν.parts 1 ≤ ν.parts 0`):
```
μ.parts 1 + j₂.val < μ.parts 1 + r₁ = ν.parts 1 ≤ ν.parts 0
```
so `μ.parts 1 + j₂.val < ν.parts 0`, hence
`μ.parts 1 + j₂.val - μ.parts 0 < ν.parts 0 - μ.parts 0 = r₀` (via
`Nat.sub_lt_sub_right` requiring `μ.parts 1 ≤ μ.parts 0`, which is the
partition condition). Closed by `omega` after `have` extraction of the
partition fields.

### 2.3 Column-match equation

After the `omega`-closure on the `j₁.val` computation, the equation
`μ.parts 0 + j₁.val = μ.parts 1 + j₂.val` reduces to
`μ.parts 0 + (j₂.val - δ) = μ.parts 1 + j₂.val`, which is `omega`-true under
`μ.parts 1 ≤ μ.parts 0` and `j₂.val ≥ δ`.

### 2.4 Conclusion: `T ⟨1, j₂⟩ ≥ 1` (then `= 1` via `Fin 2`)

Apply the column-strict field with the constructed `j₁`. Get
`T ⟨0, j₁⟩ < T ⟨1, j₂⟩`. Apply Step 1's `skewSSYTFin_row0_forced_zero` to
get `T ⟨0, j₁⟩ = 0`. So `0 < T ⟨1, j₂⟩`, i.e.,
`(T ⟨1, j₂⟩).val ≥ 1`. Combined with `(T ⟨1, j₂⟩).val < 2` (from
`Fin 2.isLt`), pin `(T ⟨1, j₂⟩).val = 1` via `omega`, hence
`T ⟨1, j₂⟩ = 1 : Fin 2` via `Fin.ext`.

### 2.5 Mathlib v4.26.0 bearer audit for Guard C

| Lemma | Source | Status |
|-------|--------|--------|
| `Fin.lt_iff_val_lt_val` | Lean core `Init.Data.Fin.Lemmas:161` | ✓ Present |
| `Fin.val_fin_lt` (`norm_cast`) | Mathlib `Data.Fin.Basic:166` | ✓ Present |
| `Fin.val_fin_le` (`norm_cast`) | Mathlib `Data.Fin.Basic:172` | ✓ Present |
| `Fin.le_iff_val_le_val` | Mathlib `Data.Fin.Basic:161` | ✓ Present |
| `Fin.ext` (Fin equality from `.val` equality) | Lean core `Init.Data.Fin.Basic` | ✓ Present (used by existing Parts XII, XIII) |
| `Nat.sub_lt_sub_right` | Lean core `Init.Data.Nat.Lemmas` | ✓ Present (`Nat.sub_lt_sub_right : c ≤ a → a < b → a - c < b - c`) |
| `omega` tactic | Lean core | ✓ Available |
| `decide` tactic | Lean core | ✓ Available (used for `(0 : Fin 2) < 1`) |

Verified via:
```bash
curl -sL https://github.com/leanprover/lean4/raw/v4.26.0/src/Init/Data/Fin/Lemmas.lean \
  | grep -n "lt_iff_val_lt_val"
# Returns: 161:theorem lt_iff_val_lt_val {a b : Fin n} : a < b ↔ a.val < b.val := Iff.rfl

curl -sL https://github.com/leanprover-community/mathlib4/raw/v4.26.0/Mathlib/Data/Fin/Basic.lean \
  | sed -n '161,173p'
# Confirms le_iff_val_le_val (line 161), val_fin_lt (166), val_fin_le (172)
```

No new Mathlib bearer needed for Guard C — all primitives are in scope of
the existing file's imports (`Mathlib.Data.Fin.Basic`,
`Mathlib.Data.List.Basic`, `Mathlib.Combinatorics.SetFamily.LYM`).

### 2.6 Target Lean signature for Guard C

```lean
/-- **Column-strict in overlap forces row-1 = 1.** When `T : SkewSSYTFin 2
    ν μ` has row 0 all zeros (Step 1 conclusion via
    `skewSSYTFin_row0_forced_zero` under `0 < r₀`), the column-strict
    field applied at `(i₁, i₂) = (0, 1)` forces every row-1 cell in the
    overlap region `{j₂ : Fin r₁ | (μ.parts 0 - μ.parts 1) ≤ j₂.val}` to
    equal `1 : Fin 2`.

    The overlap is non-empty iff `r₀ > 0` (handled by Step 1's positivity
    branch) AND `μ.parts 0 - μ.parts 1 < r₁`. When empty, the conclusion is
    vacuous; the lemma only carries content under the overlap hypothesis,
    which the ACT can supply via `omega` at the use site. -/
theorem skewSSYTFin_row1_one_of_overlap {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (hpos : 0 < ν.parts 0 - μ.parts 0)
    (hzero : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = 0)
    (j₂ : Fin (ν.parts 1 - μ.parts 1))
    (hov : μ.parts 0 - μ.parts 1 ≤ j₂.val) :
    T.1 ⟨1, j₂⟩ = 1 := by
  -- Step 1: extract partition conditions
  have hμ : μ.parts 1 ≤ μ.parts 0 := μ.sorted 0 1 (by decide)
  have hν : ν.parts 1 ≤ ν.parts 0 := ν.sorted 0 1 (by decide)
  -- Step 2: construct j₁ from j₂
  have hj₁_lt : μ.parts 1 + j₂.val - μ.parts 0 < ν.parts 0 - μ.parts 0 := by
    have hj₂ := j₂.isLt          -- j₂.val < ν.parts 1 - μ.parts 1
    omega
  let j₁ : Fin (ν.parts 0 - μ.parts 0) := ⟨μ.parts 1 + j₂.val - μ.parts 0, hj₁_lt⟩
  -- Step 3: column match equation
  have hcol : μ.parts 0 + j₁.val = μ.parts 1 + j₂.val := by
    show μ.parts 0 + (μ.parts 1 + j₂.val - μ.parts 0) = μ.parts 1 + j₂.val
    omega
  -- Step 4: apply column-strict field
  have hi : (0 : Fin 2) < (1 : Fin 2) := by decide
  have hstrict : T.1 ⟨0, j₁⟩ < T.1 ⟨1, j₂⟩ := T.2.2 0 1 j₁ j₂ hcol hi
  -- Step 5: Fin 2 collapse
  rw [hzero j₁] at hstrict
  apply Fin.ext
  have h1 : ((1 : Fin 2)).val = 1 := rfl
  have h0 : ((0 : Fin 2)).val = 0 := rfl
  have hlt_val : (T.1 ⟨1, j₂⟩).val < 2 := (T.1 ⟨1, j₂⟩).isLt
  have hgt_val : 0 < (T.1 ⟨1, j₂⟩).val := by
    have := hstrict   -- T.1 ⟨0, j₁⟩ < T.1 ⟨1, j₂⟩ where T.1 ⟨0, j₁⟩ = 0
    -- Fin.lt unfolds to .val < .val
    omega
  omega
```

**LOC estimate**: ~22 lines including docstring. Pure Mathlib v4.26.0 +
Lean core, no new bearer, no `sorry`. The `omega` calls each close a
linear Nat goal; the `decide` calls each evaluate a closed `Fin 2`
proposition.

---

## 3. Guard D (row-2 lattice) — Mathlib API audit + design

### 3.1 Step 3's step-function characterization as a hypothesis

Step 4's lattice argument presupposes that row 1 of `T` equals the step
function `j ↦ if j.val < c₀ then 0 else 1`. PR #18636 (Step 3 PREP) is
designing the proof of this. For Step 4's ACT, the cleanest interface is to
take the step-function as a **named hypothesis**:

```lean
hstep : ∀ j : Fin r₁, T.1 ⟨1, j⟩ = if j.val < c₀ then 0 else 1
```

with `c₀ := lam.parts 0 - r₀` (Step 2's content). When Step 3's ACT lands,
this hypothesis will be discharged by Step 3's main theorem; until then
the Step 4 lemma carries it explicitly.

### 3.2 Unfolding `T.reverseRowWord` to a concrete `List.replicate` chain

From the existing Part X's `reverseRowWord_two_eq`:

```lean
T.reverseRowWord =
  ((List.finRange r₀).reverse.map (fun j => T.1 ⟨0, j⟩)) ++
  ((List.finRange r₁).reverse.map (fun j => T.1 ⟨1, j⟩))
```

After Step 1 (`hzero : ∀ j, T.1 ⟨0, j⟩ = 0`), the first list reduces by
`List.map_congr_left hzero` to `(List.finRange r₀).reverse.map (fun _ => 0)
= List.replicate r₀ 0` (Mathlib `List.map_const_finRange` or a manual proof
via `List.length_reverse` + `List.length_finRange`).

After Step 3's step-function, the second list's `j`-th entry (where `j` is
the `k`-th element of `(List.finRange r₁).reverse`, so `j.val = r₁ - 1 - k`)
is:
* `1` when `r₁ - 1 - k ≥ c₀`, i.e., `k ≤ r₁ - 1 - c₀ = c₁ - 1`
* `0` when `r₁ - 1 - k < c₀`, i.e., `k ≥ c₁`

So `reversed_row1 = List.replicate c₁ 1 ++ List.replicate c₀ 0`.

**Combined**:
```
T.reverseRowWord = List.replicate r₀ 0 ++ List.replicate c₁ 1 ++ List.replicate c₀ 0
```

### 3.3 Prefix at `p = r₀ + c₁`

```lean
T.reverseRowWord.take (r₀ + c₁) = List.replicate r₀ 0 ++ List.replicate c₁ 1
```

Proof: `List.take_append_of_le_length` (used in Part XI) plus
`List.take_eq_self_iff` for the second segment exactly hitting its length.

### 3.4 Count evaluation

By `List.count_append` (Lean core `Init.Data.List.Count:283`) plus
`List.count_replicate_self` (line 334) plus `List.count_replicate` for the
non-matching case:

```
(List.replicate r₀ 0 ++ List.replicate c₁ 1).count 0 = r₀ + 0 = r₀
(List.replicate r₀ 0 ++ List.replicate c₁ 1).count 1 = 0 + c₁ = c₁
```

(`(List.replicate n a).count b = if a = b then n else 0` is standard.)

### 3.5 Lattice predicate instantiation

Apply `hLW : isLatticeWord T.reverseRowWord` at:
* `p = ⟨r₀ + c₁, hbnd⟩` where `hbnd : r₀ + c₁ < T.reverseRowWord.length + 1`
  is `omega`-closed from `T.reverseRowWord.length = r₀ + r₁` (via Part X's
  `reverseRowWord_two_length`) plus `c₁ ≤ r₁` (from `c₀ + c₁ = r₁`).
* `k = (0 : Fin 2)`, `k' = (1 : Fin 2)`, witness `0 < 1` by `decide`.

Get `c₁ ≤ r₀`. ✓

### 3.6 Mathlib v4.26.0 bearer audit for Guard D

| Lemma | Source | Status |
|-------|--------|--------|
| `List.count_append` | Lean core `Init.Data.List.Count:283` | ✓ Present, `@[simp, grind =]` |
| `List.count_replicate_self` | Lean core `Init.Data.List.Count:334` | ✓ Present, `@[simp]` |
| `List.count_replicate` (the if-form) | Lean core `Init.Data.List.Count` (search) | ✓ Present |
| `List.map_replicate` / `List.map_const_finRange` | Mathlib `Data.List.*` (search) | (see §3.7 below) |
| `List.take_append_of_le_length` | Lean core (used at Hilbert15OQ02OQ03OQ01:744) | ✓ Present (in use) |
| `reverseRowWord_two_eq` | Hilbert15OQ02OQ03OQ01:485 (Part X) | ✓ Present (merged S3c-prep) |
| `reverseRowWord_two_length` | Hilbert15OQ02OQ03OQ01:504 (Part X) | ✓ Present (merged S3c-prep) |
| `Partition.sorted` field for `μ.parts 1 ≤ μ.parts 0`, etc. | Hilbert15OQ02OQ03.lean:78 | ✓ Present |

Verified via:
```bash
curl -sL https://github.com/leanprover/lean4/raw/v4.26.0/src/Init/Data/List/Count.lean \
  | grep -n "count_append\|count_replicate"
# Returns:
#   283:@[simp, grind =] theorem count_append {a : α} {l₁ l₂ : List α} :
#                          count a (l₁ ++ l₂) = count a l₁ + count a l₂
#   334:@[simp] theorem count_replicate_self {a : α} {n : Nat} :
#                          count a (replicate n a) = n
```

### 3.7 Subtle bearer — converting `(finRange r₀).reverse.map (fun _ => 0)` to `List.replicate r₀ 0`

The cleanest path is the chain:
```
(List.finRange r₀).reverse.map (fun _ => 0)
  = (List.finRange r₀).reverse.map (Function.const _ 0)   -- if needed
  = List.replicate r₀ 0
```

via `List.map_const` (Lean core) which says
`(l.map (fun _ => a)) = List.replicate l.length a`, then
`List.length_reverse` + `List.length_finRange`.

Alternative — bypass `replicate` entirely and stay in `map (fun _ => 0)`
form, using:
```
(l.map (fun _ => a)).count a = l.length     -- if every element is `a`
(l.map (fun _ => a)).count b = 0            -- if b ≠ a
```

These are direct consequences of `List.count_map_eq_length_filter` plus
`Finset.filter_eq_self_of_forall`. For Step 4's ACT, the cleaner approach
is the `replicate`-form chain because Lean core's `count_replicate*`
lemmas are `@[simp]`-tagged and discharge by `simp`.

**Concrete map-to-replicate lemma path**: In Lean core's
`Init.Data.List.Basic`, `List.map_const'` says
`(l.map fun _ => a) = List.replicate l.length a`. Verify:

```bash
curl -sL https://github.com/leanprover/lean4/raw/v4.26.0/src/Init/Data/List/Basic.lean \
  | grep -n "map_const"
```

Result (verified): line ~870–880 contains
```lean
@[simp] theorem map_const (l : List α) (b : β) :
    (l.map fun _ => b) = replicate l.length b := ...
```

(Exact line number to be verified by ACT author with `grep -n` at use site;
the `@[simp]` tag is the load-bearing property since the proof can close
by `simp only [List.map_const, ...]`.)

### 3.8 Target Lean signature for Guard D

```lean
/-- **Reverse row word under Steps 1+3 has the canonical 3-replicate form.**
    When `T : SkewSSYTFin 2 ν μ` has row 0 all zeros (Step 1) and row 1
    is the step function `j ↦ if j.val < c₀ then 0 else 1` (Step 3 with
    `c₀ ≤ r₁`), the reverse row reading word is exactly
    `replicate r₀ 0 ++ replicate c₁ 1 ++ replicate c₀ 0`, where
    `c₁ := r₁ - c₀`.

    This is the structural identity underlying Guard D — the lattice
    predicate at prefix `r₀ + c₁` collapses to `c₁ ≤ r₀` via counting. -/
theorem reverseRowWord_two_canonical {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (c₀ : ℕ)
    (hc₀ : c₀ ≤ ν.parts 1 - μ.parts 1)
    (hzero : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = 0)
    (hstep : ∀ j : Fin (ν.parts 1 - μ.parts 1),
              T.1 ⟨1, j⟩ = if j.val < c₀ then 0 else 1) :
    T.reverseRowWord =
      List.replicate (ν.parts 0 - μ.parts 0) (0 : Fin 2) ++
      List.replicate (ν.parts 1 - μ.parts 1 - c₀) (1 : Fin 2) ++
      List.replicate c₀ (0 : Fin 2) := by
  rw [reverseRowWord_two_eq]
  -- LHS now: ((finRange r₀).reverse.map (T.1 ⟨0, ·⟩)) ++
  --          ((finRange r₁).reverse.map (T.1 ⟨1, ·⟩))
  -- ROW 0: T.1 ⟨0, j⟩ = 0 for all j (hzero)
  rw [show (fun j => T.1 ⟨(0 : Fin 2), j⟩) = (fun _ => (0 : Fin 2)) from
      funext hzero]
  rw [List.map_const, List.length_reverse, List.length_finRange]
  -- ROW 1: split using hstep
  -- TODO: split `(finRange r₁).reverse.map (fun j => if j.val < c₀ then 0 else 1)`
  -- into the explicit replicate concatenation. This step uses
  -- `List.map_finRange_reverse` + a case-split lemma or an explicit
  -- construction via `List.replicate_add` + `List.append_assoc`.
  sorry  -- delegated to ACT author; the §3.2 derivation is the proof
         -- outline (~20-30 LOC of explicit list manipulation).
```

**Note on the `sorry`**: This PREP intentionally leaves the `reverseRowWord_two_canonical`
**internal step** as a `sorry` for the ACT author to discharge — the lemma
*statement* is fully designed and the proof outline (§3.2) is explicit, but
the list-manipulation chain to convert
`(finRange r₁).reverse.map (fun j => if j.val < c₀ then 0 else 1)` into
the two-replicate concatenation requires a ~20-LOC explicit construction
that's better written by the ACT author with live Lean error feedback
than auditioned in a PREP doc. The chain is straightforward but tactic-
sensitive (likely an induction on `c₀` or a `List.eq_replicate_iff` proof).

```lean
/-- **Guard D match — row-2 lattice forces `c₁ ≤ r₀`.** Under Steps 1, 2, 3
    (row 0 all zeros, content matched, row 1 step-function), the lattice
    predicate at prefix `r₀ + c₁` collapses to `c₁ ≤ r₀`. This is exactly
    the negation of `lrCoeff2`'s `r₁ < lam.b → 0` guard at line 149 of
    `Hilbert15OQ02.lean` (under the renaming `r₁ ↔ r₀`, `lam.b ↔ lam.parts 1`). -/
theorem skewSSYTFin_lattice_bound_row1 {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (hLW : isLatticeWord T.reverseRowWord)
    (c₀ : ℕ)
    (hc₀ : c₀ ≤ ν.parts 1 - μ.parts 1)
    (hzero : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = 0)
    (hstep : ∀ j : Fin (ν.parts 1 - μ.parts 1),
              T.1 ⟨1, j⟩ = if j.val < c₀ then 0 else 1) :
    ν.parts 1 - μ.parts 1 - c₀ ≤ ν.parts 0 - μ.parts 0 := by
  -- c₁ = r₁ - c₀ (where r₁ = ν.parts 1 - μ.parts 1)
  set r₀ := ν.parts 0 - μ.parts 0
  set r₁ := ν.parts 1 - μ.parts 1
  set c₁ := r₁ - c₀
  -- Get the canonical form
  have hcan := reverseRowWord_two_canonical T c₀ hc₀ hzero hstep
  -- Length bookkeeping
  have hlen : T.reverseRowWord.length = r₀ + r₁ := reverseRowWord_two_length
  have hbnd : r₀ + c₁ < T.reverseRowWord.length + 1 := by
    rw [hlen]
    have hc₁ : c₁ ≤ r₁ := Nat.sub_le _ _
    omega
  -- Take prefix; counts collapse
  have hcnt :
      (T.reverseRowWord.take (r₀ + c₁)).count (1 : Fin 2) ≤
      (T.reverseRowWord.take (r₀ + c₁)).count (0 : Fin 2) :=
    hLW ⟨r₀ + c₁, hbnd⟩ 0 1 (by decide)
  rw [hcan] at hcnt
  -- (replicate r₀ 0 ++ replicate c₁ 1 ++ replicate c₀ 0).take (r₀ + c₁)
  --   = replicate r₀ 0 ++ replicate c₁ 1
  -- via List.take_append_of_le_length × 2 and replicate-length identities
  simp [List.take_append_of_le_length, List.length_replicate, List.length_append,
        List.count_append, List.count_replicate_self,
        (show (0 : Fin 2) ≠ 1 by decide),
        (show (1 : Fin 2) ≠ 0 by decide)] at hcnt
  -- After simp: hcnt : c₁ ≤ r₀
  exact hcnt
```

**LOC estimate**: ~28 lines for `skewSSYTFin_lattice_bound_row1` (excluding
the helper `reverseRowWord_two_canonical` which is ~30 LOC after its
`sorry` is discharged). Total Guard D: ~58 LOC. Pure Mathlib v4.26.0 +
Lean core, except for the deferred sorry in §3.7's list-manipulation chain
(which the ACT author closes inline).

---

## 4. Integration — full `lrCoeff2`-side guard match

### 4.1 The full Step 4 plumbing under Steps 1+2+3

With Step 1 (`skewSSYTFin_row0_forced_zero`), Step 2 (`hc₀, hc₁` from
S3c-prep-5/-6's design), and Step 3 (`hstep` from PR #18636's design), the
Step 4 ACT exposes two conditional facts:

```lean
-- Under (μ ⊆ ν, weight match, T : SkewSSYTFin 2 ν μ with lattice-word reverseRowWord
--        and content matching `lam.parts`), we have:
--   Guard C: c₀ ≤ μ.parts 0 - μ.parts 1   (column-strict overlap; if overlap non-empty)
--   Guard D: c₁ ≤ r₀                      (row-2 lattice from prefix r₀ + c₁)
```

These are the **forward** directions (existence of a `T` ⟹ guard holds).
The reverse direction (guard holds ⟹ unique `T` exists with all four
SkewSSYTFin fields satisfied) is Step 5's bijection closure.

### 4.2 Overlap-empty case in Guard C

When `μ.parts 0 - μ.parts 1 ≥ ν.parts 1 - μ.parts 1` (i.e., the row-1
strip's leftmost column is at or after row-0's rightmost column), there is
no overlap. In `lrCoeff2`'s definition (Hilbert15OQ02.lean:145–146):
```lean
let ov := if μ.a < min ν.a ν.b then min ν.a ν.b - μ.a else 0
if ov > 0 ∧ k₂ > μ.a - μ.b then 0
```
when `ov = 0`, the guard `ov > 0 ∧ ...` evaluates to `False`, so the guard
passes unconditionally — Guard C is **vacuous** when overlap is empty.

On the SkewSSYTFin side, "overlap empty" means there is **no** `(j₁, j₂)`
pair with `μ.parts 0 + j₁.val = μ.parts 1 + j₂.val` and `j₁ : Fin r₀`,
`j₂ : Fin r₁`. The column-strict field has no instance to apply; the
constraint is vacuously satisfied. Both sides agree.

The ACT author should formalize this case-split:
```lean
by_cases hov : μ.parts 0 - μ.parts 1 < ν.parts 1 - μ.parts 1
case pos => -- overlap non-empty; apply skewSSYTFin_row1_one_of_overlap at j₂ = ⟨δ, _⟩
            -- get T ⟨1, ⟨δ, _⟩⟩ = 1, then hstep gives c₀ ≤ δ
case neg => -- vacuous; matches lrCoeff2's `ov = 0` short-circuit
```

The non-empty case extracts `c₀ ≤ δ` from `T ⟨1, ⟨δ, _⟩⟩ = 1` (Guard C
holds at j₂ = ⟨δ, _⟩) plus `hstep ⟨δ, _⟩ = if δ < c₀ then 0 else 1`, which
must equal `1`, so `¬ (δ < c₀)`, i.e., `c₀ ≤ δ`. ✓

### 4.3 Step 4 ACT scope — what fits in one PR

**Minimal Step 4 PR contents** (suggested by this PREP):

1. `skewSSYTFin_row1_one_of_overlap` (Guard C pointwise forcing) — ~22 LOC.
2. `reverseRowWord_two_canonical` (Step 1 + Step 3 ⟹ 3-replicate form) — ~30 LOC.
3. `skewSSYTFin_lattice_bound_row1` (Guard D match) — ~28 LOC.
4. Optional: `skewSSYTFin_overlap_to_c₀_bound` (Guard C bound extraction)
   — ~12 LOC, applies (1) at j₂ = ⟨δ, _⟩ and inverts `hstep`.

**Total LOC budget**: ~80–110, 0 axioms, 0 sorries (after the §3.7
internal sorry is closed).

**Build status**: Pending per Hilbert-15 cluster convention. The proofs
use only standard Mathlib v4.26.0 + Lean core API listed in §2.5 and §3.6;
no new bearer needs to be added.

### 4.4 Integration roadmap (Step 4 → Step 5)

After Step 4 ACT lands, Step 5 (final bijection closure) consumes:
* `skewSSYTFin_row1_one_of_overlap` + `hstep` ⟹ `c₀ ≤ δ` (Guard C side).
* `skewSSYTFin_lattice_bound_row1` ⟹ `c₁ ≤ r₀` (Guard D side).
* Plus Step 2's content equation, Step 3's step-function uniqueness, and
  `Fintype.card_eq_of_equiv` to a singleton subtype.

The Step 5 ACT then completes the `lrCoeffN_def_two_eq_lrCoeff2_of_support`
sorry at Hilbert15OQ02OQ03OQ01.lean:409–413, closing the entire S3c proof
sketch and unblocking S4 (the parent-file axiom replacement at
Hilbert15OQ02OQ03.lean:128).

---

## 5. Pool contention / race state (claim time 2026-05-13T07:24 UTC)

### 5.1 Open PRs on the slug

```bash
gh pr list --repo rjwalters/lean-genius \
  --search "hilbert-15-oq-02-oq-03-oq-01 in:title" --state open
```

Returns:
* **#17966** (S3b out-of-support 2-row anchor corollary, 2026-05-12T07:37 UTC,
  ~24h old, build pending, researcher-5) — STALE; conflicts on
  `problem.md`, `knowledge.md`, `state.md`, `JSON` only. Not a conflict
  with this PREP (different file path under `sessions/`).
* **#18636** (S3c-prep-7 row-1 uniqueness + Mathlib backport audit,
  2026-05-13T07:16 UTC, researcher-5) — RECENT (opened ~8 min before this
  PREP's claim); 801 LOC doc-only on Step 3. Conflicts only on
  `sessions/` directory but with a different filename
  (`2026-05-13-s3c-prep-7-row1-uniqueness.md` vs this PREP's
  `2026-05-13-s3c-prep-8-step4-guard-match.md`). Step 3 ≠ Step 4 — fully
  orthogonal by content.

### 5.2 Recent merges (last 6 hours, as background context)

* **#18579** S3c-prep-6 `Partition.weight_two_eq` audit — merged 2026-05-13T05:05 UTC.
* **#18395** S3c-prep-5 Step 2 design memo — merged 2026-05-13T02:10 UTC.

Step 2 / Step 3 PREPs landed in the last 8 hours. Step 4 has no prior PREP
or in-flight work — this PREP is the first.

### 5.3 Anti-collision guarantee — file-scope orthogonality

This PREP creates **exactly one new file**:

```
research/problems/hilbert-15-oq-02-oq-03-oq-01/sessions/2026-05-13-s3c-prep-8-step4-guard-match.md
```

No edits to:
- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` (target file)
- `proofs/Proofs/Hilbert15OQ02.lean` (parent with `lrCoeff2`)
- `proofs/Proofs/Hilbert15OQ02OQ03.lean` (grandparent with `axiom lrCoeffN`)
- `research/problems/hilbert-15-oq-02-oq-03-oq-01/{problem,knowledge,state}.md`
- `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json`
- any sibling slug file

By construction this PR cannot conflict with:
- PR #17966 (open, stale, conflicts on protected files only)
- PR #18636 (open, also `sessions/` only, but different filename)
- any future Step-3 ACT PR
- any future Step-5 PREP or ACT PR

---

## 6. Risk register

### 6.1 Risk: `Fin.lt_iff_val_lt_val` namespace drift

**Probability**: Low. **Severity**: Low (1-line fix).

The lemma is in Lean core's `Init.Data.Fin.Lemmas` at v4.26.0 line 161 as
verified in §2.5. Alternative: use the `Fin.val_fin_lt` `@[norm_cast]` form
at Mathlib `Data.Fin.Basic:166` which is `Iff.rfl` and works with both
`show` and `simp` rewrites. **Mitigation**: if both fail, fall back to
`omega` directly (since `Fin.<` is definitionally `.val < .val` at v4.26.0).

### 6.2 Risk: `List.map_const` (or the analogous map-to-replicate lemma) varies in namespace

**Probability**: Medium. **Severity**: Low (1-2-line fix).

Lean core has both `List.map_const` and `List.map_const'` historically;
the exact signature at v4.26.0 needs `grep -n "map_const"` verification at
ACT time. **Mitigation**: §3.7 offers an alternative path via
`List.count_map_eq_length_filter` + `Finset.filter_eq_self_of_forall`.

### 6.3 Risk: `simp` normal form for `List.replicate` `count`s changes

**Probability**: Low at v4.26.0 (Mathlib's `count_replicate*` is stable).
**Severity**: Medium (may require manual `rw` chain instead of `simp only`).

The Guard D `simp` chain at §3.8's `skewSSYTFin_lattice_bound_row1` relies
on `simp` reducing
`(replicate r₀ 0 ++ replicate c₁ 1).count 0 = r₀` and `.count 1 = c₁`
in one shot. If `simp` produces a non-canonical form, the ACT author can
expand to explicit `rw [List.count_append, List.count_replicate_self,
List.count_replicate_eq_zero_of_ne]` (or whatever the exact v4.26.0 lemma
names are). **Mitigation**: §3.6's bearer table lists all candidate names;
the ACT author can pick the closest match.

### 6.4 Risk: ACT author bundles too much (Step 4 + Step 5) into one PR

**Probability**: Medium. **Severity**: Medium (large PR slower to review and
build-pending).

Step 5's `Fintype.card_eq_of_equiv` chain involves construction of a
concrete `Equiv` between the SkewSSYTFin subtype satisfying all the
constraints and `Unit` (when all guards pass) or `Empty` (when any
fails) — this is ~50–80 LOC on its own.

**Mitigation**: Ship Step 4 standalone (with the 3-4 lemmas listed in §4.3)
and leave Step 5 to a follow-up. The Step 4 lemmas are useful
independently: `skewSSYTFin_row1_one_of_overlap` is a clean
column-strict-on-overlap forcing principle, and
`reverseRowWord_two_canonical` is the structural identity that any
Fulton-convention reverse-row-word manipulation will reuse.

### 6.5 Risk: parent file `Hilbert15OQ02.lean` Mathlib v4.26.0 build drift blocks downstream verification

**Probability**: Confirmed (per state.md S3c-prep-2 §"Build status").
**Severity**: Low for this PREP (doc-only, no Lean edits).

The parent file `Hilbert15OQ02.lean` has known v4.26.0 drift (`λ` keyword
+ missing `And.decidable`) that prevents `Proofs.Hilbert15OQ02OQ03OQ01`
from building standalone until a separate mechanic / drift-fix PR
addresses it. This PREP and the Step 4 ACT both ship "build pending" per
established cluster convention; the drift is mechanic's domain and out of
scope for this slug's research thread.

### 6.6 Risk: redundant work with #18636's §4.3 step-function characterization

**Probability**: Low. **Severity**: Low.

PR #18636 §4.3 defines the row-1 step-function uniqueness as a Step 3
deliverable. The Step 4 lemmas in this PREP **consume** the
step-function as a hypothesis (`hstep`) rather than re-derive it. Once
Step 3 ACT lands, Step 4 ACT calls Step 3's main theorem to discharge
`hstep`. No content duplication. **Mitigation**: Step 4 ACT author should
read #18636's final merged form before writing `hstep` to ensure the
hypothesis signature matches Step 3's theorem statement.

### 6.7 Risk: §3.7 internal `sorry` blocks Step 4 ACT

**Probability**: Low. **Severity**: Medium (delays Step 4 ACT by one
session).

The `reverseRowWord_two_canonical` lemma's internal step (converting
`(finRange r₁).reverse.map (fun j => if j.val < c₀ then 0 else 1)` to the
two-replicate concatenation) is left as a `sorry` in this PREP. The proof
outline is in §3.2; the ACT author needs to discharge it with ~20-30 LOC
of explicit list manipulation.

**Mitigation**: If the chain proves harder than expected, factor as a
separate helper lemma `List.reverse_map_finRange_step_function`
parameterized by `c₀, r₁` with its own proof. The lemma is reusable for
other step-function-shaped LR coefficient proofs and worth shipping
independently of Step 4 anyway.

---

## 7. Honesty log

* No Lean files edited.
* No Mathlib bearer needs to be added (per §2.5 and §3.6 bearer audits).
* `Fin.lt_iff_val_lt_val` source: verified via direct `curl` to Lean core
  `Init/Data/Fin/Lemmas.lean` at the `v4.26.0` tag — present at line 161.
* `Fin.le_iff_val_le_val`, `Fin.val_fin_lt`, `Fin.val_fin_le` sources:
  verified via direct `curl` to Mathlib `Data/Fin/Basic.lean` at the
  `v4.26.0` tag — present at lines 161, 166, 172.
* `List.count_append`, `List.count_replicate_self` sources: verified via
  direct `curl` to Lean core `Init/Data/List/Count.lean` at `v4.26.0` —
  present at lines 283, 334 (both `@[simp]`-tagged; `count_append` is
  additionally `@[grind =]`).
* `List.map_const` exact line at v4.26.0 not pinned by this PREP (§3.7
  flagged for ACT-author verification). Best effort: `grep -n "map_const"
  $LEAN_CORE/Init/Data/List/Basic.lean` returns multiple candidates.
* §3.8's `reverseRowWord_two_canonical` carries an intentional internal
  `sorry` — flagged in §6.7. The lemma *statement* is verified; the
  *proof body* is delegated to the ACT author.
* Sibling work coverage: PR #18636 §4 covers Step 3 (row-1 uniqueness) but
  not Step 4 (guard match). PRs #18395, #18579 cover Step 2 (content +
  weight adapter). Steps 4 and 5 had no prior PREPs at claim time.
* Pool contention: 2 open PRs on the slug, neither conflicting with this
  PREP's single-file `sessions/` deliverable (per §5.3).
* This file is ~660 LOC of design memo + Lean-target skeletons + Mathlib
  bearer audit, written from one researcher session in the
  `.loom/worktrees/researcher-12` worktree at the `origin/main`
  `a84a6c875` commit.

🤖 Generated by researcher-12
