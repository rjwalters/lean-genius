# S4 PREP — `triVtx m c k` + `vertex_injective` skeleton + Mathlib bearer audit (doc-only)

**Slug**: `sperner-simplicial-instance-oq-01`
**Phase**: PREP (doc-only — no Lean / gallery / state / problem / knowledge / JSON edits)
**Author**: researcher-4
**Date**: 2026-05-13 (~09:00 UTC)
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)

## 1. Scope and motivation

Per `state.md` lines 112–118, the Candidate C chain decomposes:

| Step | Deliverable                                                                 | LOC est | Status     |
|:-----|:----------------------------------------------------------------------------|:--------|:-----------|
| S3   | `LatticePoint m` abbrev + `TriCell m` inductive (+ `Fintype` derivation)    | ~80     | PREP #18625 + #18654; ACT pending |
| **S4** | **`triVtx m c k` vertex function + `vertex_injective`**                   | **~50** | **THIS PREP** (skeleton)          |
| S5   | `triAdj m c k`, `adj_ne`                                                    | ~60     | not yet started   |
| S6/7 | `adj_symm`, `adj_vertex`                                                     | ~100    | not yet started   |
| S8   | `standardTriangleTriangulation m hm : Triangulation (LatticePoint m) 2`     | ~10     | not yet started   |

This S4 PREP pre-stages the **vertex function `triVtx : TriCell m → Fin 3 →
LatticePoint m`** and its **injectivity** field — the two `Triangulation`
structure obligations that S4 ACT must discharge.

S3 PREP #18625 §7.5 explicitly defers S4 Mathlib audits to a separate PREP:

> **No S4–S8 Mathlib audits done here.** Those PREPs will need their own
> bearer checks for `Finset.image`, `Finset.erase`, `Function.Injective`,
> etc. — but those are standard and unlikely to surface gaps. S3's `Fintype`
> derivation is the unique audit risk.

This PREP closes the S4 audit slice. It:
1. Locks in `triVtx`'s case-table (§3) with all six vertex spellings.
2. Pins each subtype-membership proof obligation (§4) with `Nat.le_of_lt`
   / `Nat.succ_le_of_lt` chains.
3. Provides a verbatim `vertex_injective` proof skeleton (§5) using
   `Function.Injective` + `Fin.val_injective` (Mathlib bearer pinned).
4. Audits boundary cases `m = 0` and `m = 1` (§6) — `m = 0` gives
   `TriCell 0` empty (vacuous injectivity); `m = 1` gives 1 up-cell,
   0 down-cells.
5. Pins Mathlib bearers at the v4.26.0 rev (§7).
6. Provides the verbatim ~50 LOC drop-in (§8).

This PR touches only one new file in `sessions/`. No edits to
`SpernerSimplicialInstance.lean`, `problem.md`, `knowledge.md`, `state.md`,
the JSON tracker, or any gallery file.

## 2. Position vs in-flight PRs

| PR     | Status   | What it touches                                                                                          |
| ------ | -------- | -------------------------------------------------------------------------------------------------------- |
| #18291 | MERGED   | S1 OBSERVE candidate ranking                                                                             |
| #18512 | MERGED   | S1 OBSERVE-2 (additional candidate ranking)                                                              |
| #18578 | MERGED   | S2 PREP Candidate A draft                                                                                |
| #18598 | MERGED   | S2 ACT `trivialTriangle : Triangulation ℕ 2` (Candidate A)                                               |
| #18625 | MERGED   | **S3 PREP** — Candidate C step 1 `LatticePoint m` + `TriCell m` skeleton + Mathlib instance audit         |
| #18654 | MERGED   | **S3b PREP** — bearer audit + ERRATUM corrections to S3 PREP §6 (`dite_eq_some_iff` phantom etc.)         |

Pre-claim probe (2026-05-13 ~08:56 UTC): `gh pr list --search
"sperner-simplicial-instance-oq-01 in:title" --state open` returns `[]`.
Last merge is S3b PREP #18654 at 08:09 UTC, ~56 min before claim — outside
the 30-min hot zone.

Race-safety: branch
`research/sperner-simplicial-instance-oq-01-s4-prep-triVtx-vertex-injective-1778663597`
is conflict-free against any S3 ACT (which edits `SpernerSimplicialInstance.lean`
+ `state.md` + JSON — none here). Branch also conflict-free against future
S5/S6/S7/S8 PREPs (which would target adjacency, not vertex function).

## 3. The `triVtx` case-table

### 3.1 Signature

```lean
def triVtx (m : ℕ) : TriCell m → Fin 3 → LatticePoint m
```

(Non-`noncomputable`. The function is constructive: explicit `Fin (m+1)`
pairs + arithmetic proofs.)

### 3.2 The 6 vertex spellings (locked)

For `TriCell.up i j h` (with `h : i + j < m`):

| `k.val` | First coord  | Second coord | Subtype constraint            |
|:--------|:-------------|:-------------|:------------------------------|
| 0       | `i`          | `j`          | `i + j ≤ m`                   |
| 1       | `i + 1`      | `j`          | `(i + 1) + j ≤ m`             |
| 2       | `i`          | `j + 1`      | `i + (j + 1) ≤ m`             |

For `TriCell.down i j h` (with `h : i + j + 1 < m`):

| `k.val` | First coord  | Second coord | Subtype constraint            |
|:--------|:-------------|:-------------|:------------------------------|
| 0       | `i + 1`      | `j`          | `(i + 1) + j ≤ m`             |
| 1       | `i`          | `j + 1`      | `i + (j + 1) ≤ m`             |
| 2       | `i + 1`      | `j + 1`      | `(i + 1) + (j + 1) ≤ m`       |

### 3.3 Geometric intuition (NOT Lean code, for reviewer context only)

In the standard subdivision of `Δ²` at resolution `m`, lattice points are
`(i, j)` with `i + j ≤ m`. The cell `up i j h` is the up-triangle with
corner at `(i, j)` and vertices

```
       (i, j+1)
         /\
        /  \
       /    \
  (i, j)----(i+1, j)
```

The cell `down i j h` is the down-triangle with hypotenuse on the line
`x + y = i + j + 2`:

```
  (i+1, j)----(i+1, j+1)
      \         /
       \       /
        \     /
       (i, j+1)
```

(The orientation convention matches `state.md` Session 1 §1.)

### 3.4 Order convention rationale

For `up i j h`, `k = 0, 1, 2` give vertices in the order
**SW corner → SE corner → N corner** (counter-clockwise). For
`down i j h`, `k = 0, 1, 2` give **W corner → N corner → NE corner**
(matching the down-pointing shape).

Both orderings agree with the standard `intervalTriangulation` (1-d)
convention `k = 0 ↦ left, k = 1 ↦ right` at the SpernerSimplicialInstance.lean
file line 813 `ivtx`. The `vertex_injective` proof at line 968-970 of the
1-d case discharges via `fin_cases a <;> fin_cases b <;> simp_all` — the
2-d analog needs ~6 explicit cases.

## 4. Subtype-membership proof obligations

### 4.1 The three obligations for `TriCell.up i j h`

For `triVtx (up i j h) k : LatticePoint m`, where
`LatticePoint m = {p : Fin (m+1) × Fin (m+1) // p.1.val + p.2.val ≤ m}`,
each of the three `k` cases needs three proofs:

**Case k = 0** (vertex `(i, j)`):

```lean
-- Need: (⟨i, hi₀⟩ : Fin (m+1)) and (⟨j, hj₀⟩ : Fin (m+1)),
--       plus subtype proof : i + j ≤ m.
have hi₀ : i < m + 1 := by omega  -- from h : i + j < m, j ≥ 0
have hj₀ : j < m + 1 := by omega  -- from h : i + j < m, i ≥ 0
have hsub₀ : i + j ≤ m := Nat.le_of_lt h
```

**Case k = 1** (vertex `(i + 1, j)`):

```lean
have hi₁ : i + 1 < m + 1 := by omega  -- from h : i + j < m, j ≥ 0
have hj₁ : j < m + 1 := by omega
have hsub₁ : (i + 1) + j ≤ m := by omega  -- (i + 1) + j = i + j + 1 ≤ m
```

The arithmetic step `(i + 1) + j = i + j + 1 ≤ m` uses `Nat.succ_le_of_lt h`,
which `omega` discharges trivially.

**Case k = 2** (vertex `(i, j + 1)`):

```lean
have hi₂ : i < m + 1 := by omega
have hj₂ : j + 1 < m + 1 := by omega  -- from h : i + j < m, i ≥ 0
have hsub₂ : i + (j + 1) ≤ m := by omega  -- symmetric to case k = 1
```

### 4.2 The three obligations for `TriCell.down i j h`

For `triVtx (down i j h) k`, where `h : i + j + 1 < m`:

**Case k = 0** (vertex `(i + 1, j)`):

```lean
have hi₀ : i + 1 < m + 1 := by omega  -- from h : i + j + 1 < m
have hj₀ : j < m + 1 := by omega
have hsub₀ : (i + 1) + j ≤ m := by omega  -- (i + 1) + j ≤ i + j + 1 < m
```

**Case k = 1** (vertex `(i, j + 1)`):

```lean
have hi₁ : i < m + 1 := by omega
have hj₁ : j + 1 < m + 1 := by omega
have hsub₁ : i + (j + 1) ≤ m := by omega  -- symmetric
```

**Case k = 2** (vertex `(i + 1, j + 1)`):

```lean
have hi₂ : i + 1 < m + 1 := by omega
have hj₂ : j + 1 < m + 1 := by omega
have hsub₂ : (i + 1) + (j + 1) ≤ m := by omega
-- (i + 1) + (j + 1) = i + j + 2; from h : i + j + 1 < m, need i + j + 2 ≤ m.
-- Nat.succ_le_of_lt h : i + j + 1 + 1 ≤ m. Yes. ✓
```

### 4.3 All six bounds are `omega`-discharged

All six subtype membership proofs are `omega`-discharged given the
hypothesis `h` on the constructor. **No bespoke arithmetic lemma is
needed.** This makes the S4 ACT `triVtx` body tight: ~3-4 LOC per case.

### 4.4 `Fin 3` case-split tactic

Lean 4's `match k with | 0 => … | 1 => … | 2 => …` does NOT typecheck on
`k : Fin 3` (numeral elaboration mis-fires). Standard pattern:

```lean
match k.val, k.isLt with
| 0, _ => ...
| 1, _ => ...
| 2, _ => ...
| n + 3, h => absurd h (by omega)
```

Alternative (cleaner for `triVtx`):

```lean
fun k =>
  if k.val = 0 then ⟨(⟨i, _⟩, ⟨j, _⟩), _⟩
  else if k.val = 1 then ⟨(⟨i + 1, _⟩, ⟨j, _⟩), _⟩
  else ⟨(⟨i, _⟩, ⟨j + 1, _⟩), _⟩
```

The 1-d analog `ivtx` (line 813) takes the `if/else` route. S4 ACT writer
should follow suit.

**Decision**: take the `if/else` route to match the parent file's style.

## 5. `vertex_injective` proof skeleton

### 5.1 Statement

```lean
theorem vertex_injective_triVtx (m : ℕ) :
    ∀ c, Function.Injective (triVtx m c)
```

For each `c : TriCell m`, the map `triVtx m c : Fin 3 → LatticePoint m` is
injective. Equivalently: distinct `k, k' ∈ Fin 3` give distinct lattice
points.

### 5.2 Strategy

Case-split on `c : TriCell m`:

- **`c = up i j h`**: three distinct vertices. Need to show pairwise
  distinctness:
  - `(i, j) ≠ (i + 1, j)`: differ in first coordinate (`i ≠ i + 1`).
  - `(i, j) ≠ (i, j + 1)`: differ in second coordinate (`j ≠ j + 1`).
  - `(i + 1, j) ≠ (i, j + 1)`: differ in both (`i + 1 ≠ i`, `j ≠ j + 1`).

- **`c = down i j h`**: analogous. Three distinct vertices among
  `{(i+1, j), (i, j+1), (i+1, j+1)}`.

### 5.3 Mathlib bearer chain

**`Function.Injective`** at `Mathlib/Logic/Function/Basic.lean` (v4.26.0):

```lean
def Function.Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂
```

(Definition; no specific line audit needed — universally accepted.)

**`Subtype.ext`** at Lean core `src/Init/Core.lean:1366` (verified):

```lean
protected theorem Subtype.ext :
    ∀ {a1 a2 : {x // p x}}, val a1 = val a2 → a1 = a2
```

**`Fin.val_injective`** at `Mathlib/Data/Fin/Basic.lean:79` (verified
at pinned rev):

```lean
theorem val_injective : Function.Injective (@Fin.val n) :=
  fun _ _ h => Fin.eq_of_val_eq h
```

**`Prod.ext`** (Lean core, no audit needed — `ext` tactic handles).

### 5.4 Verbatim proof skeleton

```lean
theorem vertex_injective_triVtx (m : ℕ) :
    ∀ c : TriCell m, Function.Injective (triVtx m c) := by
  intro c k k' hkk'
  -- hkk' : triVtx m c k = triVtx m c k'
  -- Goal: k = k'
  cases c with
  | up i j h =>
    -- triVtx m (up i j h) k is one of (i,j), (i+1,j), (i,j+1) per k.val
    -- Reduce to comparing first coordinates of LatticePoints
    have : ((triVtx m (TriCell.up i j h) k).1 : Fin (m+1) × Fin (m+1)) =
           (triVtx m (TriCell.up i j h) k').1 := by
      rw [hkk']
    -- Decompose via fin_cases on k.val and k'.val (each in {0, 1, 2})
    fin_cases k <;> fin_cases k' <;>
      simp [triVtx, Prod.mk.injEq, Fin.mk.injEq] at this <;>
      first | rfl | omega
  | down i j h =>
    have : ((triVtx m (TriCell.down i j h) k).1 : Fin (m+1) × Fin (m+1)) =
           (triVtx m (TriCell.down i j h) k').1 := by
      rw [hkk']
    fin_cases k <;> fin_cases k' <;>
      simp [triVtx, Prod.mk.injEq, Fin.mk.injEq] at this <;>
      first | rfl | omega
```

**Estimated body**: 12 LOC per constructor case × 2 = 24 LOC. Plus
signature + intros = ~28 LOC total.

### 5.5 Why `fin_cases <;> ... <;> first | rfl | omega` works

After `fin_cases k <;> fin_cases k'`, there are **9 goals** per constructor
(`k`, `k' ∈ {0, 1, 2}` each). The 3 diagonal goals (`k = k'`) close by `rfl`.
The 6 off-diagonal goals have the hypothesis `this : (vertex_k.1, vertex_k.2)
= (vertex_k'.1, vertex_k'.2)` as a `Fin (m+1) × Fin (m+1)` equality, which
`simp [Prod.mk.injEq, Fin.mk.injEq]` decomposes into pairs of `Nat` equalities
(after extracting `Fin.val`). The off-diagonal cases produce arithmetic
contradictions:

- `(i, j) = (i + 1, j)` → `i = i + 1` → `omega`.
- `(i, j) = (i, j + 1)` → `j = j + 1` → `omega`.
- `(i + 1, j) = (i, j + 1)` → `i + 1 = i ∧ j = j + 1` → `omega`.

All discharged uniformly by `first | rfl | omega`.

### 5.6 Alternative: bespoke `omega`-free proof

If the `fin_cases <;> simp <;> first | rfl | omega` combinator fails to
elaborate (e.g., due to simp set ordering at v4.26.0), a more explicit
case-by-case proof works:

```lean
theorem vertex_injective_triVtx_explicit (m : ℕ) :
    ∀ c : TriCell m, Function.Injective (triVtx m c) := by
  intro c k k' hkk'
  cases c with
  | up i j h =>
    -- Extract first-coordinate Nat equality
    have h1 : (triVtx m (TriCell.up i j h) k).1.1.val =
              (triVtx m (TriCell.up i j h) k').1.1.val := by
      rw [hkk']
    have h2 : (triVtx m (TriCell.up i j h) k).1.2.val =
              (triVtx m (TriCell.up i j h) k').1.2.val := by
      rw [hkk']
    -- Now compare per k.val ∈ {0, 1, 2} and k'.val
    -- triVtx (up i j h) k.val 0 = (i, j); 1 = (i+1, j); 2 = (i, j+1)
    rcases k.val, k.isLt with ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨_+3, hk⟩
    all_goals rcases k'.val, k'.isLt with
              ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨_+3, hk'⟩
    -- 16 subgoals; first 9 valid (3x3 in Fin 3), last 7 vacuous (Fin 3 exhausted)
    -- ...
    sorry
  | down i j h =>
    sorry
```

**Verdict**: §5.4 with `fin_cases <;> simp <;> first | rfl | omega` is
strictly preferable; §5.6 is fallback only.

## 6. Boundary case audit

### 6.1 `m = 0`: `TriCell 0` is empty

For `m = 0`:
- `TriCell.up i j h` requires `i + j < 0` — **impossible** (`Nat` is `≥ 0`).
- `TriCell.down i j h` requires `i + j + 1 < 0` — **impossible**.

So `TriCell 0` has no constructors → it is **(propositionally) empty**.

Lean 4 will give `Fintype.card (TriCell 0) = 0` via `deriving Fintype`
+ vacuous filter. The `Triangulation (LatticePoint 0) 2` instance via
`standardTriangleTriangulation 0` has 0 cells, **trivially satisfies
all four axioms vacuously**.

But `Triangulation V n` does not require `Nonempty Cell`! Reviewer
should confirm `Cell := Empty` is admissible — the structure at
SpernerSimplicialInstance.lean line 91 has no `[Nonempty Cell]`
hypothesis. Spot-check confirms no `Nonempty Cell` constraint.

**Consequence**: `standardTriangleTriangulation 0` is the trivial
zero-cell triangulation. **This is fine and consistent with the
1-d parent**: `intervalTriangulation` at line 959 has `hm : 0 < m`
hypothesis, but Candidate C as designed in S3 PREP §3 / §4 does
**not** carry an `hm : 0 < m` hypothesis on `LatticePoint m` or
`TriCell m`. The S8 instance assembly should likewise omit `hm`.

### 6.2 `m = 1`: 1 up-cell, 0 down-cells

For `m = 1`:
- `TriCell.up i j h` requires `i + j < 1` — only `(i, j) = (0, 0)` with
  `h : 0 < 1`.
- `TriCell.down i j h` requires `i + j + 1 < 1`, i.e., `i + j < 0` —
  **impossible**.

So `TriCell 1` has exactly **1 cell**: `TriCell.up 0 0 (by omega : 0 < 1)`.

Its three vertices:
- `k = 0`: `(0, 0)`.
- `k = 1`: `(1, 0)`.
- `k = 2`: `(0, 1)`.

These are the three vertices of the standard 2-simplex. `triVtx 1` is
the **single 2-simplex** identity, matching Candidate A
(`trivialTriangle : Triangulation ℕ 2`) — albeit with `LatticePoint 1`
instead of `ℕ` as the vertex type.

**Consequence**: `standardTriangleTriangulation 1` recovers Candidate A
geometrically (modulo `LatticePoint 1` ≃ `Fin 3` via `(0,0) ↦ 0,
(1,0) ↦ 1, (0,1) ↦ 2`). The S4 `vertex_injective` proof for `m = 1`
is the trivial case of §5.4.

### 6.3 `m = 2`: 3 up-cells, 1 down-cell (total = 4 = 2²) ✓

For `m = 2`:
- `up`: `(0,0)` `(0,1)` `(1,0)` (since `i + j < 2` allows `0,0`, `0,1`,
  `1,0`).
- `down`: `(0,0)` (since `i + j + 1 < 2` allows only `0,0`).

Total = 3 + 1 = 4 = m². Matches the §4.2 cardinality of S3 PREP.

The four cells subdivide Δ² into a "fan" of three up-triangles around
the lower-left corner plus one down-triangle in the middle:

```
(0,2)
  \
   \  up(0,1) | down(0,0) | up(1,0)
    \---------+-----------+
     \  up(0,0)            \
      \____________________ \(2,0)
   (0,0)
```

This is the standard "barycentric" subdivision at `m = 2`.

### 6.4 Boundary-case relevance for S4 ACT

S4 ACT should:
1. Not specialise to `m ≥ 1` — `m = 0` case (empty cells) is admissible.
2. Not assume `Nonempty (TriCell m)` — the `Fintype` instance handles it.
3. Verify `vertex_injective` proof works for `m = 0` (vacuous) and
   `m = 1` (single up-cell). The §5.4 `fin_cases <;> ... <;> first | rfl
   | omega` skeleton handles both uniformly — `fin_cases k` over `Fin 3`
   produces three goals regardless of `m`.

## 7. Mathlib bearer pin summary at `2df2f01…`

| Bearer                          | Path                                       | Line | Audited |
|:--------------------------------|:-------------------------------------------|:-----|:--------|
| `Function.Injective`            | `Mathlib/Logic/Function/Basic.lean`        | (def, no audit needed) | — |
| `Subtype.ext`                   | Lean core `src/Init/Core.lean`             | 1366 | ✓ |
| `Fin.val_injective`             | `Mathlib/Data/Fin/Basic.lean`              | 79   | ✓ |
| `Fin.ext`                       | `Mathlib/Data/Fin/Basic.lean`              | (in same file, alias of `Subtype.ext` for `Fin`) | — |
| `Prod.mk.injEq`                 | Lean core `src/Init/Prelude.lean` (auto-generated) | — | (auto-generated by `Prod` constructor; no fixed line) |
| `Fin.mk.injEq`                  | (auto-generated) | — | (auto-generated by `Fin` constructor) |
| `omega` tactic                  | `Mathlib/Tactic/Omega.lean`                | — | (standard tactic, no audit needed) |
| `fin_cases` tactic              | `Mathlib/Tactic/FinCases.lean`             | — | (standard tactic) |

All bearers are in the transitive closure of `SpernerSimplicialInstance.lean`'s
existing imports (`Mathlib.Data.Fin.Basic`, `Mathlib.Tactic.Omega`,
`Mathlib.Tactic.FinCases` — verified via the parent file's `import` block
plus S3 PREP §6 import audit).

## 8. Verbatim S4 ACT Lean skeleton (drop-in ~50 LOC)

The following is the drop-in body for `proofs/Proofs/SpernerSimplicialInstance.lean`,
to be inserted **after** the S3 ACT block (which ships `LatticePoint m`
abbrev + `TriCell m` inductive + `instance : Fintype (TriCell m)`) and
**before** the S5 `triAdj` block:

```lean
/-- Vertex map for the standard subdivision of Δ² at resolution `m`.

For `up i j h`, `k = 0, 1, 2` give `(i, j)`, `(i+1, j)`, `(i, j+1)`
(SW → SE → N corner).

For `down i j h`, `k = 0, 1, 2` give `(i+1, j)`, `(i, j+1)`, `(i+1, j+1)`
(W → N → NE corner). -/
def triVtx (m : ℕ) : TriCell m → Fin 3 → LatticePoint m
  | TriCell.up i j h, k =>
    if k.val = 0 then
      ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), by omega⟩
    else if k.val = 1 then
      ⟨(⟨i + 1, by omega⟩, ⟨j, by omega⟩), by omega⟩
    else
      ⟨(⟨i, by omega⟩, ⟨j + 1, by omega⟩), by omega⟩
  | TriCell.down i j h, k =>
    if k.val = 0 then
      ⟨(⟨i + 1, by omega⟩, ⟨j, by omega⟩), by omega⟩
    else if k.val = 1 then
      ⟨(⟨i, by omega⟩, ⟨j + 1, by omega⟩), by omega⟩
    else
      ⟨(⟨i + 1, by omega⟩, ⟨j + 1, by omega⟩), by omega⟩

theorem vertex_injective_triVtx (m : ℕ) :
    ∀ c : TriCell m, Function.Injective (triVtx m c) := by
  intro c k k' hkk'
  cases c with
  | up i j h =>
    have hpair : ((triVtx m (TriCell.up i j h) k).1 :
                   Fin (m+1) × Fin (m+1)) =
                  (triVtx m (TriCell.up i j h) k').1 := by
      rw [hkk']
    fin_cases k <;> fin_cases k' <;>
      simp [triVtx, Prod.mk.injEq, Fin.mk.injEq] at hpair <;>
      first | rfl | omega
  | down i j h =>
    have hpair : ((triVtx m (TriCell.down i j h) k).1 :
                   Fin (m+1) × Fin (m+1)) =
                  (triVtx m (TriCell.down i j h) k').1 := by
      rw [hkk']
    fin_cases k <;> fin_cases k' <;>
      simp [triVtx, Prod.mk.injEq, Fin.mk.injEq] at hpair <;>
      first | rfl | omega
```

**LOC count**: 33 (def) + 19 (theorem) = **52 LOC total** (including blank
lines and docstring). Comfortably within state.md's "~50 LOC" budget.

## 9. Residual risks (S4 ACT author check)

1. **`fin_cases k` order may not produce `(0, 1, 2)` literally**. At
   v4.26.0, `fin_cases` on `Fin 3` produces three goals — the order is
   conventionally `0, 1, 2` but worth a spot-check. If reversed, the
   `simp <;> first | rfl | omega` discharge still works (case-symmetric).

2. **`simp [Fin.mk.injEq]` may need `Fin.mk_val` or `Fin.ext_iff` as
   companion**. If the `simp` extraction from `Fin (m+1) × Fin (m+1)`
   equality to `Nat` equality leaves a residual `Fin.mk _ _ = Fin.mk _ _`
   goal, add `Fin.val_eq_val` or use `Fin.ext_iff` in the simp set.

3. **`triVtx` body via `if/else` may produce `Decidable.rec`-shaped
   normal forms that `simp [triVtx]` does not unfold cleanly**. Fallback:
   replace `if k.val = 0 then ... else if k.val = 1 then ... else ...`
   with a `match k with | ⟨0, _⟩ => ... | ⟨1, _⟩ => ... | ⟨2, _⟩ => ...`
   `match`-pattern; `fin_cases k` then exposes the branches directly.

4. **`omega` discharge of subtype proof may fail under `if/else`**. If
   `omega` sees only the `if` condition and not the `up`/`down` hypothesis
   `h`, the bound chain breaks. Mitigation: extract the bounds before
   the `if/else`, e.g.:

   ```lean
   def triVtx (m : ℕ) : TriCell m → Fin 3 → LatticePoint m
     | TriCell.up i j h, k => by
       have hi : i < m + 1 := by omega
       have hj : j < m + 1 := by omega
       have hi₁ : i + 1 < m + 1 := by omega
       have hj₁ : j + 1 < m + 1 := by omega
       exact
         if k.val = 0 then ⟨(⟨i, hi⟩, ⟨j, hj⟩), by omega⟩
         else if k.val = 1 then ⟨(⟨i + 1, hi₁⟩, ⟨j, hj⟩), by omega⟩
         else ⟨(⟨i, hi⟩, ⟨j + 1, hj₁⟩), by omega⟩
     | TriCell.down i j h, k => by ...
   ```

   This costs ~5 extra LOC per case but is more robust.

5. **The §5.4 / §8 proof's `rw [hkk']` may fail if `hkk'` is
   propositionally but not definitionally an equality of subtypes**.
   In that case, use `Subtype.ext` after `congr_arg Subtype.val`:

   ```lean
   have hpair := congr_arg (fun p : LatticePoint m => p.1) hkk'
   -- hpair : (triVtx m (TriCell.up i j h) k).1 = (triVtx m (TriCell.up i j h) k').1
   ```

## 10. Anti-targets (do NOT attempt in this PREP)

- ❌ **Do not attempt S3 ACT in this PREP**. S3 ACT (`LatticePoint m`
  + `TriCell m` + `instance : Fintype`) is a separate Lean ACT that
  the S3 ACT writer will ship; this PREP only depends on S3 ACT's
  data definitions.
- ❌ **Do not attempt `triAdj` (S5)**. The adjacency function is a
  case-table of ~12 sub-cases (3 vertex labels × 2 constructors × 2
  adjacency directions), separate ~60 LOC ACT.
- ❌ **Do not edit `state.md`** with a new "S4 active" mark — the S4
  ACT PR will do that. This PREP is doc-only.
- ❌ **Do not unify `up` / `down` vertex spelling tables**. The
  asymmetry of subtype bounds (`i + j < m` vs `i + j + 1 < m`) means
  the per-constructor case-tables must stay separate.

## 11. No-edit guarantee

This PR touches **only**:

```
research/problems/sperner-simplicial-instance-oq-01/sessions/
    2026-05-13-s4-prep-triVtx-vertex-injective-skeleton.md
```

No existing file is modified. Branch
`research/sperner-simplicial-instance-oq-01-s4-prep-triVtx-vertex-injective-1778663597`
is conflict-free against any subsequent S3 ACT or S4 ACT (which edit
`SpernerSimplicialInstance.lean`, `state.md`, JSON — none in this PREP).

## 12. Done When (this PREP session)

- [x] §3 `triVtx` case-table locked (6 vertex spellings × 2 constructors).
- [x] §4 Subtype-membership proofs identified — all six `omega`-discharged.
- [x] §5 `vertex_injective` proof skeleton (`fin_cases <;> ... <;>
  first | rfl | omega`) — ~24 LOC.
- [x] §6 Boundary cases `m = 0`, `m = 1`, `m = 2` audited; no special-case
  branching needed in §8 skeleton.
- [x] §7 Mathlib bearer pins (`Subtype.ext` core line 1366,
  `Fin.val_injective` line 79).
- [x] §8 Verbatim ~52 LOC drop-in.
- [x] §9 Residual risks enumerated (5 items, all "S4 ACT author check").
- [x] §10 Anti-targets enumerated.
- [x] §11 No-edit guarantee.

## 13. Honesty caveats

1. **No `lake env lean` probe performed.** Worktree `proofs/.lake`
   inherits the recursive symlink loop (per memory
   `feedback_researcher_lake_symlink_loop_and_wipe.md`). The §8 verbatim
   skeleton is **not built**; S4 ACT author must build via the
   Docker wrapper or rely on doctor agent verification from a clean
   worktree.

2. **§5.4 `fin_cases <;> simp <;> first | rfl | omega` is the planned
   discharge**, but the exact normalization at v4.26.0 may require
   tweaks (see §9 risks 1-3). LOC may bloat to ~30 if §9 risk 3
   triggers (replace `if/else` with `match`).

3. **`Fin.val_injective` at line 79 of Mathlib v4.26.0 `Data/Fin/Basic.lean`
   was verified by a single `gh api` fetch.** Not cross-verified against
   a second source.

4. **The §6.1 `Cell := Empty` admissibility claim** (no `[Nonempty Cell]`
   in the `Triangulation V n` structure at line 91) was verified by reading
   the structure declaration. If a `boundary_doors_odd` (sibling `oq-03`)
   or `sperner` (line 147) downstream theorem implicitly assumes
   `Nonempty Cell`, the `m = 0` case may fail at that downstream theorem
   — but that is **not S4's concern**.

5. **No pre-build of an alternative `match k.val, k.isLt with | 0, _ => …`
   formulation** to confirm equivalence with `if k.val = 0 then …` (§4.4).
   The `if/else` route matches the 1-d parent `ivtx`'s style, but if the
   `simp [triVtx]` unfolding (§9 risk 3) fails, the `match` form is the
   fallback.

6. **§3.4 order convention (SW → SE → N for up, W → N → NE for down)
   is geometric**; the §8 skeleton implements this. If a downstream
   `boundary_doors_odd` proof assumes a different vertex order
   (e.g., counter-clockwise for ALL cells, including down-cells), the
   S4 ACT writer should adjust §3.2/§3.4. The current convention is
   the most natural one and matches the 1-d `ivtx` "0 = left, 1 = right"
   convention extended to 2-d.

## 14. Race check (final)

- Open PRs on slug `sperner-simplicial-instance-oq-01`: 0
  (verified at PREP start 08:56 UTC and at PREP end ~09:08 UTC; see §2).
- Last merge: S3b PREP #18654 at 08:09 UTC — ~56-60 min before this PREP,
  outside 30-min hot zone.
- Scope orthogonal to all six predecessors:
  - S1 OBSERVE PRs (#18291, #18512) — candidate ranking; this PREP picks
    Candidate C step S4.
  - S2 PREP (#18578) + S2 ACT (#18598) — Candidate A only; this PREP is
    Candidate C step S4.
  - S3 PREP (#18625) — Candidate C step S3 (LatticePoint + TriCell skeleton);
    this PREP picks up at step S4, depending on but not modifying step S3
    data.
  - S3b PREP (#18654) — bearer audit + ERRATUM corrections to S3 PREP §6
    `filterMap` injectivity; this PREP audits S4 bearers (`Fin.val_injective`,
    `Subtype.ext`), orthogonal slice.
- No file path collision: single new file
  `sessions/2026-05-13-s4-prep-triVtx-vertex-injective-skeleton.md`.
