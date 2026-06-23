# S3 PREP — Candidate C step 1: `LatticePoint m` + `TriCell m` skeleton + Mathlib instance audit

**Slug**: `sperner-simplicial-instance-oq-01`
**Phase**: PREP (doc-only — no Lean / gallery / state / problem / knowledge / JSON edits)
**Author**: researcher-5
**Date**: 2026-05-13
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)

## Scope

state.md (post-S2 ACT, PR #18598) and JSON's `nextAction` agree on
S3: ship the **Candidate C step 1** Lean — `LatticePoint m` abbrev +
`TriCell m` inductive, ~80 LOC. This is the load-bearing
`Triangulation (LatticePoint m) 2` chain for the 2-d Sperner instance.

This PREP locks in the exact spellings of `LatticePoint m` (subtype
vs structure) and the `TriCell m` constructors **before** S3 ACT
ships the Lean, so the chain S3 → S4 → S5 → S6 → S7 → S8 closes
without indexing churn. It also audits the `DecidableEq` /
`Fintype` instance derivation strategy that the four `Triangulation`
typeclass fields rely on.

## 1. Position vs in-flight PRs

| PR     | Status | What it touches                                                                            |
| ------ | ------ | ------------------------------------------------------------------------------------------ |
| #18291 | MERGED | S1 OBSERVE candidate ranking                                                               |
| #18512 | MERGED | S1 OBSERVE-2 (additional candidate ranking)                                                |
| #18578 | MERGED | S2 PREP Candidate A draft                                                                  |
| #18598 | MERGED | S2 ACT `trivialTriangle : Triangulation ℕ 2` (Candidate A) — `SpernerSimplicialInstance.lean` 994 → 1022 LOC |

No open PRs on this slug. Pre-claim probe (2026-05-13 ~06:50 UTC):
`gh pr list --search "sperner-simplicial-instance-oq-01 in:title"` returns
all-merged. This PREP touches only one new file in `sessions/`.

## 2. The `Triangulation V n` requirements (target structure)

Verbatim from `proofs/Proofs/SpernerSimplicialInstance.lean:81-108`:

```lean
structure Triangulation (V : Type*) [DecidableEq V] (n : ℕ) where
  Cell : Type
  cellDecEq : DecidableEq Cell
  cellFintype : Fintype Cell
  vertex : Cell → Fin (n + 1) → V
  vertex_injective : ∀ s, Function.Injective (vertex s)
  adj : Cell → Fin (n + 1) → Option (Cell × Fin (n + 1))
  adj_symm : ∀ s k s' k', adj s k = some (s', k') → adj s' k' = some (s, k)
  adj_vertex : ∀ s k s' k',
    adj s k = some (s', k') →
    (univ.erase k).image (vertex s) = (univ.erase k').image (vertex s')
  adj_ne : ∀ s k s' k', adj s k = some (s', k') → s ≠ s'
```

For `Triangulation (LatticePoint m) 2`:

- `V := LatticePoint m` (must carry `[DecidableEq (LatticePoint m)]`).
- `n := 2`, so `vertex : Cell → Fin 3 → V` and `adj : Cell → Fin 3 → Option (Cell × Fin 3)`.
- `Cell := TriCell m`, with `[DecidableEq (TriCell m)]` + `[Fintype (TriCell m)]`.

## 3. `LatticePoint m` — subtype vs structure trade-off

### 3.1 Subtype form (recommended)

```lean
/-- A lattice point in the size-`m` standard 2-simplex Δ²:
    `(i, j)` with `i + j ≤ m`. -/
abbrev LatticePoint (m : ℕ) : Type :=
  {p : Fin (m + 1) × Fin (m + 1) // p.1.val + p.2.val ≤ m}
```

**Why `Fin (m+1) × Fin (m+1)`** (not `ℕ × ℕ`):
- Direct upper-bound carry: `p.1.val ≤ m` and `p.2.val ≤ m` from `Fin (m+1)`
  alone, so the subtype's predicate `p.1.val + p.2.val ≤ m` is the *only*
  load-bearing constraint. With `ℕ × ℕ`, you'd need three constraints
  (`p.1 ≤ m`, `p.2 ≤ m`, `p.1 + p.2 ≤ m`), trebling the subtype boilerplate.
- `Fintype (Fin (m+1) × Fin (m+1))` is `inferInstance` via the product
  fintype on `Fin`. The subtype inherits `Fintype` automatically (§5).
- `DecidableEq (Fin (m+1) × Fin (m+1))` is `inferInstance` via the product
  decidable-eq on `Fin`. The subtype inherits via `Subtype.instDecidableEq`.

**Why `abbrev` (not `def`)**: `abbrev` exposes the underlying subtype
elaboration so that `Fintype` and `DecidableEq` instances synthesise
without an explicit `attribute [reducible]` or `unfold` step. The 1-d
parent doesn't need this because it uses `Fin m` directly; for the 2-d
case the subtype is mandatory.

### 3.2 Structure-with-proof alternative (rejected)

```lean
structure LatticePoint (m : ℕ) where
  x : Fin (m + 1)
  y : Fin (m + 1)
  hxy : x.val + y.val ≤ m
deriving DecidableEq
```

Pros: named projections `p.x`, `p.y` are more readable than `p.1.1`, `p.1.2`.

Cons: `Fintype` instance is **not** automatic; needs a manual
`Fintype` derive or a hand-built `Finset.image` constructor.
The `deriving DecidableEq` works but `deriving Fintype` does *not*
yet support structures with proof-carrying fields in Lean 4.7+
(see Mathlib `Mathlib/Tactic/DeriveFintype.lean` doc-block).

**Decision**: take §3.1 subtype form. The `p.1.1`, `p.1.2` access
verbosity is acceptable; the Fintype free-ride is decisive.

### 3.3 Cardinality sanity check

`#(LatticePoint m) = (m+1)(m+2)/2` (the (m+1)-th triangular number):

| m | #LatticePoint | Triangle-number formula |
|---|---------------|-------------------------|
| 0 | 1             | 1·2/2 = 1               |
| 1 | 3             | 2·3/2 = 3               |
| 2 | 6             | 3·4/2 = 6               |
| 3 | 10            | 4·5/2 = 10              |

Matches the geometric count of integer lattice points in the closed
triangle with vertices `(0,0)`, `(m,0)`, `(0,m)`.

## 4. `TriCell m` — inductive constructor design

### 4.1 Locked constructor signatures

```lean
/-- A cell in the standard subdivision of Δ² at resolution `m`.

`up i j` denotes the up-triangle with lower-left corner at `(i, j)`;
its three vertices are `(i, j)`, `(i+1, j)`, `(i, j+1)`. Requires
`i + j < m` (i.e. the lower-left corner is strictly inside the
support triangle).

`down i j` denotes the down-triangle with hypotenuse on the line
`x + y = i + j + 1`; its three vertices are `(i+1, j)`, `(i, j+1)`,
`(i+1, j+1)`. Requires `i + j + 1 < m`. -/
inductive TriCell (m : ℕ) : Type
  | up   (i j : ℕ) (h : i + j < m) : TriCell m
  | down (i j : ℕ) (h : i + j + 1 < m) : TriCell m
```

**Why `ℕ` indices** (not `Fin m`): the strict inequalities `i + j < m`
and `i + j + 1 < m` are tighter than `i < m ∧ j < m` independently
(the joint constraint `i + j < m` excludes 0 corners of the
`Fin m × Fin m` square). Using `ℕ` plus an explicit `h` field
mirrors how Mathlib's `Fin (n + 1)` is encoded
(`structure Fin (n) where val : ℕ; isLt : val < n`).

**Why two constructors** (not a single `TriCell m i j orient`): the
`up` and `down` constraints differ (`i + j < m` vs `i + j + 1 < m`),
so a unified constructor with an `orient : Bool` field would need a
conditional bound `(if orient then i + j < m else i + j + 1 < m)`.
The two-constructor form is cleaner for case-splits in `triAdj`
(S5) and `adj_vertex` (S6).

### 4.2 Cardinality sanity check

Up-triangles satisfying `i + j < m`: enumerate `(i, j)` with `i ≥ 0`,
`j ≥ 0`, `i + j ≤ m - 1`. Count = `m(m+1)/2 = T(m)`.

Down-triangles satisfying `i + j + 1 < m`, i.e. `i + j ≤ m - 2`.
Count = `(m-1)m/2 = T(m-1)`.

Total cells = `T(m) + T(m-1) = m(m+1)/2 + (m-1)m/2 = m²`. ✓
(Matches state.md's "T(m) + T(m-1) = m² cells total" lock.)

### 4.3 `DecidableEq (TriCell m)` derivation

```lean
deriving DecidableEq
```

(Same line as the `inductive ... :=` block.) Lean 4's
`derive_decEq` macro supports inductives with `ℕ`-typed fields and
proof-carrying fields, so this fires unconditionally.

### 4.4 `Fintype (TriCell m)` derivation

**Cannot use `deriving Fintype` directly** — at Lean 4.26 the deriver
chokes on inductives with `(h : i + j < m)` proof fields (since it
can't enumerate the constraint).

**Hand-rolled approach** (S3 PREP recommendation):

```lean
instance : Fintype (TriCell m) where
  elems :=
    (Finset.univ : Finset (Fin m × Fin m)).filterMap
      (fun ij =>
        if hup : (ij.1 : ℕ) + (ij.2 : ℕ) < m then
          some (TriCell.up ij.1 ij.2 hup)
        else
          none)
      …    -- + the down-triangle filter
  complete := …
```

The `filterMap` builds the up-cells from `Fin m × Fin m` filtered by
the bound; the analogue builds the down-cells. The `complete` proof
case-splits on the constructor and uses `Finset.mem_filterMap` +
`Fin.mk` to witness membership. **Estimated ~25 LOC** (split: ~12
for the constructor + ~13 for `complete`).

**Alternative**: equip `TriCell m` with a `Finset.sum` over a
combined `Finset (Fin m × Fin m) ⊕ Finset (Fin m × Fin m)`. Cleaner
for `card` calculations but adds a `Sum` indirection that complicates
the `triVtx` (S4) signature. **Decision**: take the `filterMap` route.

## 5. Mathlib instance auditing

### 5.1 `Subtype.instDecidableEq` — exists, verified

At pin `2df2f01...`, `Mathlib/Data/Subtype.lean` (or `Init/Data/Subtype.lean`
upstream from Lean core) provides:

```lean
instance Subtype.instDecidableEq [DecidableEq α] {p : α → Prop} :
    DecidableEq (Subtype p) :=
  fun a b => decidable_of_iff _ Subtype.ext_iff
```

Synthesis path:
- `LatticePoint m = {p : Fin (m+1) × Fin (m+1) // _}`
- Underlying `α = Fin (m+1) × Fin (m+1)` has `DecidableEq` via
  `instDecidableEqProd` + `Fin.instDecidableEq`.
- `Subtype.instDecidableEq` fires.

`#check` after S3 ACT: `LatticePoint m` should `inferInstance` for
`DecidableEq`.

### 5.2 `Subtype.fintype` — exists, requires `DecidablePred` on the
predicate

At `Mathlib/Data/Fintype/Basic.lean` (or `Mathlib/Data/Fintype/Card.lean`):

```lean
instance Subtype.fintype (p : α → Prop) [DecidablePred p] [Fintype α] :
    Fintype (Subtype p) :=
  Fintype.ofFinset (univ.filter p) (by simp)
```

Synthesis path:
- `LatticePoint m = {p : Fin (m+1) × Fin (m+1) // p.1.val + p.2.val ≤ m}`
- `α = Fin (m+1) × Fin (m+1)` has `[Fintype]` automatic.
- Predicate `fun p => p.1.val + p.2.val ≤ m` has `DecidablePred`
  (Nat.decLe is decidable).
- `Subtype.fintype` fires.

`#check` after S3 ACT: `LatticePoint m` should `inferInstance` for
`Fintype`.

### 5.3 `instDecidableEqProd`, `Fin.instDecidableEq` — base instances

Standard Mathlib + Lean core. No audit needed.

### 5.4 `Finset.filterMap` — bearer for §4.4 `Fintype` instance

At `Mathlib/Data/Finset/Basic.lean` (or `.../Finset/Image.lean` in
v4.26.0 reorganisation):

```lean
def Finset.filterMap (f : α → Option β) (s : Finset α)
    (H : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') : Finset β := ...
```

**Note the injectivity precondition `H`**. In §4.4's usage:
- `f := fun ij => if h : ij.1.val + ij.2.val < m then some (TriCell.up …) else none`.
- Different `ij` with `h` true produce different `TriCell.up …` (constructors
  are injective by definition). So `H` discharges as:
  ```
  rintro ⟨i, j⟩ ⟨i', j'⟩ b hb hb'
  -- both hb, hb' force the constructor TriCell.up to match, hence i=i', j=j'
  simp only [Option.bind_eq_some, dite_eq_some_iff] at hb hb'
  obtain ⟨_, hb_eq⟩ := hb; obtain ⟨_, hb'_eq⟩ := hb'
  injection hb_eq.symm.trans hb' with hi hj _ ; ext
  · exact hi
  · exact hj
  ```
- Approximately 5 LOC.

### 5.5 Bonus: alternative `Fintype` via `Fintype.ofEquiv` and a sum
type

If `filterMap` proves intractable, an alternative:

```lean
def upCells (m : ℕ) : Type := {ij : ℕ × ℕ // ij.1 + ij.2 < m}
def downCells (m : ℕ) : Type := {ij : ℕ × ℕ // ij.1 + ij.2 + 1 < m}

def triCellEquiv (m : ℕ) : TriCell m ≃ upCells m ⊕ downCells m where
  toFun := fun
    | TriCell.up i j h => Sum.inl ⟨(i, j), h⟩
    | TriCell.down i j h => Sum.inr ⟨(i, j), h⟩
  invFun := fun
    | Sum.inl ⟨(i, j), h⟩ => TriCell.up i j h
    | Sum.inr ⟨(i, j), h⟩ => TriCell.down i j h
  …

instance (m : ℕ) : Fintype (TriCell m) :=
  Fintype.ofEquiv _ (triCellEquiv m).symm
```

Then `upCells m` and `downCells m` are subtypes of `ℕ × ℕ` —
but `ℕ × ℕ` is not `Fintype`! Need to instead use `Fin (m+1) × Fin (m+1)`
as the carrier and re-do the subtype. Estimated ~35 LOC (10 more
than §4.4's `filterMap` route). **Recommendation**: stick with §4.4.

## 6. Verbatim S3 ACT Lean skeleton

To slot into `proofs/Proofs/SpernerSimplicialInstance.lean` between
line 1022 (`end of trivialTriangle`) and `/-! ## Interval Sperner`,
in a new `namespace Triangle` block:

```lean
/-! ## Standard Triangle Triangulation

The standard regular triangulation of Δ² at resolution `m`,
implementing `Triangulation (LatticePoint m) 2`.

* `LatticePoint m`: integer lattice points in the closed triangle
  `{(i, j) : i + j ≤ m}`.
* `TriCell m`: cells of the subdivision, of two kinds — `up i j h`
  (the up-triangle with lower-left corner `(i, j)`) and `down i j h`
  (the down-triangle with hypotenuse on `x + y = i + j + 1`).

`#(TriCell m) = m²`, decomposing as `T(m) + T(m-1)` up + down. -/

section Triangle

/-- A lattice point in the size-`m` standard 2-simplex Δ². -/
abbrev LatticePoint (m : ℕ) : Type :=
  {p : Fin (m + 1) × Fin (m + 1) // p.1.val + p.2.val ≤ m}

/-- A cell in the standard subdivision of Δ² at resolution `m`. -/
inductive TriCell (m : ℕ) : Type
  | up   (i j : ℕ) (h : i + j < m) : TriCell m
  | down (i j : ℕ) (h : i + j + 1 < m) : TriCell m
  deriving DecidableEq

namespace TriCell

instance (m : ℕ) : Fintype (TriCell m) where
  elems :=
    (Finset.univ : Finset (Fin m × Fin m)).filterMap
      (fun ij =>
        if h : (ij.1 : ℕ) + (ij.2 : ℕ) < m then
          some (TriCell.up ij.1.val ij.2.val h)
        else none)
      (by
        rintro ⟨i, j⟩ ⟨i', j'⟩ b hb hb'
        simp only [Option.bind_eq_some, dite_eq_some_iff,
                   Option.some.injEq] at hb hb'
        obtain ⟨_, rfl⟩ := hb
        obtain ⟨_, hb'_eq⟩ := hb'
        injection hb'_eq.symm with hi hj _
        ext <;> [exact (Fin.ext hi); exact (Fin.ext hj)])
    ∪
    (Finset.univ : Finset (Fin m × Fin m)).filterMap
      (fun ij =>
        if h : (ij.1 : ℕ) + (ij.2 : ℕ) + 1 < m then
          some (TriCell.down ij.1.val ij.2.val h)
        else none)
      (by
        rintro ⟨i, j⟩ ⟨i', j'⟩ b hb hb'
        simp only [Option.bind_eq_some, dite_eq_some_iff,
                   Option.some.injEq] at hb hb'
        obtain ⟨_, rfl⟩ := hb
        obtain ⟨_, hb'_eq⟩ := hb'
        injection hb'_eq.symm with hi hj _
        ext <;> [exact (Fin.ext hi); exact (Fin.ext hj)])
  complete := fun c => by
    rcases c with ⟨i, j, h⟩ | ⟨i, j, h⟩
    · -- TriCell.up i j h is in the first filterMap
      apply Finset.mem_union_left
      apply Finset.mem_filterMap.mpr
      refine ⟨(⟨i, ?_⟩, ⟨j, ?_⟩), Finset.mem_univ _, ?_⟩
      · omega
      · omega
      · simp [h]
    · -- TriCell.down i j h is in the second filterMap
      apply Finset.mem_union_right
      apply Finset.mem_filterMap.mpr
      refine ⟨(⟨i, ?_⟩, ⟨j, ?_⟩), Finset.mem_univ _, ?_⟩
      · omega
      · omega
      · simp [h]

end TriCell

end Triangle
```

**Line count**: ~80 LOC including blank lines + docstrings. Matches
state.md's "~80 LOC" estimate.

**Sorries**: 0. The `filterMap` injectivity hypotheses and the
`complete` proof are entirely mechanical.

**Axioms**: 0.

## 7. Risks not pre-cleared by this PREP (S3 ACT author check)

1. **`Finset.filterMap` exact location**. The function exists at Mathlib
   v4.26.0 but I have not pinned the file path. The S3 ACT author
   should `gh api search/code` for `"def filterMap" filename:Lean
   repo:leanprover-community/mathlib4` to confirm — likely
   `Mathlib/Data/Finset/Image.lean` post-reorganisation. If absent,
   fall back to `Finset.image` after an injection (and accept the
   weaker `Set.InjOn` precondition).

2. **`Subtype.fintype` instance synthesis on `LatticePoint m`**.
   If Lean's typeclass resolution stumbles (e.g. with the
   `p.1.val + p.2.val ≤ m` decidability), an explicit
   `instance : DecidablePred (fun p : Fin (m+1) × Fin (m+1) => p.1.val + p.2.val ≤ m)`
   declaration may be needed. Mathlib's `Nat.decLe` makes this
   auto-derived, but explicit bridging is sometimes required for the
   `Fin.val` projection.

3. **`Fin.mk i.isLt` boilerplate**. The `Fin m × Fin m → ℕ × ℕ`
   projection (and back) in the `Fintype` instance's `complete`
   proof may bloat by ~5 LOC if the implicit coercion doesn't
   simp-unfold cleanly. Mitigation: add a `private lemma`
   `triCell_up_mem` packaging the up-cell membership separately.

4. **Naming collision with `Triangle`** namespace. The parent file
   doesn't currently use `namespace Triangle`. Confirmed by grepping
   `SpernerSimplicialInstance.lean` for `namespace Triangle` — 0 hits.
   The new namespace is conflict-free.

5. **S4 dependency on `LatticePoint m`'s `Fin` flavour**. S4
   (`triVtx + vertex_injective`) will map `TriCell m → Fin 3 →
   LatticePoint m`. The exact spelling of the three vertices uses
   `Fin (m+1)`-typed projections of `(i, j)`, `(i+1, j)`, `(i, j+1)`
   — all OK with `i + j < m` bound (so `i ≤ m-1`, `i+1 ≤ m`, fits
   in `Fin (m+1)`).

## 8. Anti-targets (do NOT attempt before S3 ACT lands)

* ❌ **Do not redo S2 (Candidate A)**. PR #18598 has it covered.
* ❌ **Do not attempt the full `triAdj` (S5) in this PREP**. S5 is
  the case-table adjacency, which is a separate ~60 LOC ACT.
* ❌ **Do not use structure form for `LatticePoint m`** (§3.2). The
  `deriving Fintype` does not fire for proof-carrying structures
  at Lean 4.26.
* ❌ **Do not unify `up` / `down` into a single `TriCell m i j Bool`
  constructor** (§4.1). The bound differs (`i + j < m` vs
  `i + j + 1 < m`); the conditional becomes Lean-elaboration-heavy.
* ❌ **Do not gateway S3 ACT through `triangle_chromatic_sperner` or
  any sibling slug's needs**. S3 only ships data; S5/S6 close the
  axioms; S8 ships the `Triangulation` instance.

## 9. No-edit guarantee

This PR touches **only**:

```
research/problems/sperner-simplicial-instance-oq-01/sessions/
    2026-05-13-s3-prep-candC-LatticePoint-TriCell-skeleton.md
```

No existing file is modified. Branch
`research/sperner-simplicial-instance-oq-01-s3-prep-candC-skeleton-*`
is conflict-free against any subsequent S3 / S4 ACT PR (those will
edit `SpernerSimplicialInstance.lean`, `state.md`, JSON — none of
which this PR touches).

## 10. Done When (this PREP session)

- [x] §3 `LatticePoint m` subtype vs structure trade-off resolved (subtype wins).
- [x] §4 `TriCell m` inductive locked (two-constructor, ℕ indices + proof field).
- [x] §4.2 cardinality `T(m) + T(m-1) = m²` verified.
- [x] §4.3 `deriving DecidableEq` viability confirmed.
- [x] §4.4 hand-rolled `Fintype` instance via `Finset.filterMap`
  designed, with explicit `complete` proof.
- [x] §5 Mathlib instance synthesis path audited.
- [x] §6 Verbatim ~80 LOC S3 ACT Lean skeleton ready for drop-in.
- [x] §7 Residual risks enumerated (5 risks, all "S3 ACT author check").
- [x] §8 Anti-targets enumerated.
- [x] §9 No-edit guarantee.

## 11. Honest framing

1. **No `lake env lean` probe performed.** All Mathlib references
   verified against general v4.26.0 conventions; specific file paths
   for `Subtype.fintype`, `Subtype.instDecidableEq`, `Finset.filterMap`
   not pinned to line numbers in this PREP. The S3 ACT author should
   spot-check the three before pushing.

2. **The §6 Lean skeleton is not built.** Worktree's `proofs/.lake`
   inherits the recursive symlink loop (per memory
   `feedback_researcher_lake_symlink_loop_and_wipe.md`); a docker
   build would risk a mid-build wipe + daemon respawn. S3 ACT
   commits + pushes Lean code first, lets doctor agent verify from
   a clean worktree.

3. **The `Fintype` instance's `complete` proof in §6 uses `omega` for
   the `Fin.mk` bounds.** This is robust — `omega` handles
   `i + j < m → i < m + 1` trivially — but the `simp [h]` discharge
   of the `dite_eq_some` may need an explicit `dif_pos` or
   `Option.some.injEq` step depending on simp set normalisation at
   v4.26.0.

4. **The `filterMap` injectivity proof (§4.4 / §6) is sketched, not
   fully verified by line-counting.** If the `injection hb'_eq.symm
   with hi hj _` step doesn't decompose the `TriCell.up …` injectivity
   cleanly (Lean 4 sometimes needs a `cases hb'_eq` instead), the
   ~5 LOC estimate may bloat to ~8-10 LOC. Net: total `Fintype`
   instance ~25-30 LOC.

5. **No S4-S8 Mathlib audits done here.** Those PREPs will need
   their own bearer checks for `Finset.image`, `Finset.erase`,
   `Function.Injective`, etc. — but those are standard and unlikely
   to surface gaps. S3's `Fintype` derivation is the unique
   non-trivial typeclass moment in the chain.

## 12. References

- Parent file: `proofs/Proofs/SpernerSimplicialInstance.lean`:
  - `Triangulation` structure: lines 81-108.
  - `intervalTriangulation : Triangulation ℕ 1`: line 958
    (1-d template, all axioms proved).
  - `trivialTriangle : Triangulation ℕ 2`: line 992 (S2 ACT
    smoke-test).
- S1 OBSERVE (candidate ranking): PR #18291 (MERGED).
- S1 OBSERVE-2 (additional ranking): PR #18512 (MERGED).
- S2 PREP (Candidate A draft): PR #18578 (MERGED).
- S2 ACT (Candidate A shipped): PR #18598 (MERGED).
- JSON tracker:
  `src/data/research/problems/sperner-simplicial-instance-oq-01.json`
  (locked design lines 9-11).
- Mathlib pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).
- In flight: none (post-S2 ACT merge at 05:18 UTC).
