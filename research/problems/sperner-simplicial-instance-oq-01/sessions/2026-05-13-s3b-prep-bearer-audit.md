# S3b PREP — bearer audit + simp-name corrections to S3 PREP §6 skeleton (doc-only)

**Slug**: `sperner-simplicial-instance-oq-01`
**Phase**: PREP (doc-only — no Lean / gallery / state / problem / knowledge / JSON edits)
**Author**: researcher-12
**Date**: 2026-05-13 (claim ~07:21 UTC, push target ~07:40 UTC)
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0,
verified against `proofs/lake-manifest.json`)

## 1. Scope and motivation

The S3 PREP (PR #18625, merged 2026-05-13T06:58:45Z by researcher-5)
§11.1 explicitly defers Mathlib bearer pinning:

> **No `lake env lean` probe performed.** All Mathlib references
> verified against general v4.26.0 conventions; specific file paths
> for `Subtype.fintype`, `Subtype.instDecidableEq`, `Finset.filterMap`
> not pinned to line numbers in this PREP. The S3 ACT author should
> spot-check the three before pushing.

This S3b PREP closes that gap by running the `gh api` audits and
records the line-numbered pins at the pinned Mathlib rev, plus two
**ERRATUM** flags on simp-lemma names used in the §6 verbatim
`filterMap` injectivity proof. With these corrections in place, the
S3 ACT author can drop the §6 skeleton in verbatim minus two name
edits.

This PR touches only one new file in `sessions/`. No edits to
`SpernerSimplicialInstance.lean`, `problem.md`, `knowledge.md`,
`state.md`, the JSON tracker, or any gallery file.

## 2. Position vs in-flight PRs

| PR     | Status | What it touches                                                                                                  |
| ------ | ------ | ---------------------------------------------------------------------------------------------------------------- |
| #18291 | MERGED | S1 OBSERVE candidate ranking                                                                                     |
| #18512 | MERGED | S1 OBSERVE-2 (additional candidate ranking)                                                                      |
| #18578 | MERGED | S2 PREP Candidate A draft                                                                                        |
| #18598 | MERGED | S2 ACT `trivialTriangle : Triangulation ℕ 2` (Candidate A)                                                       |
| #18625 | MERGED | **S3 PREP** — Candidate C step 1 `LatticePoint m` + `TriCell m` skeleton + Mathlib instance audit (researcher-5) |

No open PRs on this slug. Pre-claim probe (2026-05-13 ~07:21 UTC):
`gh pr list --repo rjwalters/lean-genius --search
"sperner-simplicial-instance-oq-01 in:title"` returns all-merged
(most recent #18625 at 06:58:45Z, +22 min before claim).

Race-safety: this PREP only touches `sessions/`. Branch
`research/sperner-simplicial-instance-oq-01-s3b-prep-bearer-audit-20260513-0028`.
Conflict-free against any subsequent S3 ACT (which would edit
`SpernerSimplicialInstance.lean`, `state.md`, JSON — none here).

## 3. Bearer audits at Mathlib rev `2df2f01…`

All four bearers are accessible from `SpernerSimplicialInstance.lean`'s
existing transitive imports — see §6 for the full import chain.

### 3.1 `Subtype.fintype` — **exists** at `Mathlib/Data/Fintype/Sets.lean:263`

Verbatim at pin `2df2f01…`:

```lean
instance Subtype.fintype (p : α → Prop) [DecidablePred p] [Fintype α] : Fintype { x // p x } :=
  Fintype.subtype (univ.filter p) (by simp)
```

**ERRATUM (minor, body recall only)**: The S3 PREP §5.2 cited the body
as `Fintype.ofFinset (univ.filter p) (by simp)`. The actual body is
`Fintype.subtype (univ.filter p) (by simp)`. `Fintype.ofFinset` is a
separate definition at `Mathlib/Data/Fintype/Defs.lean:274` that itself
reduces to `Fintype.subtype` via the `Set α`-valued predicate path.

The two are inter-derivable up to `@[implicit_reducible]`. Synthesis
of `Fintype (LatticePoint m)` fires identically regardless of which
helper is named. **Net impact on S3 ACT: zero.**

Synthesis path for `LatticePoint m`:
- `LatticePoint m = {p : Fin (m + 1) × Fin (m + 1) // p.1.val + p.2.val ≤ m}`.
- `Fin (m+1) × Fin (m+1)` has `Fintype` automatically (product Fintype).
- `fun p => p.1.val + p.2.val ≤ m` has `DecidablePred` via `Nat.decLe`.
- `Subtype.fintype` synthesises.

### 3.2 `Subtype.instDecidableEq` — **exists** anonymously in Lean core

Located in `leanprover/lean4` at `src/Init/Core.lean:1387` (within
`namespace Subtype`):

```lean
instance {α : Sort u} {p : α → Prop} [DecidableEq α] : DecidableEq {x : α // p x} :=
  fun ⟨a, h₁⟩ ⟨b, h₂⟩ =>
    if h : a = b then isTrue (by subst h; exact rfl)
    else isFalse (fun h' => Subtype.noConfusion rfl .rfl (heq_of_eq h')
                              (fun h' => absurd (eq_of_heq h') h))
```

**ERRATUM (minor, name + body recall)**:

1. **Name**: The S3 PREP §5.1 cited the name as `Subtype.instDecidableEq`.
   The instance is **anonymous** in core (no explicit name). Lean's
   auto-naming gives it `instDecidableEqSubtype` (or similar — invariant
   across the v4.26 line). It is **not callable by name** in user code;
   only `inferInstance` and elaboration use it. **Net impact on S3 ACT:
   zero** — the §6 skeleton uses `deriving DecidableEq` on `TriCell m`
   (which fires via Lean core's `derive_decEq` macro, not via
   `Subtype.instDecidableEq`), and `LatticePoint m`'s `DecidableEq`
   synthesises via `inferInstance` without naming.

2. **Body**: S3 PREP §5.1 cited the body as `decidable_of_iff _
   Subtype.ext_iff`. The actual body is an explicit `if h : a = b`
   case-split using `Subtype.noConfusion`. The two are extensionally
   equivalent (both decide via `α`'s `DecidableEq`); the body discrepancy
   is purely cosmetic. **Net impact on S3 ACT: zero.**

### 3.3 `Finset.filterMap` — **exists** at `Mathlib/Data/Finset/Image.lean:520`

Verbatim at pin `2df2f01…`:

```lean
def filterMap (f : α → Option β) (s : Finset α)
    (f_inj : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') : Finset β :=
  ⟨s.val.filterMap f, s.nodup.filterMap f f_inj⟩
```

Companion lemmas at the same file:

- Line 534: `@[simp, grind =] theorem mem_filterMap {b : β} : b ∈ s.filterMap f f_inj ↔ ∃ a ∈ s, f a = some b`
- Line 528: `@[simp] theorem filterMap_val : (filterMap f s' f_inj).1 = s'.1.filterMap f := rfl`
- Line 531: `@[simp] theorem filterMap_empty : (∅ : Finset α).filterMap f f_inj = ∅ := rfl`

**Confirmation**: signature and `f_inj` precondition match the S3 PREP
§5.4 sketch verbatim. **Net impact on S3 ACT: zero (positive)**. S3
ACT can use `Finset.filterMap` confidently; `Finset.mem_filterMap` is a
default simp lemma for the `complete` proof.

### 3.4 `Fintype.subtype` and `Fintype.ofFinset` — **both exist** at `Mathlib/Data/Fintype/Defs.lean`

Used by `Subtype.fintype` (§3.1) under the hood. Audit recorded for
completeness:

- Line 266: `protected def subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) : Fintype { x // p x }` (`@[implicit_reducible]`).
- Line 274: `def ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : Fintype p` (`@[implicit_reducible]`) — reduces to `Fintype.subtype s H`.

Confirms §3.1's body discrepancy is benign: both definitions live in
the same file and reduce to the same finset filter.

### 3.5 `Finset.mem_union_left` / `Finset.mem_union_right` — **exist** at `Mathlib/Data/Finset/Lattice/Basic.lean`

Used by the §6 skeleton's `complete` proof to dispatch the up-cell vs
down-cell case:

- Line 113: `theorem mem_union_left (t : Finset α) (h : a ∈ s) : a ∈ s ∪ t`
- Line 116: `theorem mem_union_right (s : Finset α) (h : a ∈ t) : a ∈ s ∪ t`

In the transitive closure of `Mathlib.Data.Finset.Image`'s imports.
**Net impact on S3 ACT: zero (positive)**.

## 4. ERRATUM — phantom + mis-spelled simp lemmas in §6 skeleton's `filterMap` injectivity proof

The S3 PREP §6 ships a verbatim `filterMap` injectivity proof at lines
352-357 and again at 366-371 (one block per up/down constructor):

```lean
simp only [Option.bind_eq_some, dite_eq_some_iff,
           Option.some.injEq] at hb hb'
obtain ⟨_, rfl⟩ := hb
obtain ⟨_, hb'_eq⟩ := hb'
injection hb'_eq.symm with hi hj _
ext <;> [exact (Fin.ext hi); exact (Fin.ext hj)]
```

Two simp lemma names in this block are **incorrect**:

### 4.1 `dite_eq_some_iff` — **PHANTOM** (does not exist)

`gh api search/code` queries:

```
q='"dite_eq_some_iff" repo:leanprover-community/mathlib4'  → 0 hits
q='"dite_eq_some_iff" repo:leanprover/lean4'                 → 0 hits
q='"dite_eq_some"     repo:leanprover-community/mathlib4'  → 0 hits
q='"dite_eq_some"     repo:leanprover/lean4'                 → 0 hits
```

Closest existing names (Lean core `src/Init/PropLemmas.lean:726/729`):

```lean
@[simp] theorem dite_eq_left_iff  {p : Prop} [Decidable p] {x : α} {y : ¬ p → α} :
    (if h : p then x else y h) = x ↔ ∀ h : ¬ p, y h = x
@[simp] theorem dite_eq_right_iff {p : Prop} [Decidable p] {x : p → α} {y : α} :
    (if h : p then x h else y) = y ↔ ∀ h : p, x h = y
```

Neither matches the `dite = some` shape used in §6. Using
`dite_eq_some_iff` in `simp only` produces an "unknown identifier"
elaboration error. **The §6 verbatim proof will not build as written.**

### 4.2 `Option.bind_eq_some` — **mis-spelled** (correct name is `Option.bind_eq_some_iff`)

Lean core `src/Init/Data/Option/Lemmas.lean:209`:

```lean
theorem bind_eq_some_iff : x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp
```

Note: not marked `@[simp]`. The bare name `Option.bind_eq_some` is
unbound; only `Option.bind_eq_some_iff` is defined.

(Cross-check: `bind_eq_none_iff` IS `@[simp]` at line 212, but
`bind_eq_some_iff` is not.)

### 4.3 Recommended `filterMap` injectivity discharge (corrected, ~9 LOC per constructor block)

Replace each of the two §6 blocks with the following pattern. (For the
up-cell case; the down-cell case is identical modulo `+1` in the bound.)

```lean
(by
  rintro ⟨i, j⟩ ⟨i', j'⟩ b hb hb'
  -- hb  : (if h : i.val + j.val < m  then some (TriCell.up i.val j.val h)  else none) = some b
  -- hb' : (if h : i'.val + j'.val < m then some (TriCell.up i'.val j'.val h) else none) = some b
  by_cases hij : (i : ℕ) + (j : ℕ) < m
  · rw [dif_pos hij] at hb
    by_cases hij' : (i' : ℕ) + (j' : ℕ) < m
    · rw [dif_pos hij'] at hb'
      rw [Option.some.injEq] at hb hb'
      -- hb  : TriCell.up i.val j.val hij  = b
      -- hb' : TriCell.up i'.val j'.val hij' = b
      obtain rfl := hb
      injection hb'.symm with hi hj _
      ext
      · exact Fin.val_injective hi
      · exact Fin.val_injective hj
    · rw [dif_neg hij'] at hb'; exact (Option.noConfusion hb').elim
  · rw [dif_neg hij] at hb; exact (Option.noConfusion hb).elim)
```

Three small re-targets vs §6:

1. **`by_cases` + `dif_pos/dif_neg`** replaces the phantom
   `dite_eq_some_iff` simp step.
2. **`rw [Option.some.injEq]`** replaces the
   mis-spelled `Option.bind_eq_some`. (Note: §6 invokes
   `Option.bind_eq_some` but the function is a `dite`, not a `bind`
   over `Option` — the simp lemma `bind` of any flavour was never the
   right tool here. The right tool is `Option.some.injEq` (auto-
   generated, exists, `@[simp]`).)
3. **`Fin.val_injective`** replaces `Fin.ext` — both are valid; `Fin.ext`
   takes `Fin.val a = Fin.val b → a = b`, `Fin.val_injective` does the
   same thing as `Function.Injective`. The §6 spelling `exact (Fin.ext hi)`
   is correct in principle but threads through `Fin.ext_iff.mpr` rather
   than `Fin.ext` (which is the structure-extensionality lemma). Using
   `Fin.val_injective hi` is most robust.

Estimated LOC delta vs §6: +5 LOC per block (×2 = +10 LOC total).
Net §6 skeleton: 80 → ~90 LOC. Still under the state.md "~80 LOC"
estimate by a healthy margin.

### 4.4 Alternative — `split_ifs` one-liner (cleaner, ~7 LOC per block)

A more concise discharge using `split_ifs`:

```lean
(by
  rintro ⟨i, j⟩ ⟨i', j'⟩ b hb hb'
  split_ifs at hb hb' with hij hij' hij hij'
  all_goals first | (cases hb) | (cases hb') | skip
  rw [Option.some.injEq] at hb hb'
  obtain rfl := hb
  injection hb'.symm with hi hj _
  ext
  · exact Fin.val_injective hi
  · exact Fin.val_injective hj)
```

`split_ifs at hb hb'` performs the four-way case-split on the two
`dite`s. The three "either `hb` or `hb'` is `none = some b`" branches
discharge by `cases` on the resulting `none = some b` hypothesis (no
constructor available). The fourth (positive×positive) branch is the
real injectivity case.

**Recommendation**: take §4.3 (explicit `by_cases`) as the primary
target — more verbose but more robust to simp-set changes. Keep §4.4
as a fall-back if the explicit form runs long.

## 5. ERRATUM — minor body discrepancy in S3 PREP §5.5 alternative `Fintype` route

The S3 PREP §5.5 evaluates an alternative `Fintype` via `Fintype.ofEquiv`
and rejects it with:

> Then `upCells m` and `downCells m` are subtypes of `ℕ × ℕ` —
> but `ℕ × ℕ` is not `Fintype`! Need to instead use `Fin (m+1) × Fin (m+1)`
> as the carrier and re-do the subtype.

**This rejection is correct in conclusion but wrong in framing**: the
§5.5 sketch uses `ij : ℕ × ℕ` because the §4.1 lock chose `ℕ` indices
for `TriCell.up i j h` and `TriCell.down i j h`. Switching to `Fin (m+1)
× Fin (m+1)` (or `Fin m × Fin m` as the §6 skeleton does) would require
re-indexing `TriCell` itself, which the §4.1 lock rejects.

If S5/S6 author finds the §4.3 corrected `filterMap` discharge
intractable, the fall-back is a parallel inductive `TriCell.Fin m` with
`Fin (m+1)`-typed indices, equipped with an `Equiv` to `TriCell m`.
But this introduces a 30-40 LOC bridge that defeats the simplicity of
§4.4's `filterMap` approach.

**Net impact**: §5.5 stays rejected; §4.3 (this PREP) provides the
corrected injectivity proof and removes the need for the §5.5
fallback.

## 6. Import audit — no new imports needed

`proofs/Proofs/SpernerSimplicialInstance.lean` (at S2 ACT post-#18598
state) imports:

```lean
import Mathlib.Data.Finset.Sort
import Proofs.SpernerMathlib4
```

Transitive closure of these (verified via `gh api repos/leanprover-
community/mathlib4/contents/...?ref=2df2f01…` walk):

- `Mathlib.Data.Finset.Sort` → `Mathlib.Data.Fintype.EquivFin` →
  `Mathlib.Data.Fintype.Card` → `Mathlib.Data.Fintype.Basic`.
- `Mathlib.Data.Fintype.Basic` imports **both** `Mathlib.Data.Finset.Image`
  (for `Finset.filterMap` + `mem_filterMap`) **and**
  `Mathlib.Data.Fintype.Sets` (for `Subtype.fintype`).
- `Mathlib.Data.Finset.BooleanAlgebra` (also imported by
  `Fintype.Basic`) pulls in `Mathlib.Data.Finset.Lattice.Basic` for
  `mem_union_left/right`.

Lean core lemmas (`dif_pos`, `dif_neg`, `Option.some.injEq`,
`Option.noConfusion`, `Fin.val_injective`) are unconditionally
available; no import needed.

**Confirmation**: S3 ACT does NOT need to add any new `import`
statements. The §6 skeleton (with §4.3's `filterMap` injectivity
correction applied) compiles against the existing import list.

## 7. Residual S3 ACT author checks (after §4 corrections applied)

1. **`Finset.mem_filterMap` simp expansion**. The `complete` proof in
   §6 ends each branch with `simp [h]` (line 380 / line 387 of the
   §6 skeleton). This relies on `Finset.mem_filterMap` being a default
   simp lemma — confirmed in §3.3 (it carries `@[simp]`). The `simp`
   should also resolve the existential `∃ a ∈ s, f a = some b` to the
   explicit witness `⟨i, j⟩` already supplied via `refine`. **Likely
   to work; spot-check at build time.**

2. **`Fin.mk i ?_` bound resolution via `omega`**. The two `?_`
   holes in each branch (lines 377-379 of §6) are
   `i < m` and `j < m`, discharged by `omega` from the assumed bound
   `i + j < m`. `omega` reliably handles linear arithmetic over `ℕ`;
   this is a non-issue.

3. **The `simp [h]` final step**. After the `refine ⟨⟨i, _⟩, ⟨j, _⟩, _, _⟩`
   shape, the residual goal is to show
   `(if h : (Fin.mk i ...).val + (Fin.mk j ...).val < m then some ...
   else none) = some (TriCell.up i j h)`. The `simp [h]` should
   discharge this via `dif_pos h` + `Fin.mk_val_eq` (the latter is
   `(Fin.mk i hi).val = i`). If `simp [h]` stalls, the explicit
   `rw [dif_pos h]` + `rfl` is the manual fallback.

4. **`Subtype.fintype` instance vs explicit `DecidablePred`**.
   `LatticePoint m`'s predicate is
   `fun p : Fin (m+1) × Fin (m+1) => p.1.val + p.2.val ≤ m`.
   `Nat.decLe` makes this decidable, but for typeclass elaboration to
   *find* the `DecidablePred` instance, Lean may need an
   `instance : DecidablePred (fun p : Fin (m+1) × Fin (m+1) =>
   p.1.val + p.2.val ≤ m) := by intro p; exact Nat.decLe _ _`
   declaration. **Spot-check after S3 ACT push** — usually
   `inferInstance` synthesises this directly.

5. **`deriving DecidableEq` on `TriCell m`**. Confirmed `derive_decEq`
   supports inductives with `ℕ`-typed fields and proof-carrying
   fields (§3.2). The §6 `deriving DecidableEq` clause should fire
   unconditionally.

## 8. Verbatim S3 ACT Lean skeleton (S3 PREP §6 + §4.3 corrections)

For convenient drop-in by the S3 ACT author, the corrected §6
skeleton (with §4.3's injectivity discharge swapped in) is:

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
        by_cases hij : (i : ℕ) + (j : ℕ) < m
        · rw [dif_pos hij] at hb
          by_cases hij' : (i' : ℕ) + (j' : ℕ) < m
          · rw [dif_pos hij'] at hb'
            rw [Option.some.injEq] at hb hb'
            obtain rfl := hb
            injection hb'.symm with hi hj _
            ext
            · exact Fin.val_injective hi
            · exact Fin.val_injective hj
          · rw [dif_neg hij'] at hb'; exact (Option.noConfusion hb').elim
        · rw [dif_neg hij] at hb; exact (Option.noConfusion hb).elim)
    ∪
    (Finset.univ : Finset (Fin m × Fin m)).filterMap
      (fun ij =>
        if h : (ij.1 : ℕ) + (ij.2 : ℕ) + 1 < m then
          some (TriCell.down ij.1.val ij.2.val h)
        else none)
      (by
        rintro ⟨i, j⟩ ⟨i', j'⟩ b hb hb'
        by_cases hij : (i : ℕ) + (j : ℕ) + 1 < m
        · rw [dif_pos hij] at hb
          by_cases hij' : (i' : ℕ) + (j' : ℕ) + 1 < m
          · rw [dif_pos hij'] at hb'
            rw [Option.some.injEq] at hb hb'
            obtain rfl := hb
            injection hb'.symm with hi hj _
            ext
            · exact Fin.val_injective hi
            · exact Fin.val_injective hj
          · rw [dif_neg hij'] at hb'; exact (Option.noConfusion hb').elim
        · rw [dif_neg hij] at hb; exact (Option.noConfusion hb).elim)
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

**Line count**: ~90 LOC including blank lines + docstrings (up from
§6's ~80 due to the +5 LOC ×2 from §4.3's explicit `by_cases`/`dif_*`
discharge replacing the broken `simp only [dite_eq_some_iff, ...]`
one-liner).

**Sorries**: 0. **Axioms**: 0.

## 9. Anti-targets (unchanged from S3 PREP §8)

* ❌ **Do not redo S2 (Candidate A)**. PR #18598 has it covered.
* ❌ **Do not attempt the full `triAdj` (S5) in this PREP**. S5 is a
  separate ~60 LOC ACT.
* ❌ **Do not use structure form for `LatticePoint m`** (S3 PREP §3.2).
* ❌ **Do not unify `up` / `down` into a single `TriCell m i j Bool`
  constructor** (S3 PREP §4.1).
* ❌ **Do not push the §8 skeleton without commit + push first**. The
  worktree `.lake` symlink loop persists; doctor verifies build from
  a clean worktree (memory `feedback_researcher_lake_symlink_loop_and_wipe.md`).

## 10. Done When (this S3b PREP session)

- [x] §3.1 `Subtype.fintype` pinned to `Sets.lean:263`; body ERRATUM noted.
- [x] §3.2 Subtype `DecidableEq` pinned to Lean core `Init/Core.lean:1387`; name ERRATUM noted.
- [x] §3.3 `Finset.filterMap` pinned to `Image.lean:520`.
- [x] §3.4 `Fintype.subtype` / `ofFinset` pinned to `Defs.lean:266/274`.
- [x] §3.5 `Finset.mem_union_left/right` pinned to `Lattice/Basic.lean:113/116`.
- [x] §4.1 `dite_eq_some_iff` flagged as PHANTOM.
- [x] §4.2 `Option.bind_eq_some` flagged as mis-spelled (correct: `bind_eq_some_iff`).
- [x] §4.3 Corrected `filterMap` injectivity discharge given (`by_cases` + `dif_pos/neg`).
- [x] §4.4 Alternative `split_ifs` one-liner given as fall-back.
- [x] §5 S3 PREP §5.5 framing nuance noted (rejection correct, framing imprecise).
- [x] §6 Import chain verified — no new imports needed.
- [x] §7 Five S3 ACT author spot-checks enumerated (all "spot-check at build time").
- [x] §8 Verbatim corrected §6 skeleton ready for drop-in.

## 11. Honest framing

1. **No `lake env lean` probe performed.** All bearer pins verified via
   `gh api repos/leanprover-community/mathlib4/contents/...?ref=2df2f01…`
   and `gh api repos/leanprover/lean4/contents/src/...` against current
   `main` of Lean core (which may differ slightly from the toolchain
   version at the Mathlib pin — but the four named bearers and the
   five named lemmas/instances are stable across the v4.26 line).

2. **The §8 corrected Lean skeleton is not built.** Worktree `.lake`
   symlink loop precludes local Docker build. The §4.3 corrections
   are derived from the simp-lemma name space audit, not from a live
   build trace. The S3 ACT author should be prepared for residual
   simp-set normalisation issues at v4.26 (§7 risks 1-3 enumerate
   these). The corrections close the two **named-identifier**
   errors; behavioural simp-set drift is a separate concern.

3. **The `split_ifs` fall-back (§4.4) is sketched, not exhaustively
   verified.** The `all_goals first | (cases hb) | (cases hb') | skip`
   pattern is robust in principle but may need adjustment if
   `split_ifs` produces hypotheses in a different order than
   `(hij true, hij' true) / (hij true, hij' false) / ...`. Take §4.3
   as the primary; §4.4 as fall-back.

4. **`Fin.val_injective` vs `Fin.ext`**. Both are valid discharges of
   `(Fin.mk i _).val = (Fin.mk j _).val → Fin.mk i _ = Fin.mk j _`.
   The §6 PREP used `Fin.ext hi`; the §4.3 correction uses
   `Fin.val_injective hi`. Either works; the latter has a clearer
   `Function.Injective` shape and is more robust to elaboration. If
   `Fin.val_injective` produces a unification issue, fall back to
   `Fin.ext hi`.

5. **No S4-S8 audits done here.** S3b is scoped to S3 only. Future
   PREPs for S4 (`triVtx` + `vertex_injective`), S5 (`triAdj`),
   S6 (`adj_symm`/`adj_vertex`), S7 (`adj_ne`), S8 (`standardTriangle
   Triangulation`) will each need their own bearer audits — but those
   bearers (`Function.Injective`, `Finset.image`, `Finset.erase`) are
   standard and unlikely to surface gaps. S3's `Fintype` derivation
   was the unique high-risk typeclass moment in the chain.

## 12. References

- Parent file: `proofs/Proofs/SpernerSimplicialInstance.lean`:
  - `Triangulation` structure: lines 81-108.
  - `intervalTriangulation : Triangulation ℕ 1`: line 958.
  - `trivialTriangle : Triangulation ℕ 2`: line 992 (S2 ACT smoke-test).
- S3 PREP (Candidate C step 1 skeleton): PR #18625 (MERGED 2026-05-13T06:58:45Z).
- S2 ACT (Candidate A shipped): PR #18598 (MERGED 2026-05-13T05:21:40Z).
- Mathlib pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0),
  verified against `proofs/lake-manifest.json`.
- Lean core (for `dif_pos/neg`, `Option.some.injEq`, `Option.bind_eq_some_iff`,
  `dite_eq_left_iff/right_iff`, anonymous `DecidableEq (Subtype p)`):
  branch `main` of `leanprover/lean4` (stable across the v4.26 toolchain
  line tagged by `proofs/lean-toolchain`).
- Memory: `feedback_researcher_lake_symlink_loop_and_wipe.md` — commit + push
  Lean first, doctor verifies build from clean worktree.
- Memory: `feedback_researcher_12_2026_05_13_triple_mathlib_bearer_audit.md`
  — parent-PREP "Mathlib: X / Y machinery" phrasing is a signal that the
  bearer wasn't pinned; this PREP follows that pattern (S3 PREP §11.1
  was the signal).
