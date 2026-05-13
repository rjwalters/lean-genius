# S2 PREP-5 — Typeclass-instance bridge + deferred API audit for Candidate B5 (doc-only)

**Author:** researcher-12
**Timestamp:** 2026-05-13 ~09:55 UTC
**Phase:** S2 PREP-5 (doc-only Mathlib API audit; closes PREP-4 §11 caveats + 1 new finding)
**Iteration:** 6-prep
**Builds on:**
- S1 OBSERVE — PR #18285 (merged), three candidates A/B/C
- S1b OBSERVE — PR #18359 (merged), audit correction (C is moot)
- S2 PREP — PR #18453 (merged), Candidate A* 5-substep decomposition
- S2 PREP-2 — PR #18493 (merged), Candidate B 5-substep decomposition + "Mathlib one-shot"
- S2 PREP-3 — PR #18546 (merged), `frattini_profinite` degeneracy audit
- S2 PREP-4 — PR #18658 (merged), Mathlib bearer audit (PHANTOM `closedSubgroup_eq_sInf_open`)

**Mathlib pin:** v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), confirmed via `proofs/lake-manifest.json`.

## 0. Why this angle now

PREP-4 §11 ("Honesty / what could be wrong") explicitly defers three
API signature questions to the S2 ACT picker:

> - **`nhds_basis_clopen`** (§4 proposed B5 replacement) is mentioned in
>   `ClopenNhdofOne.lean:48` and should live in
>   `Mathlib/Topology/Separation/Profinite.lean`, but its **exact signature**
>   has not been verified in this audit.
> - **`isClosed_singleton.isOpen_compl`** in §4 — `IsClosed.isOpen_compl`
>   is the standard combinator; should typecheck without issue but
>   unverified for this exact use site.
> - **`Filter.HasBasis.mem_iff'`** usage in §4 — copied from
>   `ClopenNhdofOne.lean:48`; the form should be reusable but exact
>   signature variation under v4.26.0 not separately verified.

This memo verifies all three at the pinned commit AND adds a fourth
finding PREP-4 missed: the typeclass-instance bridge from
`hpf : IsProfiniteGroup G` (a Prop-valued bundled structure with five
explicit fields) to the Mathlib `[IsTopologicalGroup G]` typeclass
required by `IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one`
(the one bearer in `ClopenNhdofOne.lean` that survived PREP-4's phantom
finding).

**Strict orthogonality.** Writes one new `sessions/` file. No edits to
`problem.md`, `state.md`, `knowledge.md`,
`src/data/research/problems/sylow-theorems-oq-03.json`, any prior
session file, or any Lean file. No build. No edits to the parent file
`proofs/Proofs/SylowTheoremOQ02.lean`. No race window: 0 open PRs on
slug at push time.

## 1. Findings summary

| # | Severity | Claim (PREP-4 §4) | Reality at v4.26.0 | Impact on B5 |
|---|----------|-------------------|--------------------|--------------|
| I | **GAP (new)** | (Not addressed by PREP-4) — chain assumes `IsTopologicalGroup G` is in scope | `IsTopologicalGroup` is a `class extends ContinuousMul, ContinuousInv` with **no own fields** but **no auto-synthesis** instance from `[ContinuousMul] + [ContinuousInv]` | **Add 1 LOC**: `haveI : IsTopologicalGroup G := { }` after the existing `ContinuousMul`/`ContinuousInv` haveI's |
| II | **MINOR API SHAPE FIX** | `(nhds_basis_clopen (1 : G)).mem_iff'.mp ...` (no explicit `t` arg) | `mem_iff'` is a **structure field** with explicit `t : Set α` arg; theorem `mem_iff` (no prime) is the curried/implicit form. PREP-4 §4 omitted the `t`. | **Replace `.mem_iff'.mp`** with `.mem_iff.mp` (theorem with implicit `t`). +0 LOC. |
| III | **CONFIRMED** | `nhds_basis_clopen` exists in `Mathlib/Topology/Separation/Profinite.lean` | Exists at line **45**: `theorem nhds_basis_clopen (x : X) : (𝓝 x).HasBasis (fun s : Set X => x ∈ s ∧ IsClopen s) id`. Variable section `[T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]`. | None operational; bearer + signature verified |
| IV | **CONFIRMED** | `IsClosed.isOpen_compl` exists | Exists as **structure field** of `IsClosed` class at `Mathlib/Topology/Defs/Basic.lean:104`: `class IsClosed (s : Set X) : Prop where isOpen_compl : IsOpen sᶜ`. PREP-4 §4's dot-notation `isClosed_singleton.isOpen_compl` typechecks. | None operational |
| V | **CONFIRMED with extra typeclass** | `isClosed_singleton` requires `[T1Space X]` | Confirmed at `Mathlib/Topology/Separation/Basic.lean:341`: `theorem isClosed_singleton [T1Space X] {x : X} : IsClosed ({x} : Set X)`. **`T2Space → T1Space` is a Mathlib `instance (priority := 100)` at `Mathlib/Topology/Separation/Hausdorff.lean:115`**, so `haveI := hpf.isT2` makes `T1Space` synthesizable transitively. | +0 LOC; transitive synthesis suffices |

**Net.** 1 new gap (Finding I — typeclass bridge), 1 minor shape fix
(Finding II — `mem_iff'` arg), 3 confirmations (III, IV, V). Finding
**I** is the only one that adds a new LOC requirement (1 LOC). Finding
**II** corrects the proof script but doesn't change the LOC budget.

## 2. Finding I in detail — `IsTopologicalGroup` typeclass synthesis

### 2.1 Class definition

`Mathlib/Topology/Algebra/Group/Defs.lean:110-111`:

```lean
@[to_additive]
class IsTopologicalGroup (G : Type*) [TopologicalSpace G] [Group G] : Prop
    extends ContinuousMul G, ContinuousInv G
```

In Lean 4 Mathlib idiom, `class extends ...` with no `where ... :=`
clauses defines a **conjunction class**: an `IsTopologicalGroup G`
instance is morally `⟨inferInstance, inferInstance⟩` from
`[ContinuousMul G] + [ContinuousInv G]`. **However**, this synthesis
is **not automatic**: there is no Mathlib-side
`instance [ContinuousMul G] [ContinuousInv G] : IsTopologicalGroup G`
declaration that would let typeclass inference auto-build one from the
two parents.

Searching Mathlib at the pinned commit:

```bash
gh api -X GET 'search/code' -f q='instance.*IsTopologicalGroup.*ContinuousMul.*ContinuousInv repo:leanprover-community/mathlib4'
```

returns no hit matching the auto-build pattern. Direct read of
`Mathlib/Topology/Algebra/Group/Basic.lean` shows 6 specific
`IsTopologicalGroup` instances:

| Line | Instance | Source typeclass requirements |
|------|----------|-------------------------------|
| 397  | `instance : IsTopologicalGroup (ULift G)` | `[IsTopologicalGroup G]` |
| 488  | `Prod.instIsTopologicalGroup` | `[IsTopologicalGroup G] [IsTopologicalGroup H]` |
| 493  | `OrderDual.instIsTopologicalGroup` | `[IsTopologicalGroup G]` |
| 508  | `instance ... : IsTopologicalGroup αᵐᵒᵖ` | `[IsTopologicalGroup α]` |
| 559  | `instance (S : Subgroup G) : IsTopologicalGroup S` | `[IsTopologicalGroup G]` |
| 1200 | `instance [ContinuousMul α] : IsTopologicalGroup αˣ` | `[ContinuousMul α]` only (units) |

None of these synthesizes `IsTopologicalGroup G` from `[ContinuousMul G] + [ContinuousInv G]` for arbitrary `G`. The
`of_nhds_one` constructor at line 832 is `theorem` (not `instance`)
and requires `Tendsto`-based hypotheses, not `Continuous`-based.

### 2.2 The bridge OQ-02 already establishes (and where B5 needs more)

`proofs/Proofs/SylowTheoremOQ02.lean:208-209` establishes:

```lean
haveI : ContinuousMul G := ⟨hpf.continuous_mul⟩
haveI : ContinuousInv G := ⟨hpf.continuous_inv⟩
```

This is sufficient for `isClosed_conj_map` (lines 205-223) and
`isProP_conj_map` (lines 226-254) because those proofs only use the
`ContinuousMul` / `ContinuousInv` typeclasses to build `Continuous`
combinators (`continuous_mul_right`, `continuous_mul_left`) — they
never call a lemma whose signature requires `[IsTopologicalGroup G]`.

The bearer `IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one`
in `Mathlib/Topology/Algebra/ClopenNhdofOne.lean:27` (verbatim from
PREP-4 §5) reads:

```lean
theorem exist_openNormalSubgroup_sub_clopen_nhds_of_one {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    ∃ H : OpenNormalSubgroup G, (H : Set G) ⊆ W := by
  ...
```

It demands `[IsTopologicalGroup G] [CompactSpace G]` — both as
typeclass instances. PREP-4 §4 inherits PREP-2's pattern and writes
implicit `haveI := hpf.isT2`, `haveI := hpf.isTotallyDisc`, `haveI := hpf.isCompact` — but **omits the IsTopologicalGroup haveI**, which
typeclass inference cannot synthesize automatically from
`ContinuousMul + ContinuousInv` alone.

### 2.3 The 1-LOC fix

In B5 (and any other call to a bearer requiring
`[IsTopologicalGroup G]`), add **after** the existing `ContinuousMul`
/ `ContinuousInv` haveI's:

```lean
haveI : ContinuousMul G := ⟨hpf.continuous_mul⟩
haveI : ContinuousInv G := ⟨hpf.continuous_inv⟩
haveI : IsTopologicalGroup G := { }  -- ← NEW: 1 LOC
```

The anonymous `{ }` syntax constructs the no-own-fields class from the
two parents in scope. Equivalent forms:
- `haveI : IsTopologicalGroup G := ⟨⟩` (anonymous constructor; works
  because `class extends` synthesizes the `mk` field for the parent
  bundle)
- `haveI : IsTopologicalGroup G := IsTopologicalGroup.mk` (named, but
  `mk` may be auto-generated and unstable across Mathlib versions)

Recommended: `{ }` for clarity and stability across Lean 4 minor
versions.

### 2.4 Why PREP-4 missed this

PREP-4 §4's proposed B5 sketch focused on the **set-of-clopen-bases**
machinery (`nhds_basis_clopen`) and the **separation** machinery
(`isClosed_singleton.isOpen_compl`) — both of which only need
`[T2Space G] [CompactSpace G] [TotallyDisconnectedSpace G]`, all
established via `haveI := hpf.isT2/isCompact/isTotallyDisc`.

The follow-up call to `IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one`
(PREP-4 §4 line 138 in the corrected sketch) is the first place a
**topological-group**-flavored bearer is invoked, but PREP-4 §4 wrote
that line without re-checking the typeclass requirements of the
called function. This is a reasonable omission — the bearer name does
contain `Topological` but not `Group` — but it's a real LOC delta the
S2 ACT picker must add.

## 3. Finding II in detail — `Filter.HasBasis.mem_iff'` vs `.mem_iff`

### 3.1 Structure definition

`Mathlib/Order/Filter/Bases/Basic.lean:209-211`:

```lean
structure HasBasis (l : Filter α) (p : ι → Prop) (s : ι → Set α) : Prop where
  mem_iff' : ∀ t : Set α, t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t
```

`mem_iff'` is the **structure field** — a function taking explicit
`t : Set α`, returning the iff. The unprimed alias is at line 219:

```lean
theorem HasBasis.mem_iff (hl : l.HasBasis p s) : t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t :=
  hl.mem_iff' t
```

`HasBasis.mem_iff` curries away the explicit `t` (it becomes implicit
because the goal's `t` lets Lean elaborate it).

### 3.2 PREP-4 §4's usage

PREP-4 §4 line 247:

```lean
rcases (nhds_basis_clopen (1 : G)).mem_iff'.mp (hxc_open.mem_nhds h1_in_xc) with ⟨W, hW_clopen, hW_sub⟩
```

This **does not typecheck**: `(...).mem_iff'` is a function of type
`∀ t, t ∈ l ↔ ...`, so `.mp` cannot be applied directly without first
specializing `t`. The correct forms:

```lean
-- Form A (theorem, implicit t — recommended for brevity):
rcases (nhds_basis_clopen (1 : G)).mem_iff.mp (hxc_open.mem_nhds h1_in_xc)
  with ⟨W, hW_clopen, hW_sub⟩

-- Form B (structure field, explicit t — pre-existing usage in OQ-02-adjacent ClopenNhdofOne.lean:48):
rcases (Filter.HasBasis.mem_iff' (nhds_basis_clopen (1 : G)) ({x}ᶜ)).mp
  (hxc_open.mem_nhds h1_in_xc)
  with ⟨W, hW_clopen, hW_sub⟩
```

Form A is closer to PREP-4 §4's intent (1 LOC, implicit `t` flow).
Form B is closer to the existing Mathlib pattern in
`ClopenNhdofOne.lean:48` (3 LOC across 3 lines, explicit `U`/`{x}ᶜ`).

### 3.3 Existing `ClopenNhdofOne.lean:48` usage as reference

PREP-4 §5 reproduced line 48 of `ClopenNhdofOne.lean` (as part of the
verbatim file paste):

```lean
rcases ((Filter.HasBasis.mem_iff' ((nhds_basis_clopen (1 : G))) U).mp <|
    mem_nhds_iff.mpr (by use U)) with ⟨W, hW, h⟩
```

This uses **Form B** (explicit `U` arg to `.mem_iff'`). It also nests
`<|` inside `(...).mp` to apply `mem_nhds_iff.mpr` first. The style is
Mathlib-canonical for this lemma.

**Recommendation for B5.** Use **Form A** (`.mem_iff.mp`) for the
new code path; it's more readable and consistent with the rest of the
profinite-group proofs OQ-02 already contains.

### 3.4 Note on the unpacking pattern

`(nhds_basis_clopen x).mem_iff` returns `t ∈ 𝓝 x ↔ ∃ s, (x ∈ s ∧ IsClopen s) ∧ s ⊆ t`.
Note the **nested conjunction in the predicate `p`**: `(x ∈ s ∧ IsClopen s)` is
**one argument** to the existential, then `s ⊆ t` is conjoined separately. So the
`rcases` pattern is `⟨W, ⟨h1W, hW_clopen⟩, hW_sub⟩` — a 3-deep nesting, **not**
PREP-4 §4's flat `⟨W, hW_clopen, hW_sub⟩`. Corrected pattern:

```lean
rcases (nhds_basis_clopen (1 : G)).mem_iff.mp (hxc_open.mem_nhds h1_in_xc)
  with ⟨W, ⟨h1W, hW_clopen⟩, hW_sub⟩
```

This is a **second sub-correction** to PREP-4 §4: the rcases pattern
must reflect the basis predicate's actual structure
`(fun s => x ∈ s ∧ IsClopen s)`, not a flat 3-tuple.

## 4. Findings III–V (confirmations) — verification records

### 4.1 Finding III: `nhds_basis_clopen` signature

`Mathlib/Topology/Separation/Profinite.lean:43-45`:

```lean
variable [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]

theorem nhds_basis_clopen (x : X) : (𝓝 x).HasBasis (fun s : Set X => x ∈ s ∧ IsClopen s) id :=
  ⟨fun U => by ...⟩
```

The `variable` line establishes the typeclass requirements. The basis
indexing function is `id` (sets are indexed by themselves), and the
predicate is `fun s => x ∈ s ∧ IsClopen s`. So unpacking gives sets
`W` with `(x ∈ W ∧ IsClopen W) ∧ W ⊆ U`.

### 4.2 Finding IV: `IsClosed.isOpen_compl`

`Mathlib/Topology/Defs/Basic.lean:102-105`:

```lean
/-- A set is closed if its complement is open -/
class IsClosed (s : Set X) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ
```

This is the **class definition itself**: `IsClosed s` is a single-field
typeclass whose field is `isOpen_compl : IsOpen sᶜ`. Dot notation
`(h : IsClosed s).isOpen_compl` projects the field, returning
`IsOpen sᶜ`.

So `isClosed_singleton.isOpen_compl : IsOpen ({x}ᶜ)` typechecks
provided the ambient `[T1Space G]` is in scope (Finding V).

### 4.3 Finding V: `isClosed_singleton` typeclass requirement

`Mathlib/Topology/Separation/Basic.lean:341`:

```lean
theorem isClosed_singleton [T1Space X] {x : X} : IsClosed ({x} : Set X) :=
  T1Space.t1 x
```

Requires `[T1Space X]`. The `T2Space → T1Space` lift is at
`Mathlib/Topology/Separation/Hausdorff.lean:115`:

```lean
instance (priority := 100) T2Space.t1Space [T2Space X] : T1Space X :=
  ...
```

So in B5, after `haveI := hpf.isT2`, both `[T1Space G]` and
`[T2Space G]` are synthesizable; `isClosed_singleton` resolves
without further haveI's.

## 5. Corrected B5 sketch (~22 LOC, addresses Findings I + II)

Combining all five findings, the corrected B5 sketch is:

```lean
-- Auxiliary: clopen-separation lemma (drop-in for B5's first half)
lemma x_ne_one_separated_by_clopen
    (hpf : IsProfiniteGroup G) (x : G) (hx : x ≠ 1) :
    ∃ W : Set G, IsClopen W ∧ (1 : G) ∈ W ∧ x ∉ W := by
  haveI := hpf.isT2                                         -- T2 → T1 transitively
  haveI := hpf.isTotallyDisc
  haveI := hpf.isCompact
  -- {x}ᶜ is open since {x} is closed in T1
  have hxc_open : IsOpen ({x}ᶜ : Set G) := isClosed_singleton.isOpen_compl
  have h1_in_xc : (1 : G) ∈ ({x}ᶜ : Set G) := by simpa using hx.symm
  -- nhds_basis_clopen gives a clopen W ⊆ {x}ᶜ with 1 ∈ W
  rcases (nhds_basis_clopen (1 : G)).mem_iff.mp (hxc_open.mem_nhds h1_in_xc)
    with ⟨W, ⟨h1W, hW_clopen⟩, hW_sub⟩
  refine ⟨W, hW_clopen, h1W, ?_⟩
  intro hxW
  exact hW_sub hxW rfl
```

(LOC count: 9 inside the `by` block + 4 lines of signature = 13; plus
namespace + variables + 1 blank ≈ ~16-20 LOC depending on file
context.)

The B5 main step then becomes:

```lean
lemma sInter_openNormal_eq_one
    (hpf : IsProfiniteGroup G) (x : G)
    (hx_in_all : ∀ H : OpenNormalSubgroup G, x ∈ H.toSubgroup) :
    x = 1 := by
  by_contra hx
  -- Get clopen W with 1 ∈ W, x ∉ W
  obtain ⟨W, hW_clopen, h1W, hxW⟩ := x_ne_one_separated_by_clopen hpf x hx
  -- Establish IsTopologicalGroup G needed by exist_openNormalSubgroup_sub_clopen_nhds_of_one
  haveI : ContinuousMul G := ⟨hpf.continuous_mul⟩
  haveI : ContinuousInv G := ⟨hpf.continuous_inv⟩
  haveI : IsTopologicalGroup G := { }                       -- ← Finding I: 1 LOC
  haveI := hpf.isCompact                                    -- needed for the bearer
  -- Get an open normal H ⊆ W
  obtain ⟨H, hH⟩ :=
    IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one hW_clopen h1W
  -- x ∈ H by hypothesis, but H ⊆ W, contradicting x ∉ W
  exact hxW (hH (hx_in_all H))
```

(LOC count: 8 inside the `by` block + 4 lines of signature = 12; plus
namespace overhead ≈ ~14-16 LOC.)

**Total B5 (separator + main step): ~30-35 LOC** (vs. PREP-4 §4's
optimistic ~28 LOC; vs. PREP-2's phantom-dependent ~10 LOC). The +5
LOC delta over PREP-4 comes from:
- +1 LOC for `IsTopologicalGroup G := { }` (Finding I)
- +0 LOC for `mem_iff` vs `mem_iff'` (just a syntax change)
- +2-3 LOC for the corrected rcases pattern with nested predicate
  unpacking (Finding II §3.4)
- +1-2 LOC for explicit `haveI := hpf.isCompact` (PREP-4 had it but
  the bearer also requires it; small bookkeeping)

This is **not a blocker**, just a correction to the LOC budget. **Net Candidate B total: ~50-55 LOC** (matching S1b's original ~60 LOC
estimate, slightly tighter due to PREP-4's `nhds_basis_clopen` insight).

## 6. Verification cross-check table

| Claim | Source PREP | Method | Result |
|-------|-------------|--------|--------|
| `IsTopologicalGroup` is a `class extends ContinuousMul, ContinuousInv` with no own fields | (this audit, Finding I) | Contents API on `Mathlib/Topology/Algebra/Group/Defs.lean:110-111` | Confirmed: 2 lines, no `where` body |
| No `instance [ContinuousMul] [ContinuousInv] : IsTopologicalGroup` exists in Mathlib at the pin | (this audit, Finding I) | search/code + read of `Group/Basic.lean` | Confirmed: 6 specific instances at lines 397/488/493/508/559/1200, none synthesizing from `ContinuousMul + ContinuousInv` for arbitrary `G` |
| `Filter.HasBasis.mem_iff'` is a structure field with explicit `t : Set α` | PREP-4 §4 (#18658) | Contents API on `Mathlib/Order/Filter/Bases/Basic.lean:211` | Confirmed: `mem_iff' : ∀ t : Set α, t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t` |
| `Filter.HasBasis.mem_iff` is a theorem with implicit `t` (curried wrapper) | (this audit, Finding II) | Contents API on `Mathlib/Order/Filter/Bases/Basic.lean:219-220` | Confirmed: `theorem HasBasis.mem_iff (hl : l.HasBasis p s) : t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t := hl.mem_iff' t` |
| `nhds_basis_clopen` exists in `Mathlib/Topology/Separation/Profinite.lean` | PREP-4 §4 (#18658) | Contents API | Confirmed at line **45**; signature `(𝓝 x).HasBasis (fun s : Set X => x ∈ s ∧ IsClopen s) id` |
| `nhds_basis_clopen` requires `[T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]` | (this audit, Finding III §4.1) | Contents API line 43 (variable section) | Confirmed |
| `IsClosed.isOpen_compl` is structure field of `IsClosed` class | PREP-4 §4 (#18658) | Contents API on `Mathlib/Topology/Defs/Basic.lean:102-105` | Confirmed: class definition itself |
| `isClosed_singleton` requires `[T1Space X]` | (this audit, Finding V) | Contents API on `Mathlib/Topology/Separation/Basic.lean:341` | Confirmed: `theorem isClosed_singleton [T1Space X] {x : X} : IsClosed ({x} : Set X)` |
| `T2Space → T1Space` is a Mathlib instance (priority := 100) | (this audit, Finding V) | Contents API on `Mathlib/Topology/Separation/Hausdorff.lean:115` | Confirmed |
| `IsOpen.mem_nhds` exists | PREP-4 §4 (#18658, used `hxc_open.mem_nhds h1_in_xc`) | Contents API on `Mathlib/Topology/Neighborhoods.lean:90` | Confirmed: `IsOpen.mem_nhds (hs : IsOpen s) (hx : x ∈ s) : s ∈ 𝓝 x` |
| Basis predicate `(fun s => x ∈ s ∧ IsClopen s)` requires nested rcases pattern | (this audit, Finding II §3.4) | Direct read of basis predicate in `nhds_basis_clopen` definition | Confirmed: pattern is `⟨W, ⟨h1W, hW_clopen⟩, hW_sub⟩` not flat `⟨W, hW_clopen, hW_sub⟩` |

## 7. Net effect on Candidate B LOC budget

| Component | PREP-2 (#18493) | PREP-4 (#18658) | This PREP-5 | Reason |
|-----------|------------------|------------------|-------------|--------|
| B1 (intersection unpacking) | 5 | 5 | 5 | Unchanged |
| B2 (image to G/N is p ∩ q-group) | 8 | 8 | 8 | Unchanged |
| B3 (coprime ⇒ trivial in G/N) | 12 | 12 | 12 | Unchanged |
| B4 (lift to ⋂ open normal) | 4 | 4 | 4 | Unchanged |
| B5 (⋂ open normal = ⊥) | ~10 (phantom-dependent) | ~20-25 (nhds_basis_clopen route) | **~30-35** | +5-10 from Finding I (typeclass haveI), Finding II (rcases pattern + arg fix) |
| **Total** | **~25** | **~50** | **~55-60** | Matches S1b's pre-PREP estimate of ~60 LOC |

The S2 ACT picker for Candidate B should plan **~55-60 LOC**, not
PREP-2's ~25 or PREP-4's ~50. The overrun against PREP-4 is small
(+5-10 LOC) but real; budgeting for it avoids mid-build surprise.

**Candidate A\* and `frattini_profinite_trivial` are unaffected** by
findings I–V; their LOC budgets per PREP and PREP-3 stand.

## 8. Anti-targets (what this PREP explicitly does NOT do)

1. **No** edits to `proofs/Proofs/SylowTheoremOQ02.lean` (parent file).
2. **No** creation of `proofs/Proofs/SylowTheoremOQ03.lean` (no Lean
   code ships).
3. **No** edits to `problem.md`, `state.md`, `knowledge.md`, or the
   gallery JSON.
4. **No** edits to prior session files (PREPs 1-4 stand as-merged;
   their LOC estimates and proof sketches are corrected via this
   advisory note, not via rewriting their text).
5. **No** Docker build attempt. The corrected B5 sketch in §5 is
   marked unverified; it is intended as a starting point for the S2
   ACT picker, not a typechecked proof.
6. **No** re-claim or status update on this slug beyond the standard
   `release` after PR push.
7. **No** sibling-slug edits (OQ-02 / OQ-04 / OQ-05 not touched).
8. **No** new ACT candidate proposed beyond A/A\*/B/D (S1b's
   shortlist as refined by PREP-4 stands; C remains moot per S1b).
9. **No** edit to `src/data/research/problems/sylow-theorems-oq-03.json`
   (gallery sync deferred to S2 ACT or a later S1c if needed).

## 9. Honesty / what could be wrong

- **`{ }` constructor for `IsTopologicalGroup G`** (Finding I §2.3) —
  in Lean 4, `class extends` with no `where`-body should accept `{ }`
  to construct the no-own-fields class from the parents-in-scope. If
  Lean 4 elaboration changes the rule (it has been stable since 4.0
  but is not formally guaranteed), the workaround is `⟨⟩` (anonymous
  constructor) or an explicit field-value form. Both are documented
  Lean 4 idioms; the construction itself is mathematically trivial
  (no fields to provide). Verification deferred to S2 ACT-time
  Docker build.
- **The corrected rcases pattern** (Finding II §3.4) assumes Lean's
  unpacking matches the basis predicate's literal structure
  `(fun s => x ∈ s ∧ IsClopen s)`. If Mathlib pretty-printer or a
  `simp`-normalization re-associates the conjunction, the flat
  `⟨W, hW_clopen, hW_sub⟩` PREP-4 wrote may also typecheck (Lean's
  anonymous-constructor support for `And` is permissive). The nested
  pattern is the safer bet; both should compile.
- **Corrected B5 sketch (§5)** is not Lean-checked. The two helper
  lemmas (`x_ne_one_separated_by_clopen` and `sInter_openNormal_eq_one`)
  are sketches; `simpa using hx.symm` may need `Set.mem_compl_iff` or
  `Set.mem_singleton_iff` rewriting depending on the goal-state form
  Lean produces. The S2 ACT picker should expect 1-3 small
  `simp`-style adjustments per helper.
- **`OpenNormalSubgroup.toSubgroup` coercion** in B5 — the bearer
  returns `H : OpenNormalSubgroup G`; B5 needs `x ∈ H.toSubgroup` (or
  `(H : Set G)` set-membership). The `hx_in_all` hypothesis statement
  uses `H.toSubgroup`; consistent with the `OpenNormalSubgroup`
  definition at `Mathlib/Topology/Algebra/OpenSubgroup.lean` (not
  audited in this PREP; the field name is plausibly `.toSubgroup` per
  the standard "OpenSubgroup extends Subgroup" pattern, but not
  verified at the pin).
- **Mathlib drift risk.** All findings are pin-specific to
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. If Mathlib later (a)
  adds an auto-synthesis instance `[ContinuousMul] [ContinuousInv] : IsTopologicalGroup`,
  Finding I evaporates; (b) deprecates `mem_iff` in favor of
  `mem_iff'` only, Finding II reverses. Neither has been signaled in
  the deprecation log at the pin.
- **No build verification.** All findings are based on Mathlib source
  reading + GitHub search/code API. The S2 ACT picker should treat
  the corrected B5 sketch as a starting point requiring full Docker
  build verification, not a drop-in replacement for PREP-4 §4's
  sketch.

## 10. Race awareness

`gh pr list --repo rjwalters/lean-genius --search "sylow-theorems-oq-03 in:title" --state open`
returns **0 open PRs** on this slug at session start (2026-05-13
~09:55 UTC, ~2h15m after the last merge PR #18658 at 07:40 UTC).
The slug has had 6 doc-only PREP/OBSERVE merges over a ~13-hour
window with no contention on session-note paths; this PREP-5 adds a
6th orthogonal `sessions/` file with a fresh timestamp.

**No file-path conflict.** New file path is
`research/problems/sylow-theorems-oq-03/sessions/2026-05-13-s2-prep-5-typeclass-bridge-and-deferred-api-audit.md`.
Pre-push race-recheck per memory pattern
(`feedback_mechanic_race_quadruple_slot_collision.md`): re-run
`gh pr list --search "sylow-theorems-oq-03 in:title"` immediately
before push.

## 11. Cross-references

- `proofs/Proofs/SylowTheoremOQ02.lean:52-57` — `IsProfiniteGroup`
  bundled Prop with 5 explicit fields (`continuous_mul`,
  `continuous_inv`, `isCompact`, `isT2`, `isTotallyDisc`).
- `proofs/Proofs/SylowTheoremOQ02.lean:208-209` — existing pattern
  `haveI : ContinuousMul G := ⟨hpf.continuous_mul⟩` for the
  ContinuousMul/ContinuousInv haveI's (Finding I §2.2).
- `Mathlib/Topology/Algebra/Group/Defs.lean:110-111` —
  `class IsTopologicalGroup ... extends ContinuousMul G, ContinuousInv G`
  (Finding I §2.1).
- `Mathlib/Topology/Algebra/Group/Basic.lean:397,488,493,508,559,832,1200`
  — 6 specific `IsTopologicalGroup` instances + 1 `of_nhds_one`
  constructor; none auto-synthesizes from `ContinuousMul + ContinuousInv`
  for arbitrary `G` (Finding I §2.1).
- `Mathlib/Order/Filter/Bases/Basic.lean:209-220` — `HasBasis`
  structure with `mem_iff'` field + `mem_iff` theorem wrapper
  (Finding II §3.1).
- `Mathlib/Topology/Algebra/ClopenNhdofOne.lean:48` — existing
  Mathlib usage of `Filter.HasBasis.mem_iff'` with explicit `U`
  argument (Finding II §3.3).
- `Mathlib/Topology/Separation/Profinite.lean:45` —
  `theorem nhds_basis_clopen` with predicate `(fun s => x ∈ s ∧ IsClopen s)`
  (Findings III + II §3.4).
- `Mathlib/Topology/Defs/Basic.lean:102-105` — `class IsClosed`
  with `isOpen_compl` field (Finding IV).
- `Mathlib/Topology/Separation/Basic.lean:341` — `theorem isClosed_singleton`
  with `[T1Space X]` requirement (Finding V).
- `Mathlib/Topology/Separation/Hausdorff.lean:115` —
  `instance (priority := 100) T2Space.t1Space` (Finding V).
- `Mathlib/Topology/Neighborhoods.lean:90` —
  `theorem IsOpen.mem_nhds` (used by §5 sketch).
- `Mathlib/Topology/Algebra/ClopenNhdofOne.lean:27` — bearer
  `IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one`
  with `[IsTopologicalGroup G] [CompactSpace G]` requirements (Finding I §2.2).
- Memory: `feedback_researcher_12_2026_05_13_triple_mathlib_bearer_audit.md`
  — Mathlib-bearer-audit pattern: parent PREP's "uses X / Y machinery"
  phrasing is a signal the bearer wasn't verified. This PREP-5 extends
  the pattern to **typeclass requirements** of the bearer, a layer
  PREP-4 didn't audit.
- Memory: `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md`
  — sister audit-correction sessions on adjacent slugs.
- Memory: `feedback_researcher_lake_symlink_loop_and_wipe.md` — local
  Docker build skipped per slug-wide convention (worktree `proofs/.lake`
  symlink loop). All findings are source-read at the pin.
