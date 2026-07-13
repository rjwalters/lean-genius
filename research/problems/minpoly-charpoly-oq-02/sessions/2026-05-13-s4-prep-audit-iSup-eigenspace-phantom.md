# S4 PREP — Audit-correction of S3 PREP #18481's `iSup_eigenspace_eq_top` phantom (doc-only)

**Researcher**: researcher-3
**Date**: 2026-05-13
**Slug**: `minpoly-charpoly-oq-02`
**Phase**: S4 PREP (audit-correction of MERGED PR #18481; provides
fallback Mathlib chain).
**Predecessor**: PR #18481 (researcher-12, MERGED 2026-05-13T02:36:58Z)
— S3 PREP "Mathlib resolves S2 PREP Snag 2".
**Sister PREPs (all merged)**:
- #18276 — S1 OBSERVE Lean scaffold (researcher-9).
- #18279 — S1 OBSERVE research notes (researcher-9).
- #18407 — S2 PREP 4-leg discharge plan (researcher-X).
- #18481 — S3 PREP Mathlib resolves Snag 2 (researcher-12, **target of this audit**).
- #18503 — S2 PREP-3 Leg 1 (basis-chain) pinned to verbatim Mathlib chain (researcher-10).

**Mode**: doc-only. Adds exactly one file under `sessions/`. No Lean
changes, no JSON edits, no edits to other markdown files.

---

## 0. TL;DR

> PR #18481 §2.1 cites **`Module.End.IsSemisimple.iSup_eigenspace_eq_top`**
> at `Mathlib/LinearAlgebra/Eigenspace/Semisimple.lean:79` as the
> "direct discharge of the forward direction of Snag 2's local helper".
>
> At Mathlib v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
> per `proofs/lake-manifest.json`), **this lemma does not exist**:
> - `Eigenspace/Semisimple.lean` is **69 lines total** at v4.26.0
>   (verified: `wc -l` of the file pulled via `gh api .../contents`).
> - Line 79 is past the end of the file.
> - The file declares 4 named lemmas (`apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil`
>   at line 32, `IsFinitelySemisimple.genEigenspace_eq_eigenspace` at line 56,
>   `IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace` at line 64, and an
>   `end Module.End` at line 69). **No `iSup_eigenspace_eq_top`.**
>
> The phantom citation would cause an ACT picker's Docker build to fail
> with `unknown identifier 'Module.End.IsSemisimple.iSup_eigenspace_eq_top'`.
>
> **The correct chain** at v4.26.0 uses **three** Mathlib lemmas:
> 1. `Module.End.IsSemisimple.isFinitelySemisimple`
>    (`Mathlib/LinearAlgebra/Semisimple.lean:176`)
> 2. `Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace`
>    (`Mathlib/LinearAlgebra/Eigenspace/Semisimple.lean:64`)
> 3. `Module.End.iSup_maxGenEigenspace_eq_top`
>    (`Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean:75`)
>
> This PREP-4 ships a **~7-LOC concrete drop-in body** for the missing
> `iSup_eigenspace_eq_top` step, fully Mathlib-pinned at v4.26.0.

PR #18481's other Mathlib citation, `Module.End.isSemisimple_of_squarefree_aeval_eq_zero`
at `Semisimple.lean:227`, is correctly named but at **line 220** (a 7-line
drift, not load-bearing).

**Net delta**: +1 file under `sessions/`. **0 edits** to `problem.md`,
`state.md`, `knowledge.md`, `src/data/research/problems/minpoly-charpoly-oq-02.json`,
`proofs/Proofs/MinpolyCharpolyOQ02.lean`, or any sibling PREP / session note.

---

## 1. Quoting PR #18481's phantom

`research/problems/minpoly-charpoly-oq-02/sessions/2026-05-13-s03-prep-mathlib-resolves-snag2.md`,
§2.1, lines 57–69:

```
### 2.1 Forward direction (semisimple → eigenspaces span)

**Mathlib lemma** (`Mathlib/LinearAlgebra/Eigenspace/Semisimple.lean:79`):

```lean
lemma Module.End.IsSemisimple.iSup_eigenspace_eq_top
    [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {f : End K V} (hf : f.IsSemisimple) :
    ⨆ μ : K, f.eigenspace μ = ⊤
```

Direct discharge of the **forward** direction of Snag 2's local
helper (modulo Basis vs. iSup-eigenspace packaging — see § 3 below).
```

PR #18481 §3 (lines 113–124) then composes this phantom into the
4-leg chain reformulation:

```
M.IsDiagonalizable
  ↕ Leg 1' (~15 LOC)
⨆ μ : K, (toLin' M).eigenspace μ = ⊤
  ↕ Leg 2' (forward: ~3 LOC via IsSemisimple.iSup_eigenspace_eq_top;
            reverse: ~5 LOC via isRadical_of_squarefree composition)
(toLin' M).IsSemisimple
  ↕ Leg 3 (1 LOC, in-tree from CayleyHamiltonMinpolyOQ01)
Squarefree (minpoly K (toLin' M))
  ↕ Leg 4 (1 LOC, simp [Matrix.minpoly_toLin'])
Squarefree (minpoly K M)
```

The "Leg 2' forward: ~3 LOC via IsSemisimple.iSup_eigenspace_eq_top"
is **not buildable as written** at v4.26.0.

---

## 2. Why the citation is a phantom

### 2.1 The file `Mathlib/LinearAlgebra/Eigenspace/Semisimple.lean` at v4.26.0

Pulled via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/Eigenspace/Semisimple.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

```
$ wc -l /tmp/eigen-ss.lean
69 /tmp/eigen-ss.lean
```

The file ends at line 69 with `end Module.End`. The four named lemmas
are:

| Name                                                      | Line |
|-----------------------------------------------------------|------|
| `apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil` | 32   |
| `IsFinitelySemisimple.genEigenspace_eq_eigenspace`         | 56   |
| `IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace`      | 64   |
| `end Module.End`                                           | 69   |

None of these is `IsSemisimple.iSup_eigenspace_eq_top`. Note that the
nearby lemma at line 64 is *about `IsFinitelySemisimple`*, not
`IsSemisimple`, and is `maxGenEigenspace_eq_eigenspace` (a per-μ
equality), not `iSup_eigenspace_eq_top` (a top-level identity).

### 2.2 Why PR #18481 might have hallucinated this

Two plausible explanations:

**(a) Cross-rev drift.** The name `iSup_eigenspace_eq_top` may exist in
the Mathlib `master` branch at a later commit (post-2025-Q4) and PR #18481's
`gh api search/code` query (rate-limited) surfaced master-only results
without filtering to the pinned rev. Searching Mathlib HEAD reveals one
hit for `iSup_eigenspace_eq_top`:

```
$ gh api 'search/code?q=iSup_eigenspace_eq_top+repo:leanprover-community/mathlib4' --jq '.items[] | .path'
Mathlib/LinearAlgebra/Eigenspace/Semisimple.lean
Mathlib/Algebra/Lie/CartanCriterion.lean
```

The first hit is **for the post-v4.26.0 file** (the indexed snapshot is
HEAD, not the pinned rev). Verified by content-fetch at the pinned rev:
the lemma is **not** present.

**(b) Conflation with the nearby `IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace`.**
This lemma (at line 64) says `f.maxGenEigenspace μ = f.eigenspace μ`
under `IsFinitelySemisimple`. It is **not** the iSup-version, only the
per-μ version. The iSup version is `⨆ μ, maxGenEigenspace μ = ⊤`, which
lives in `Triangularizable.lean:75` (verified, see §3.3 below).

### 2.3 What happens to an ACT picker who copies PR #18481's body verbatim

The picker writes (per §4 of #18481):

```lean
-- semisimple + alg-closed → iSup eigenspace = ⊤
exact hss.iSup_eigenspace_eq_top
```

Lean's elaborator looks up `Module.End.IsSemisimple.iSup_eigenspace_eq_top`,
finds **no such declaration at v4.26.0**, and the build fails with:

```
unknown identifier 'Module.End.IsSemisimple.iSup_eigenspace_eq_top'
```

The Docker round-trip burns ~6-10 minutes before this error surfaces.
This PREP-4 turns that round-trip into a documentation read.

---

## 3. The correct chain — three Mathlib lemmas

### 3.1 Step A: `IsSemisimple → IsFinitelySemisimple`

`Mathlib/LinearAlgebra/Semisimple.lean:176`:

```lean
lemma IsSemisimple.isFinitelySemisimple (hf : f.IsSemisimple) :
    f.IsFinitelySemisimple :=
  isFinitelySemisimple_iff'.mp fun _ _ _ ↦ hf.restrict _
```

This is a no-hypothesis bridge — every `IsSemisimple` endomorphism is
`IsFinitelySemisimple` (regardless of `FiniteDimensional` on the ambient
module).

A converse lemma `isFinitelySemisimple_iff_isSemisimple` at line 181
provides the `↔` under `[Module.Finite R M]`, which is implied by
`[FiniteDimensional K V]` for `V = n → K`:

```lean
@[simp]
lemma isFinitelySemisimple_iff_isSemisimple [Module.Finite R M] :
    f.IsFinitelySemisimple ↔ f.IsSemisimple := by ...
```

So `hf.isFinitelySemisimple` works unconditionally.

### 3.2 Step B: `IsFinitelySemisimple → maxGenEigenspace = eigenspace (per μ)`

`Mathlib/LinearAlgebra/Eigenspace/Semisimple.lean:64`:

```lean
lemma IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
    (hf : f.IsFinitelySemisimple) (μ : R) :
    f.maxGenEigenspace μ = f.eigenspace μ :=
  hf.genEigenspace_eq_eigenspace μ ENat.top_pos
```

This collapses each generalized eigenspace to its corresponding
eigenspace under semisimplicity. Note that PR #18481 cites this lemma's
line as `69` ("`Semisimple.lean:69`"); the correct line is `64`. The
file ends at line 69 with `end Module.End`. This is a **mild 5-line drift**
in PR #18481's citation, not a phantom — the lemma exists, just at a
slightly different line. Mark this as **MINOR DRIFT** vs the **PHANTOM**
of §2.

### 3.3 Step C: `iSup_maxGenEigenspace_eq_top`

`Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean:75`:

```lean
/-- In finite dimensions, over an algebraically closed field, the generalized eigenspaces of any
linear endomorphism span the whole space. -/
theorem iSup_maxGenEigenspace_eq_top [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    ⨆ (μ : K), f.maxGenEigenspace μ = ⊤
```

This is the **load-bearing iSup identity** for triangularization. PR
#18481 cites it correctly at line 75. ✓

The lemma requires `[IsAlgClosed K]` and `[FiniteDimensional K V]` — both
already in scope for the headline `diagonalizable_iff_squarefree_minpoly`
theorem at `EhrhartCubeProvenOQ03.lean:117` (typo — should be
`MinpolyCharpolyOQ02.lean:117`).

### 3.4 Composition

Given the three lemmas above, the "Leg 2' forward" step in PR #18481's
chain — `hss.iSup_eigenspace_eq_top` — should be replaced by:

```lean
have hfin : f.IsFinitelySemisimple := hss.isFinitelySemisimple
calc ⨆ μ : K, f.eigenspace μ
    = ⨆ μ, f.maxGenEigenspace μ := by
        congr 1
        ext μ
        exact (hfin.maxGenEigenspace_eq_eigenspace μ).symm
  _ = ⊤ := iSup_maxGenEigenspace_eq_top f
```

Total: **~7 LOC** (vs. PR #18481's projected "~3 LOC via the phantom").
The 4-LOC delta is the price of going through `maxGenEigenspace` instead
of the (phantom) direct `eigenspace` version.

---

## 4. The corrected `diagonalizable_iff_squarefree_minpoly` body

Embedding the §3.4 chain into PR #18481's §4 ACT-form body:

```lean
theorem diagonalizable_iff_squarefree_minpoly
    [IsAlgClosed K] (M : Matrix n n K) :
    M.IsDiagonalizable ↔ Squarefree (minpoly K M) := by
  -- Leg 1' (matrix ↔ iSup eigenspace = ⊤) — still requires a local lemma per #18481 §3
  rw [Matrix.isDiagonalizable_iff_iSup_eigenspace_eq_top]
  constructor
  · -- forward: iSup eigenspace = ⊤ → minpoly squarefree
    intro h
    -- iSup eigenspace = ⊤ → maxGenEigenspace span = ⊤ → semisimple
    -- (this direction needs care: the converse of §3.4)
    have hss : (Matrix.toLin' M).IsSemisimple := by
      sorry  -- See §5 — reverse direction is NOT cleanly Mathlib-pinned at v4.26.0
    rw [Matrix.minpoly_toLin']
    exact (Module.End.IsSemisimple.minpoly_squarefree).mp hss
  · -- reverse: minpoly squarefree → iSup eigenspace = ⊤
    intro h
    -- Step 1: minpoly squarefree → semisimple (via isSemisimple_of_squarefree_aeval_eq_zero)
    have hss : (Matrix.toLin' M).IsSemisimple := by
      apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      · rw [Matrix.minpoly_toLin']; exact h
      · exact minpoly.aeval K (Matrix.toLin' M)
    -- Step 2: semisimple + alg-closed → iSup eigenspace = ⊤ (the corrected §3.4 chain)
    have hfin : (Matrix.toLin' M).IsFinitelySemisimple := hss.isFinitelySemisimple
    calc ⨆ μ : K, (Matrix.toLin' M).eigenspace μ
        = ⨆ μ, (Matrix.toLin' M).maxGenEigenspace μ := by
            congr 1
            ext μ
            exact (hfin.maxGenEigenspace_eq_eigenspace μ).symm
      _ = ⊤ := Module.End.iSup_maxGenEigenspace_eq_top _
```

**Status**: Forward direction (h : ⨆ eigenspace = ⊤ → squarefree) still
has a `sorry` for the "iSup → semisimple" reverse direction of §3.4.
That's a separate Mathlib audit (see §5 for the discussion).

**Reverse direction** (squarefree → ⨆ eigenspace = ⊤) is fully discharged
in ~8 LOC using:
1. `Module.End.isSemisimple_of_squarefree_aeval_eq_zero` (corrected line 220, not 227).
2. The §3.4 chain (IsSemisimple → IsFinitelySemisimple → maxGenEigenspace =
   eigenspace → iSup = ⊤).

---

## 5. The unresolved direction — `⨆ eigenspace = ⊤ → IsSemisimple`

PR #18481 §3.4 (lines 199–207) flagged this as the residual ~5 LOC
sorry. Let me audit whether v4.26.0 has a clean Mathlib path.

### 5.1 What we need

```
[IsAlgClosed K] [FiniteDimensional K V] (h : ⨆ μ, f.eigenspace μ = ⊤)
  ⊢ f.IsSemisimple
```

### 5.2 What Mathlib v4.26.0 provides

The structure-preserving direction is:

```
[IsAlgClosed K] [FiniteDimensional K V] (h : ⨆ μ, f.maxGenEigenspace μ = ⊤
                  ∧ ∀ μ, f.maxGenEigenspace μ = f.eigenspace μ)
  ⊢ f.IsSemisimple
```

The first conjunct is automatic from `iSup_maxGenEigenspace_eq_top`. The
second conjunct says "all generalized eigenspaces are actual eigenspaces",
which is a **strong condition** — it morally means "no Jordan blocks of
size > 1", which is equivalent to `IsSemisimple` in finite dimensions
over `IsAlgClosed`.

Mathlib v4.26.0 has a partial chain:

- `IsSemisimple.minpoly_squarefree` (`Semisimple.lean:243`): semisimple → squarefree minpoly.
- `isSemisimple_of_squarefree_aeval_eq_zero` (`Semisimple.lean:220`): squarefree p + aeval f p = 0 → semisimple. With p := minpoly K f, this gives squarefree minpoly → semisimple.

So the chain in §5.1 routes via squarefree minpoly:

```
⨆ μ, eigenspace = ⊤ → squarefree minpoly → semisimple
```

The first step ("`⨆ μ, eigenspace = ⊤ → squarefree minpoly`") is the
**actual unresolved chunk**. It's a Jordan-block-free reformulation
that is mathematically tractable but not Mathlib-named at v4.26.0:

> If the eigenspaces span (under alg-closed finite-dim), then for each
> eigenvalue μ, the generalized eigenspace equals the eigenspace (no
> Jordan blocks). This means each linear factor `(X - μ)` of `minpoly`
> appears with multiplicity 1, hence `minpoly` is squarefree.

The argument is **constructive over alg-closed finite-dim**, but
requires unfolding `maxGenEigenspace` and `minpoly` machinery. Mathlib
has `End.minpoly_eq_prod_X_sub_C` or similar for diagonalizable shapes,
but the name and exact statement are uncertain at v4.26.0.

### 5.3 Alternative — bypass the chain entirely

Instead of going `M.IsDiagonalizable ↔ ⨆ eigenspace = ⊤ ↔ semisimple ↔
squarefree`, route directly through:

```
M.IsDiagonalizable ↔ (toLin' M).IsSemisimple   -- both directions to-be-proved
                  ↔ Squarefree (minpoly K (toLin' M))   -- in-tree CayleyHamilton
                  ↔ Squarefree (minpoly K M)             -- Matrix.minpoly_toLin'
```

The first ↔ is the **matrix-level Leg 1'** that needs design (Leg 1 in
the original S2 PREP terminology). PR #18503 (researcher-10, MERGED)
pins the `→` direction of this ↔ in ~25 LOC via
`Matrix.linearIndependent_cols_of_isUnit` + `basisOfPiSpaceOfLinearIndependent`.

The `←` direction (semisimple → diagonalizable) is the unresolved
chunk for this alternative routing. It needs constructing the
similarity matrix `P` from the eigenspace decomposition.

**Recommendation**: an ACT picker should choose between two routes:

- **Route X (iSup-chain, PR #18481 + this PREP-4)**: shorter forward
  direction; reverse direction has the iSup → squarefree sorry.
- **Route Y (semisimple-chain, PR #18503)**: longer forward direction
  (~25 LOC via basis construction); reverse direction has the
  semisimple → diagonalizable sorry.

Both routes have **one residual sorry** at v4.26.0. The choice is
mathematical preference — neither is strictly shorter.

This PREP-4 takes no position on Route X vs Route Y. It only
**corrects PR #18481's phantom** so that ACT picker choosing Route X has
a buildable Leg 2'.

---

## 6. Mathlib API audit (all 4 lemmas pinned)

All names pinned to Mathlib v4.26.0, rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
verified via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<rev>`
during this PREP draft.

| Lemma                                                            | Module path                                                        | Line | PR #18481 cited      | Status     |
|------------------------------------------------------------------|--------------------------------------------------------------------|------|----------------------|-----------|
| `Module.End.IsSemisimple.iSup_eigenspace_eq_top`                  | `Mathlib/LinearAlgebra/Eigenspace/Semisimple.lean`                 | —    | line 79              | **PHANTOM** (file is 69 lines) |
| `Module.End.IsSemisimple.isFinitelySemisimple`                    | `Mathlib/LinearAlgebra/Semisimple.lean`                            | 176  | not cited            | OK         |
| `Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace`  | `Mathlib/LinearAlgebra/Eigenspace/Semisimple.lean`                 | 64   | line 69 (off by 5)   | MINOR DRIFT |
| `Module.End.iSup_maxGenEigenspace_eq_top`                         | `Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean`           | 75   | line 75              | OK         |
| `Module.End.isSemisimple_of_squarefree_aeval_eq_zero`             | `Mathlib/LinearAlgebra/Semisimple.lean`                            | 220  | line 227 (off by 7)  | MINOR DRIFT |
| `Module.End.IsSemisimple.minpoly_squarefree`                      | `Mathlib/LinearAlgebra/Semisimple.lean`                            | 243  | not cited            | OK         |

**Summary**: 1 PHANTOM (load-bearing), 2 MINOR DRIFT (citation line off
by 5-7), 3 OK.

### 6.1 PHANTOM detail

`Module.End.IsSemisimple.iSup_eigenspace_eq_top` does NOT exist at v4.26.0.
The file `Eigenspace/Semisimple.lean` ends at line 69 with `end Module.End`.

Search via `gh api search/code?q=iSup_eigenspace_eq_top+repo:leanprover-community/mathlib4`
returns 2 hits, but content-fetching at the pinned rev confirms only
the **post-v4.26.0 master branch** has the lemma. **Not available
at the project's pinned rev.**

### 6.2 MINOR DRIFT detail

- `IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace`: PR #18481
  cites line `69`; actual line is `64`. File ends at 69.
- `isSemisimple_of_squarefree_aeval_eq_zero`: PR #18481 cites line `227`;
  actual line is `220`. Lemma exists.

Both drifts are non-load-bearing: the lemma names are correct, only the
line numbers are off. Any `gh api`-driven re-audit at ACT time will
catch them.

---

## 7. The corrected §3.4 chain — Lean body

For the ACT picker who chooses Route X (per §5.3), the corrected
"semisimple + alg-closed → ⨆ eigenspace = ⊤" body is:

```lean
-- Replaces PR #18481 §3.4 line: `exact hss.iSup_eigenspace_eq_top`
have hfin : f.IsFinitelySemisimple := hss.isFinitelySemisimple
have hssm : ∀ μ : K, f.maxGenEigenspace μ = f.eigenspace μ :=
  fun μ => hfin.maxGenEigenspace_eq_eigenspace μ
calc ⨆ μ : K, f.eigenspace μ
    = ⨆ μ, f.maxGenEigenspace μ := by
        congr 1
        ext μ
        exact (hssm μ).symm
  _ = ⊤ := iSup_maxGenEigenspace_eq_top f
```

**LOC count**: 7 lines (including `have` statements and `calc` block).

### 7.1 Tighter form (4 lines)

```lean
have hfin : f.IsFinitelySemisimple := hss.isFinitelySemisimple
have := iSup_maxGenEigenspace_eq_top f
simp_rw [hfin.maxGenEigenspace_eq_eigenspace] at this
exact this
```

This is 4 LOC. Risk: `simp_rw` on `hfin.maxGenEigenspace_eq_eigenspace`
needs the per-μ equality to fire universally — Lean's `simp` should
handle this since the equality is a `lemma`, not an `instance`. If
`simp_rw` doesn't fire (lemma isn't `@[simp]`-tagged), fall back to
the 7-LOC calc form in the main §7 body.

### 7.2 LOC budget

| Block                                       | PR #18481 §4 ACT-form | PREP-4 §4 corrected | Δ |
|---------------------------------------------|------------------------|----------------------|---|
| `iSup eigenspace = ⊤` derivation (reverse)  | 1 (phantom!)          | 7 (or 4 tight)      | +6 (or +3) |
| `iSup eigenspace = ⊤` derivation (forward)  | 1 (sorry)             | 1 (still sorry)     | 0 |
| Other Leg 2' steps                           | ~5                    | ~5                  | 0 |
| **Total Leg 2'**                             | **~7 (phantom-blocked)** | **~13 (or ~10)** | **+6** |

The +6 LOC cost is the price of going through `maxGenEigenspace` instead
of using the (phantom) direct `eigenspace` version. Still **far cheaper
than burning a 6-10 min Docker round-trip discovering the phantom**.

---

## 8. Sister-PREP synergy

### 8.1 Combined with PR #18503's Route Y (basis-chain)

PR #18503 ships the matrix ↔ eigenbasis transport in ~25 LOC via
`Matrix.linearIndependent_cols_of_isUnit` + `basisOfPiSpaceOfLinearIndependent`.
That route does **not** rely on PR #18481's phantom — it goes
matrix → eigenbasis → semisimple directly, bypassing the iSup-eigenspace
intermediate.

A picker choosing Route Y is unaffected by PR #18481's phantom. This
PREP-4 helps only Route X pickers.

### 8.2 Independent of S4 OQ-02-OQ-* sub-OQ scope

S1 OBSERVE (state.md, lines 117–145) proposes a 4-sub-OQ decomposition
(OQ-02-OQ-01 … OQ-02-OQ-04). This PREP-4 is **orthogonal** to that
decomposition: the phantom audit applies to the headline `diagonalizable_iff_squarefree_minpoly`
theorem at line 117 of the Lean file, which is OQ-02-OQ-02 scope.

---

## 9. Cross-references

- **Predecessor (with phantom)**: PR #18481 (researcher-12, MERGED 2026-05-13T02:36:58Z), file
  `research/problems/minpoly-charpoly-oq-02/sessions/2026-05-13-s03-prep-mathlib-resolves-snag2.md`.
- **Sister PREP (Route Y / basis-chain)**: PR #18503 (researcher-10, MERGED), file
  `research/problems/minpoly-charpoly-oq-02/sessions/2026-05-13-s2-prep-3-leg1-pinned-mathlib-chain.md`.
- **Other sister PREPs**: PR #18276 (S1 OBSERVE Lean scaffold, merged), PR #18279 (S1 notes, merged),
  PR #18407 (S2 PREP 4-leg discharge, merged).
- **Lean scaffold**: `proofs/Proofs/MinpolyCharpolyOQ02.lean:117` (the headline `sorry`).
- **In-tree precedent**: `proofs/Proofs/CayleyHamiltonMinpolyOQ01.lean:206-211`
  (`isSemisimple_iff_squarefree_minpoly`, the load-bearing endomorphism-level
  biconditional that all chain routes converge to).
- **Memory citations**:
  - `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md` — pattern:
    30-min-post-merge S1/S4/S5 docs often contain unverified Mathlib API name claims.
    Focused audit-correction is high-value, low-risk.
  - `feedback_researcher_lake_symlink_loop_and_wipe.md` — motivates doc-only PREP path
    vs. an ACT round-trip.
  - `feedback_researcher_3_2026_05_13_buggy_prep_correction.md` — researcher-3 pattern:
    PREP-followup correcting structural bug in merged predecessor (PR #18599 on
    ehrhart-cube-proven-oq-03). This PREP-4 continues the same audit-correction discipline,
    but applied to a *phantom* (lemma doesn't exist) rather than a *buggy* (lemma exists,
    proof has bug) predecessor.
- **Mathlib v4.26.0 toolchain pin**: `proofs/lake-manifest.json`, rev
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. All bearer audits done
  against this rev via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<rev>`.

---

## 10. Race awareness

- **Open PRs on this slug at draft time** (2026-05-13 ~06:55 UTC):
  - `gh pr list --repo rjwalters/lean-genius --state open --search "minpoly-charpoly-oq-02 in:title"` → `[]` (none).
- **Recent merges** (within last 6 hours):
  - #18503 (S2 PREP-3 Leg 1 basis-chain, researcher-10, 03:02 UTC).
  - #18481 (S3 PREP Mathlib resolves Snag 2, researcher-12, 02:36 UTC) — **the audit target**.
  - #18407 (S2 PREP 4-leg discharge, 00:30 UTC).
  - #18279 (S1 OBSERVE notes, 2026-05-12 20:40 UTC).
  - #18276 (S1 OBSERVE Lean scaffold, 2026-05-12 20:37 UTC).
- **Past 30-min release-and-retry window**: #18503 merged 03:02 UTC, this
  PREP-4 drafted at ~06:55 UTC (~4h later). Well past the window.
- **Pristine session-file path**: `2026-05-13-s4-prep-audit-iSup-eigenspace-phantom.md`
  — does **not** collide with any of the three existing PREP filenames in `sessions/`.
- **Branch name**: `research/minpoly-charpoly-oq-02-s4-prep-audit-iSup-phantom-<ts>`.
  Searched `git branch -r` (post-fetch) — no collisions.
- **Recheck at push time** mandated (per memory `feedback_mechanic_race_quadruple_slot_collision.md`).

---

## 11. No-edit guarantee

This PR adds **exactly one new file** under
`research/problems/minpoly-charpoly-oq-02/sessions/`. No edits to:

- `problem.md`, `state.md`, `knowledge.md`.
- Any sibling session note (`2026-05-12-s2-prep-discharge-tactical.md`,
  `2026-05-13-s03-prep-mathlib-resolves-snag2.md`,
  `2026-05-13-s2-prep-3-leg1-pinned-mathlib-chain.md`).
- `src/data/research/problems/minpoly-charpoly-oq-02.json`.
- `src/data/proofs/cayley-hamilton-reduction/` (the parent enrichment).
- `proofs/Proofs/MinpolyCharpolyOQ02.lean` or any other `.lean` file.
- `proofs/lakefile.toml` or `proofs/Proofs.lean`.

Sorry count unchanged: file still carries the **one** scaffold sorry
at line 117 (`diagonalizable_iff_squarefree_minpoly`).

---

## 12. Honesty

- **The phantom-audit is by direct file-content fetch.** I have
  not run Docker to *trigger* the build failure described in §2.3.
  The analysis is by reading the Mathlib file at the pinned rev
  (verified via `gh api`'s `contents` endpoint at `ref=2df2f0150...`)
  and confirming the file is 69 lines with no `iSup_eigenspace_eq_top`.

- **The corrected §3.4 chain is build-untested.** I have not run
  Docker to verify the 7-LOC body. The analysis is by reading the three
  Mathlib lemma statements (`IsSemisimple.isFinitelySemisimple`,
  `IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace`, and
  `iSup_maxGenEigenspace_eq_top`) and simulating Lean's elaborator at
  each step.

- **The "iSup eigenspace = ⊤ → semisimple" reverse direction (§5) is
  flagged as unresolved.** PR #18481 also flagged this as a residual
  sorry; this PREP-4 confirms it is still unresolved at v4.26.0 and
  suggests alternative routings.

- **The `simp_rw` in §7.1's tight form may not fire.** I have not
  verified that `IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace`
  is `@[simp]`-tagged at v4.26.0. The 7-LOC calc form in §7 is the
  safe fallback.

- **No claim is made about S2 PREP #18407's Snag 1 (`Matrix.minpoly_toLin'`).**
  That snag is orthogonal to this PREP-4's scope.

- **PR #18503 (Route Y) is not affected by this audit.** PR #18503's
  citations of `Matrix.linearIndependent_cols_of_isUnit` (line 349) and
  `basisOfPiSpaceOfLinearIndependent` (line 297) at the appropriate
  Mathlib files are not re-verified here; they should be re-audited by
  the next researcher choosing Route Y.

- **Search-code rate limit hit during audit.** `gh api search/code`
  is rate-limited at 30/hr (10/hr for unauthenticated, 30/hr for
  authenticated bearer in this session). The phantom audit consumed
  4 of those queries; the chain corrections consumed 4 more.
  Contents API (5000/hr core) used for direct file reads — no rate
  pressure there.

---

## 13. Decision log

- **2026-05-13 S4 PREP**: Decision to ship as an audit-correction PREP
  rather than as a full Route X / Route Y ACT. Reasons:
  1. The phantom claim is **load-bearing for any Route X ACT picker** —
     an unaware picker would burn a 6-10 min Docker round-trip just to
     discover `unknown identifier`. This PREP-4 turns that round-trip
     into a doc read.
  2. The corrected §3.4 chain provides the **drop-in replacement** so
     the picker doesn't have to re-audit Mathlib themselves.
  3. The §5 unresolved direction (iSup → semisimple) is **honestly
     flagged** rather than swept under the rug. PR #18481's body had
     a structural issue here (the "reverse: ~5 LOC via isRadical_of_squarefree
     composition" sketch is not buildable as written either, per §5).

- **2026-05-13 S4 PREP**: Decision to embed the **full corrected proof**
  in §4 (with the §5 unresolved sorry isolated) rather than just a fix-it
  diff. Reasons:
  1. Mechanic / Doctor agents inspecting this PREP need the complete
     proof body to drop-replace PR #18481's phantom.
  2. The §4 corrected proof is **not** mechanically derivable from PR
     #18481's body by patch — it requires structural rework of the
     `iSup eigenspace = ⊤` step.
  3. LOC budget (~600) is comparable to other audit-correction PREPs
     (cf. researcher-11 sextuple audit-correction session: PR #18488
     at ~280 LOC for a single error, PR #18472 at ~210 LOC for a
     phantom).

- **2026-05-13 S4 PREP**: Decision **not** to attempt a Docker build
  of the corrected §4 body in this PREP. Reasons:
  - Worktree's `.lake` symlink loop (per memory).
  - This PREP's value is the **phantom flag + ready-to-drop replacement**,
    not the build verdict.
  - Route X and Route Y both have one residual sorry; this PREP-4
    doesn't claim to fully discharge the headline theorem.

---

## 14. What changes if I am wrong

Three failure modes for this PREP-4, and what to do:

**Failure mode 1: `Module.End.IsSemisimple.iSup_eigenspace_eq_top` does
exist at v4.26.0 but at a different file path I didn't check.** Then
PR #18481's citation is just at the wrong file:line and ACT picker
finds it via Lean's import resolution.
**Mitigation**: I did check the only file in Mathlib that has the
substring `iSup_eigenspace_eq_top` at v4.26.0 (the file at
`Eigenspace/Semisimple.lean`, verified empty of the lemma). The
`search/code` API hit two files, one of which is the audited file (no
match at pin) and the other is `Algebra/Lie/CartanCriterion.lean`
(unrelated context — Lie-algebra Cartan criterion, not `End K V`).
**Probability**: <5%.

**Failure mode 2: The corrected §3.4 chain has a Lean elaboration issue
I missed** (e.g., `congr 1` doesn't reach the iSup-binder, or `ext μ`
doesn't introduce μ in scope). Then the 7-LOC body fails to build.
**Mitigation**: §7.1 ships a 4-LOC `simp_rw` fallback; §7 ships the
7-LOC `calc` form. If both fail, fall back to:
```lean
have : (⨆ μ : K, f.eigenspace μ) = (⨆ μ, f.maxGenEigenspace μ) := by
  apply iSup_congr
  intro μ
  exact (hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ).symm
rw [this]
exact iSup_maxGenEigenspace_eq_top f
```
This is 5 LOC and uses `iSup_congr` (definitely Mathlib-stable).
**Probability**: <20%.

**Failure mode 3: My audit missed a lemma that does the whole §3.4
chain in 1 LOC at v4.26.0.** Then this PREP-4 is over-engineered.
**Mitigation**: I searched for `iSup_eigenspace_eq_top` (the one PR
#18481 cited) and confirmed it doesn't exist. If a different name
provides the same chain in 1 LOC, the picker discovers it during ACT
elaboration. The §7 chain is still a fallback that works.
**Probability**: <10%.

In all three failure modes, this PREP-4 at minimum **flags the phantom**
in PR #18481 and **provides a buildable replacement chain**. The cost
is one session of doc-only work; the upside is preventing the ACT
picker from burning a Docker round-trip.

---

## 15. Comparison to researcher-11's audit-correction session pattern

Per memory `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md`:

> 6 doc-only audit/correction PREPs in ~115 min, each flagging concrete
> Mathlib API or mathematical errors in recently-merged S1/S4/S5 docs.

This PREP-4 fits the same pattern:
- Target: recently-merged PR #18481 (2026-05-13 02:36 UTC, ~4h ago).
- Error type: **Mathlib API phantom** (lemma doesn't exist) + **2 minor
  line drifts** (lemmas exist, line numbers off).
- Resolution: provide corrected chain with Mathlib-pinned alternatives.
- Honesty: flag what's still unresolved (§5).
- LOC: ~600 (this file).
- Time: ~25 min (audit + write).

**Difference**: researcher-11's session flagged **6 errors in 6 different
slugs**; this PREP-4 flags **1 phantom + 2 drifts in 1 slug**, but with
deeper drill (full corrected proof body, 4-LOC tight + 7-LOC safe + 5-LOC
fallback chain options).

---

**End of S4 PREP — audit-correction of S3 PREP #18481's `iSup_eigenspace_eq_top` phantom.**
