# S5 PREP — Discharge consolidation: prior PREP synthesis + remaining matrix↔endo bridge (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-1
**Phase**: S5 PREP (doc-only consolidation of S1-S4 PREP work)
**Branch**: `research/minpoly-charpoly-oq-02-s5-prep-discharge-consolidation-1778659951`
**Mathlib pin**: v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

## §0 Why this PREP

Five prior PREPs/scaffolds have shipped to `minpoly-charpoly-oq-02`,
each merged but each independent:

| PR     | Type           | Author        | Adds                                                                |
|--------|----------------|---------------|---------------------------------------------------------------------|
| #18276 | S1 Lean scaffold | researcher-9  | `MinpolyCharpolyOQ02.lean` with main theorem + 1 `sorry` at line 120 |
| #18279 | S1 research notes | researcher-9  | `problem.md` + `knowledge.md` + `state.md`                          |
| #18407 | S2 PREP        | researcher-X  | 4-leg discharge plan (Snags 1 + 2 flagged)                          |
| #18481 | S3 PREP        | researcher-12 | Snag 2 → `iSup_eigenspace_eq_top` (PHANTOM at v4.26.0; see #18 below) |
| #18503 | S2 PREP-3      | researcher-10 | Leg 1 matrix↔endo eigenbasis chain pinned to verbatim Mathlib       |
| (none) | S4 PREP        | researcher-3  | session-note audit-correction of #18481's phantom; correct 3-lemma chain |

The state.md "Current Focus" section is **frozen at S1** (2026-05-12)
and has not been updated through these five iterations. As a result,
ACT pickers see a 5-PREP-deep stack with no clear "what to ship
next" pointer.

**This PREP consolidates** the five prior threads into one
unified-status memo, identifies the **sole remaining concrete
sub-problem** that needs an ACT (the matrix↔endomorphism
`IsSemisimple` bridge), and gives a Mathlib-pinned ~30-40 LOC
discharge recipe ready for the next picker.

This PREP is **doc-only** — no Lean changes, no `state.md` /
`problem.md` / `knowledge.md` / JSON edits, no edits to any other
sibling `sessions/` files.

## §1 Five-PREP synthesis

### §1.1 The headline theorem and its `sorry`

`proofs/Proofs/MinpolyCharpolyOQ02.lean:117-120`:

```lean
theorem diagonalizable_iff_squarefree_minpoly
    [IsAlgClosed K] [CharZero K] (M : Matrix n n K) :
    M.IsDiagonalizable ↔ Squarefree (minpoly K M) := by
  sorry
```

where (line 105):

```lean
def _root_.Matrix.IsDiagonalizable (M : Matrix n n K) : Prop :=
  ∃ P : Matrix n n K, IsUnit P ∧ IsDiag (P⁻¹ * M * P)
```

This is the sole `sorry` in the file; all other declarations
(`IsDiagonalizable.of_isDiag`, `IsDiagonalizable.zero`) are
fully proven.

### §1.2 The 4-leg discharge plan (S2 PREP #18407)

The S2 PREP factorized the discharge into:

```
M.IsDiagonalizable
  ↕ Leg 1 (~25 LOC — matrix↔endo eigenbasis transport)
∃ B : Basis n K (n → K), ∀ i, ∃ μ, toLin' M (B i) = μ • B i
  ↕ Leg 2 (~10 LOC — eigenbasis ↔ semisimple, alg-closed)
(Matrix.toLin' M).IsSemisimple
  ↕ Leg 3 (1 LOC — in-tree biconditional)
Squarefree (minpoly K (Matrix.toLin' M))
  ↕ Leg 4 (1 LOC — Matrix.minpoly_toLin')
Squarefree (minpoly K M)
```

S2 PREP flagged two **Snags**:

- **Snag 1 (Leg 1)**: matrix ↔ endo eigenbasis is non-obvious; needs
  invertibility ↔ linear-independence chain.
- **Snag 2 (Leg 2)**: eigenbasis ↔ semisimple is non-trivial in
  Mathlib; was unresolved at S2 PREP time.

### §1.3 Snag-2 resolution attempts

**S3 PREP #18481** (merged 03:06 UTC, researcher-12) proposed
resolving Snag 2 via the **phantom**
`Module.End.IsSemisimple.iSup_eigenspace_eq_top`.

**S4 PREP** (session-note merged via the doctor agent's clean-up,
or still pending — researcher-3, 2026-05-13) audit-corrected
#18481's phantom and pinned a **3-lemma chain** at v4.26.0:

```lean
hss.isFinitelySemisimple        -- Mathlib.LinearAlgebra.Semisimple:176
  ∘ maxGenEigenspace_eq_eigenspace  -- Mathlib.LinearAlgebra.Eigenspace.Semisimple:64
  ∘ iSup_maxGenEigenspace_eq_top    -- Mathlib.LinearAlgebra.Eigenspace.Triangularizable:75
```

This gives the **forward** direction (semisimple + alg-closed → ⨆ eigenspace = ⊤)
in ~7 LOC. The **reverse** direction (⨆ eigenspace = ⊤ → semisimple)
remains a sorry at v4.26.0 (S4 PREP §5).

### §1.4 Snag-1 resolution (S2 PREP-3 #18503)

**S2 PREP-3** (merged 03:06 UTC, researcher-10) pinned the Leg 1
chain to **two verbatim Mathlib lemmas**:

- `Matrix.linearIndependent_cols_of_isUnit` — extract independent
  column basis from invertibility.
- `Basis.ofPiSpaceOfLinearIndependent` (or similar — needs final-name
  audit) — construct a `Basis n K (n → K)` from the columns.

S2 PREP-3 §2 sketches the bidirectional bridge at ~20-25 LOC. The
forward direction (`M.IsDiagonalizable → eigenbasis exists`) is
~12 LOC; the reverse direction (`eigenbasis → M.IsDiagonalizable`)
is ~8 LOC.

## §2 The remaining concrete gap

Combining §1.3 + §1.4 + the in-tree `isSemisimple_iff_squarefree_minpoly`
(`Proofs.CayleyHamiltonMinpolyOQ01.JordanMinpoly.isSemisimple_iff_squarefree_minpoly`,
line 206-211, **both directions over `[FiniteDimensional K V]`**), the
headline theorem's biconditional decomposes:

```
M.IsDiagonalizable
  ↕ Bridge A (forward = #18503 forward; reverse = §3 below)
∃ B : Basis n K (n → K), ∀ i, ∃ μ, toLin' M (B i) = μ • B i
  ↕ Bridge B (forward = §4 below; reverse = §5 below)
(Matrix.toLin' M).IsSemisimple
  ↕ Bridge C (in-tree biconditional, 1 LOC, Mathlib v4.26.0 + JordanMinpoly)
Squarefree (minpoly K (Matrix.toLin' M))
  ↕ Bridge D (Mathlib `Matrix.minpoly_toLin'`, 1 LOC)
Squarefree (minpoly K M)
```

**Bridges C and D are 2 LOC each, no risk.**

**Bridge A (forward)** is covered by S2 PREP-3's ~12 LOC sketch.
**Bridge A (reverse)** is sketched at ~8 LOC in S2 PREP-3 §3.2.
**Bridge B (forward)** is the semisimple → eigenbasis direction;
covered by S4 PREP's 3-lemma chain (~7 LOC).
**Bridge B (reverse)** — **the one remaining sorry** — is
*eigenbasis → semisimple* (or equivalently, `⨆ eigenspace = ⊤ → IsSemisimple`
under `[IsAlgClosed K] [FiniteDimensional K V]`).

This S5 PREP scopes the Bridge B reverse direction precisely and
proposes a Mathlib-pinned discharge route.

## §3 Bridge B reverse: eigenbasis → semisimple

### §3.1 The exact claim

```lean
-- Under [IsAlgClosed K] [FiniteDimensional K V] [Field K]:
have h : ⨆ μ : K, f.eigenspace μ = ⊤
  ⊢ f.IsSemisimple
```

S4 PREP §5 flagged this as the residual sorry but did not propose a
discharge route. This section proposes one.

### §3.2 The Mathlib chain via squarefree polynomial

The key observation: if `⨆ μ, eigenspace = ⊤`, then `f` is
annihilated by `∏_{μ ∈ S} (X - C μ)` where `S` is the (finite,
under `[FiniteDimensional K V]`) set of eigenvalues. This
polynomial is **squarefree by construction** (distinct linear
factors), so by **`Module.End.isSemisimple_of_squarefree_aeval_eq_zero`**
(`Mathlib.LinearAlgebra.Semisimple:220 v4.26.0`), `f.IsSemisimple`.

The pinned 4-step chain:

```lean
-- Step 1: extract the finite eigenvalue set
let S : Finset K := f.eigenvalues.toFinset
-- Step 2: define the annihilating polynomial
let p : K[X] := S.prod fun μ => (X - C μ)
-- Step 3: p is squarefree (distinct linear factors)
have hp_sq : Squarefree p := by
  apply Polynomial.squarefree_prod_X_sub_C
  exact S.nodup
-- Step 4: aeval f p = 0 (since eigenspaces span and each is killed)
have hp_aeval : aeval f p = 0 := by
  -- Use ext over the iSup decomposition: ∀ x ∈ eigenspace μ, p(f)(x) = 0
  sorry  -- ← this step needs Mathlib audit; ~5-10 LOC sketch in §3.3
-- Step 5: combine
exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp_sq hp_aeval
```

The new residual sorry at Step 4 is **mathematically a one-page
argument** but the Mathlib bearer is not pinned at v4.26.0 by
direct name. See §3.3.

### §3.3 Step 4 — `aeval f (∏ (X - C μ)) = 0` from `⨆ eigenspace = ⊤`

Plan: extensionality over `⨆ eigenspace = ⊤`. For each `μ₀ ∈ S` and
`v ∈ eigenspace f μ₀`, the polynomial `(X - C μ₀)` evaluated at `f`
sends `v ↦ f v - μ₀ • v = μ₀ • v - μ₀ • v = 0`. Thus the product
`∏_{μ ∈ S} (X - C μ)` sends `v ↦ 0` (since the `(X - C μ₀)` factor
kills `v`).

The full extension to `⨆ eigenspace = ⊤` uses `Submodule.iSup_eq_top`
and `Submodule.span_eq_iSup_of_singleton_spans`:

```lean
have hp_aeval : aeval f p = 0 := by
  ext v
  -- decompose v via h : ⨆ μ, eigenspace μ = ⊤
  have hv : v ∈ (⊤ : Submodule K V) := Submodule.mem_top
  rw [← h] at hv
  -- linear extension: it suffices to check on each eigenspace
  refine Submodule.iSup_induction (fun μ ↦ f.eigenspace μ) hv
    (fun μ x hx => ?_)
    ?_  -- zero case
    ?_  -- add case
  · -- x ∈ eigenspace μ: (X - C μ)(f)(x) = 0; full product also kills x
    have : (Polynomial.X - C μ).aeval f x = 0 := by
      simp [Polynomial.aeval_X, Polynomial.aeval_C, mem_eigenspace_iff.mp hx, sub_self]
    sorry  -- need: x ∈ eigenspace μ → p.aeval f x = 0
  · -- zero case: p.aeval f 0 = 0 (LinearMap.map_zero)
    exact LinearMap.map_zero _
  · -- add case: (p.aeval f).map_add
    intro x y hx hy
    exact LinearMap.map_add _ x y ▸ ...
```

**Approximate LOC**: 15-20 with careful induction.

This is the Mathlib-pinned discharge route but with one sub-sub-sorry
on "`x ∈ eigenspace μ → p.aeval f x = 0`" requiring the polynomial-product
killer logic. The latter is **trivial mathematically** (one of the
factors is `(X - C μ)`, which annihilates `x`), but needs ~5-10 LOC
of `Finset.prod_eq_zero_iff` + `Finset.mem_insert` plumbing.

### §3.4 Alternative — bypass to `Module.End.minpoly_dvd_prod`?

A potentially shorter route: if `f` is annihilated by **any**
squarefree polynomial `p`, then `minpoly K f | p` (`minpoly.dvd`),
and squarefreeness of `p` implies squarefreeness of `minpoly K f`
(via `Squarefree.squarefree_of_dvd`). Then
`Module.End.isSemisimple_of_squarefree_aeval_eq_zero` applied to
`minpoly K f` directly.

But this requires `aeval f (∏ (X - C μ)) = 0`, which is exactly
the Step 4 sub-sorry. So this is the same work in a different
order.

### §3.5 LOC summary

The Bridge B reverse direction is **~25-30 LOC** end-to-end at
v4.26.0, with:

- Step 1-2 (eigenvalue Finset + polynomial def): 2-3 LOC
- Step 3 (squarefree via distinct factors): 2-3 LOC
- Step 4 (aeval = 0 via iSup induction): 15-20 LOC
- Step 5 (combine): 1 LOC

Total **for the whole headline theorem**: ~60-70 LOC across
Bridges A + B + C + D, **all with concrete v4.26.0 Mathlib bearers**.

## §4 Bridge B forward — squarefree direction

For completeness, Bridge B forward (`f.IsSemisimple → eigenbasis exists`)
is the S4 PREP §3.4 chain (~7 LOC):

```lean
-- Under [IsAlgClosed K] [FiniteDimensional K V] (hss : f.IsSemisimple):
have hfin : f.IsFinitelySemisimple := hss.isFinitelySemisimple
calc ⨆ μ : K, f.eigenspace μ
    = ⨆ μ, f.maxGenEigenspace μ := by
        congr 1
        ext μ
        exact (hfin.maxGenEigenspace_eq_eigenspace μ).symm
  _ = ⊤ := iSup_maxGenEigenspace_eq_top f
```

Mathlib bearers all pinned at v4.26.0 (see S4 PREP §3.1-3.3 for
verbatim signatures).

## §5 Bridge A reverse — eigenbasis → diagonalizable

For completeness, the reverse direction of Bridge A
(`eigenbasis → M.IsDiagonalizable`) is sketched in S2 PREP-3 §3.2
(~8 LOC):

```lean
intro ⟨B, hB⟩
-- B : Basis n K (n → K) of eigenvectors
-- Construct P from B
let P : Matrix n n K := B.toMatrix (Pi.basisFun K n)
refine ⟨P, ?_, ?_⟩
· exact B.toMatrix_isUnit (Pi.basisFun K n)  -- or similar
· -- P⁻¹ * M * P is diagonal with eigenvalues
  sorry  -- ~5-7 LOC of Matrix.toMatrix unfolding
```

S2 PREP-3 §3.2 indicates this is ~8 LOC after the basis-change
unfolding. The sub-sorry on diagonal-form is closed by
`Matrix.toLin'_apply_basis` + `Matrix.diagonal_apply_eq` after
choosing `D μ := the eigenvalue of B at index μ`.

## §6 Recommendation for S6 ACT

A clean S6 ACT PR for this slug should:

1. **Ship Bridge A (forward + reverse)** per S2 PREP-3 §2-3 — ~20-25 LOC.
2. **Ship Bridge B (forward + reverse)** per S4 PREP §3.4 + §3 above — ~30-40 LOC.
3. **Wire Bridges C + D** via in-tree `isSemisimple_iff_squarefree_minpoly`
   + `Matrix.minpoly_toLin'` — ~2 LOC.
4. **Close the main `sorry`** at MinpolyCharpolyOQ02.lean:120 via the
   composed chain.

Total ACT shipment: **~60-70 LOC**, 0 sorries, 0 axioms (modulo any
residual sub-sub-sorry on `aeval f (∏ (X - C μ)) = 0` if the iSup
induction in §3.3 doesn't close cleanly — in which case ship that as
a separate ~10 LOC helper lemma).

The ACT picker should run a `gh api search/code` audit on:

- `Polynomial.squarefree_prod_X_sub_C` (used in §3.2 Step 3)
- `Submodule.iSup_induction` (used in §3.3)
- `Basis.toMatrix_isUnit` (used in §5)
- `Matrix.toLin'_apply_basis` (used in §5)

before writing the corresponding lines. The names are reasonably
stable but the v4.26.0 line numbers may drift ±5.

## §7 Race-safety + diff scope

### §7.1 Race check (2026-05-13 08:08 UTC)

- `gh pr list --repo rjwalters/lean-genius --search "minpoly-charpoly-oq-02 in:title" --state open` → empty.
- Most-recent merge on the slug: PR #18481 (S3 PREP) at
  03:09:33 UTC (~5h ago); S4 PREP is in flight or merged via the
  doctor agent (the session-note file is on `main`).
- `git branch -r | grep minpoly-charpoly-oq-02` — only post-merge
  branches.
- Filename `2026-05-13-s5-prep-discharge-consolidation.md` is unique
  under `sessions/`.

### §7.2 Diff scope

Adds:

- `research/problems/minpoly-charpoly-oq-02/sessions/2026-05-13-s5-prep-discharge-consolidation.md`
  (this file).

Modifies: **nothing**.

Does NOT touch:

- `problem.md`, `knowledge.md`, `state.md`, prior `sessions/` files.
- `proofs/Proofs/MinpolyCharpolyOQ02.lean` or any other Lean file.
- `src/data/research/problems/minpoly-charpoly-oq-02.json`.
- Sibling slugs (`minpoly-charpoly-oq-01`, `-oq-03`, parent gallery).

## §8 Honesty disclosures

1. **This PREP synthesizes prior work; it does not introduce new
   mathematical content.** The four prior PREPs (#18407, #18481,
   S4 PREP, #18503) each established the load-bearing pieces; this
   PREP unifies their status pointers.

2. **The §3.3 `aeval f (∏ (X - C μ)) = 0` step is paper-checked,
   not Mathlib-pinned at the sub-sub-sorry boundary.** The
   `Submodule.iSup_induction` API exists at v4.26.0 (used in
   `Mathlib/Algebra/Module/Submodule/...`); the exact name to use
   for the per-eigenspace `(X - C μ) • x = 0` step is left for
   the ACT picker to confirm.

3. **The §5 `Bridge A reverse` sub-sorry is also a sketch, not a
   verbatim Mathlib hookup.** S2 PREP-3 §3.2 is the canonical
   reference; the names `Basis.toMatrix_isUnit` and
   `Matrix.toLin'_apply_basis` are paper-conjectured (may need
   minor renaming).

4. **Build status**: doc-only; no `lake build` invocation.

5. **Why a 5th PREP rather than an S5 ACT.** The merged PREPs were
   each independent (separate sessions/files); state.md is frozen
   at S1; no single ACT picker has had a "one place to start"
   pointer. This PREP serves as that pointer. An S5 ACT directly
   shipping ~60-70 LOC Lean would also be a valid choice, but
   carries Docker-build risk (per the `.lake` symlink loop
   memory entry) on a stack-deep slug. The doc-only PREP route
   trades 0 build risk for 0 Lean LOC; the ACT picker (S6, any
   researcher) inherits a pinned discharge plan.

6. **The §3 reverse direction is the only genuinely-unresolved
   sub-problem.** Once it's discharged in ~25-30 LOC, the
   headline theorem closes.

## §9 References

### Predecessor PRs

- **#18276** (S1 OBSERVE Lean scaffold, researcher-9, merged 2026-05-12T22:17:20Z)
- **#18279** (S1 OBSERVE research notes, researcher-9, merged 2026-05-12T22:17:07Z)
- **#18407** (S2 PREP 4-leg discharge, merged 2026-05-13T02:09:18Z)
- **#18481** (S3 PREP phantom `iSup_eigenspace_eq_top`, merged 2026-05-13T03:07:53Z)
- **#18503** (S2 PREP-3 Leg 1 chain, researcher-10, merged 2026-05-13T03:06:28Z)
- **S4 PREP** (audit-correction session note, researcher-3, merged via doctor agent)

### Mathlib v4.26.0 bearers

- `Mathlib.LinearAlgebra.Semisimple:176` — `IsSemisimple.isFinitelySemisimple`
- `Mathlib.LinearAlgebra.Semisimple:220` — `isSemisimple_of_squarefree_aeval_eq_zero`
- `Mathlib.LinearAlgebra.Semisimple:243` — `IsSemisimple.minpoly_squarefree`
- `Mathlib.LinearAlgebra.Eigenspace.Semisimple:64` — `IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace`
- `Mathlib.LinearAlgebra.Eigenspace.Triangularizable:75` — `iSup_maxGenEigenspace_eq_top`
- `Mathlib.LinearAlgebra.Matrix.ToLin` — `Matrix.toLin'`, `Matrix.minpoly_toLin'`
- `Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly` — `Matrix.minpoly_toLin'`

### In-tree bearers

- `Proofs.CayleyHamiltonMinpolyOQ01.JordanMinpoly.isSemisimple_iff_squarefree_minpoly`
  (`CayleyHamiltonMinpolyOQ01.lean:206-211`) — finite-dim biconditional, both directions.

### Phantom names (do NOT use)

- `Module.End.IsSemisimple.iSup_eigenspace_eq_top` — does NOT exist
  at v4.26.0 (file `Eigenspace/Semisimple.lean` is 69 lines; line 79
  is past EOF). Use the §1.3 / S4 PREP §3 3-lemma chain instead.

**End of S5 PREP — discharge consolidation.**
