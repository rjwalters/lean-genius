# S7 PREP — OQ-03-OQ-01 S2 discharge of `xModule_isTorsionBy_charpoly`

**Date**: 2026-05-12
**Agent**: researcher-5
**Mode**: PREP (doc-only)
**Parent slug**: `minpoly-charpoly-oq-03`
**Child slug touched (read-only)**: `minpoly-charpoly-oq-03-oq-01`
**Phase**: parent-level state.md "Next Action" **option 1** — discharge
`xModule_isTorsionBy_charpoly` in PR #17995's now-merged
`MinpolyCharpolyOQ03OQ01.lean`.

## 1. Why this memo (and why doc-only)

The parent slug `minpoly-charpoly-oq-03` has two PRs in flight:

* PR #18182 (S5 — `prodFactors_natDegree_le_lastFactor_natDegree_mul`,
  build pending) — touches `Proofs/MinpolyCharpolyOQ03.lean`.
* PR #18425 (S6 PREP — firstFactor-side mirror design, doc-only) —
  creates one new session file in `sessions/`.

Both PRs operate on the parent's `InvariantFactorChain` API surface.
The state.md "Next Action" enumerates four options for the next ACT
iteration; PR #18425 ships **option 4 bullet 2**. The remaining
options are:

* **Option 1** — discharge `xModule_isTorsionBy_charpoly` in the
  child slug's file (this memo).
* **Option 2** — strong-form upgrade of `rational_canonical_form_exists`
  (5-line statement-only edit).
* **Option 3** — OQ-03-OQ-02 SCAFFOLD (~300 LOC, new file).

This memo locks Mathlib API surface, proof sketch, anti-targets, and
a ~30-LOC delta budget for **option 1** *before* S2 ACT lands, so that
when a future researcher claims this slug and routes to OQ-03-OQ-01
discharge, the design work is already done. Doc-only deliverable; no
race against PR #18182 (different file) or PR #18425 (different
file).

## 2. Target lemma (verbatim from `MinpolyCharpolyOQ03OQ01.lean:127–132`)

```lean
/-- The characteristic polynomial of `M` annihilates every element of
    the `F[X]`-module `xModule M`. This is Cayley–Hamilton transported
    to the `Module.AEval'` synonym. -/
theorem xModule_isTorsionBy_charpoly (M : Matrix n n F) :
    Module.IsTorsionBy F[X] (xModule M) M.charpoly := by
  sorry
```

Statement is **fixed** (PR #17995 merged). S2 ACT replaces the `by sorry`
body with a discharge of ~6 tactic lines (see §5).

`endo M = M.mulVecLin` (line 95 of the same file).
`xModule M = Module.AEval' (endo M)` (line 100).

## 3. Mathlib API audit (pinned rev `2df2f0150c27`, Mathlib v4.26.0)

All four lemmas below are confirmed at the lakefile-pinned revision via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c27`.

### 3.1 `LinearMap.aeval_self_charpoly`

`Mathlib/LinearAlgebra/Charpoly/Basic.lean:90`:

```lean
theorem aeval_self_charpoly : aeval f f.charpoly = 0 := by
  apply (LinearEquiv.map_eq_zero_iff (algEquivMatrix (chooseBasis R M)).toLinearEquiv).1
  rw [AlgEquiv.toLinearEquiv_apply, ← AlgEquiv.coe_algHom, ← Polynomial.aeval_algHom_apply _ _ _,
    charpoly_def]
  exact Matrix.aeval_self_charpoly _
```

**Hypothesis surface**: `{R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
[Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M)`.

For our use site, `R = F` (a field) and `M = (n → F)` with `n : Fintype + DecidableEq`.
`Module.Free F (n → F)` and `Module.Finite F (n → F)` are auto-instances from the
standard-basis `Pi.basisFun`. No manual instance plumbing required.

**Conclusion**: `aeval (endo M) (endo M).charpoly = 0` is a one-line term.

### 3.2 `Matrix.charpoly_mulVecLin`

`Mathlib/LinearAlgebra/Charpoly/ToMatrix.lean:98`:

```lean
@[simp]
theorem charpoly_mulVecLin (A : Matrix n n R) : A.mulVecLin.charpoly = A.charpoly :=
  charpoly_toLin' A
```

**Hypothesis surface**: `{R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]`.

**Conclusion**: bridges the matrix-level `M.charpoly` with the linear-map-level
`(endo M).charpoly = M.mulVecLin.charpoly`. This is the **one rewrite** that
turns `LinearMap.aeval_self_charpoly` into the form `aeval (endo M) M.charpoly = 0`.

**Important**: `@[simp]` means a bare `simp` (or `simp only [Matrix.charpoly_mulVecLin]`)
will close the rewrite. Equivalently, `(charpoly_mulVecLin M).symm` is the explicit
`Eq` for `rw`.

### 3.3 `Module.AEval.of_symm_smul`

`Mathlib/Algebra/Polynomial/Module/AEval.lean:72–73`:

```lean
@[simp] lemma of_symm_smul (f : R[X]) (m : AEval R M a) :
    (of R M a).symm (f • m) = aeval a f • (of R M a).symm m := rfl
```

`rfl` — definitionally equal, no proof obligation. Tagged `@[simp]`.

This is the **load-bearing reduction**: applying `(AEval.of _).symm` to a
polynomial-action goal converts `f • x` into `aeval _ f • _`, where the RHS smul
is the underlying module action.

For `AEval'`, `AEval'.of φ : M ≃ₗ[R] AEval' φ` is `AEval.of R M φ`
(line 198), so `AEval.of_symm_smul` applies directly.

### 3.4 `Module.AEval.of_aeval_smul`

`Mathlib/Algebra/Polynomial/Module/AEval.lean:70`:

```lean
lemma of_aeval_smul (f : R[X]) (m : M) : of R M a (aeval a f • m) = f • of R M a m := rfl
```

`rfl` again. The **forward** direction: if `aeval a f • m_original = 0` on the
underlying `M`, then `f • (of R M a m_original) = of R M a 0 = 0` in `AEval`.

For our use site, "underlying `M`" is `(n → F)` and "underlying smul" is
the `Module.End F (n → F)` action on `(n → F)` — i.e., function application,
since `AEval'` specializes `A = M →ₗ[R] M`. Thus `aeval (endo M) f` is a
`Module.End F (n → F)`, and `aeval (endo M) f • m_orig` is
`(aeval (endo M) f) m_orig` (LinearMap application).

## 4. Action-unfolding lemma chain (for reference)

The `AEval'` module structure layers three smuls:

```
f : F[X]       acts on  xModule M
              via       Module.AEval.instModulePolynomial = compHom · (aeval (endo M)).toRingHom
              
aeval (endo M) f : Module.End F (n → F)
              acts on  AEval' (endo M)  (= type-equal to (n → F))
              via      the End-as-A-module structure of (n → F)
              
((aeval (endo M) f) : End) y : (n → F)
              =   (aeval (endo M) f).toFun y
              =   LinearMap function application
```

Schematically: `f • x = aeval (endo M) f • x = (aeval (endo M) f) x` (the last
equality is `LinearMap.smul_def` / `Module.End.smul_def`).

For the discharge it suffices to know that *every* layer reduces to
`(aeval (endo M) f) x`, and if `aeval (endo M) f = 0` as a linear map, then
applied to any `x` it gives `0`. **No manual smul-tower unfolding is required**
because `of_symm_smul` collapses the chain in one rewrite.

## 5. Proof sketch (target: ≤8 tactic lines)

### 5.1 Primary route (preferred)

```lean
theorem xModule_isTorsionBy_charpoly (M : Matrix n n F) :
    Module.IsTorsionBy F[X] (xModule M) M.charpoly := by
  -- M.charpoly = (endo M).charpoly  via  Matrix.charpoly_mulVecLin
  -- Substitute to land at LinearMap.aeval_self_charpoly's exact form.
  intro x
  have hC : (endo M).charpoly = M.charpoly := charpoly_mulVecLin M
  -- Goal: M.charpoly • x = 0  in  xModule M
  -- Reduce via injectivity of (AEval'.of (endo M)).symm:
  apply (AEval'.of (endo M)).symm.injective
  rw [Module.AEval.of_symm_smul, ← hC, LinearMap.aeval_self_charpoly]
  -- Goal: (0 : Module.End F (n → F)) • _ = (AEval'.of (endo M)).symm 0
  simp
```

**Line count**: 6 tactic lines + 1 `have` (= 7 total). Within the
`≤8` budget.

### 5.2 Alternate route (term mode via `of_aeval_smul`)

```lean
theorem xModule_isTorsionBy_charpoly (M : Matrix n n F) :
    Module.IsTorsionBy F[X] (xModule M) M.charpoly := fun x => by
  -- Express x as AEval'.of (endo M) y for some y : (n → F).
  obtain ⟨y, rfl⟩ := (AEval'.of (endo M)).surjective x
  -- Goal: M.charpoly • AEval'.of (endo M) y = 0
  rw [← Module.AEval.of_aeval_smul, ← charpoly_mulVecLin,
      LinearMap.aeval_self_charpoly]
  -- Goal: AEval'.of (endo M) ((0 : Module.End F (n → F)) • y) = 0
  simp
```

**Line count**: 4 tactic lines (3 if `simp` is replaced by `rfl`-chase).

Primary route is preferred for readability; alternate is a safety net if
`AEval'.of … .symm.injective` triggers an elaboration slowdown.

### 5.3 Fallback (in case both routes break)

The `IsTorsionBy` definition unfolds to `∀ ⦃x⦄, M.charpoly • x = 0` (line 211
of `Torsion/Basic.lean`). The least-magical proof:

```lean
theorem xModule_isTorsionBy_charpoly (M : Matrix n n F) :
    Module.IsTorsionBy F[X] (xModule M) M.charpoly := by
  intro x
  -- Convert to the original M-module side via the AEval' inverse.
  let y := (AEval'.of (endo M)).symm x
  -- The action f • x in AEval' unfolds to (aeval (endo M) f) acting on y.
  -- aeval (endo M) M.charpoly = 0  by LinearMap.aeval_self_charpoly + charpoly_mulVecLin.
  show M.charpoly • x = (0 : xModule M)
  rw [show M.charpoly • x = (AEval'.of (endo M))
      ((aeval (endo M) M.charpoly) y) from ?_,
      show aeval (endo M) M.charpoly = 0 from ?_]
  · simp
  · rw [← charpoly_mulVecLin]; exact LinearMap.aeval_self_charpoly _
  · -- The smul-reduction step: f • of φ y = of φ (aeval φ f • y), and on M = (n→F)
    -- with End-as-A action, aeval-smul = aeval-apply.
    rfl
```

Larger (~10 lines), but every step is mechanical. Use only if §5.1 and §5.2
break against unexpected `compHom`/`SMul` diamonds.

## 6. LOC delta budget

| Region | Δ lines | Status |
|---|---|---|
| `xModule_isTorsionBy_charpoly` body | +5–7 (replace `by sorry`) | S2 ACT target |
| New `have hC` or top-level lemma | 0–1 | inline |
| New imports | 0 | already imported by S1 scaffold |
| Top docstring (3.1 audit reference) | optional, +3 | nice-to-have |
| **Total** | **~6–10 LOC** | within "≤30 lines" S2 estimate |

The OQ-03-OQ-01 state.md estimates 30–50 LOC for the S2 discharge. With
the API audit done in this memo, the actual delivery should sit comfortably
at the ~6–10 LOC end of that range. The estimate accounted for unknown
smul-diamond resolution; the audit confirms `of_symm_smul` is `rfl`, so the
diamond is illusory.

## 7. Mathlib drift risk (v4.26.0 pinned rev)

Pinned revision is `2df2f0150c27` (lake-manifest.json). At this rev:

* `LinearMap.aeval_self_charpoly` — confirmed at line 90 of
  `Mathlib/LinearAlgebra/Charpoly/Basic.lean?ref=2df2f0150c27`.
* `Matrix.charpoly_mulVecLin` — confirmed at line 98 of
  `Mathlib/LinearAlgebra/Charpoly/ToMatrix.lean?ref=2df2f0150c27`. `@[simp]`.
* `Module.AEval.of_symm_smul` — confirmed at line 72 of
  `Mathlib/Algebra/Polynomial/Module/AEval.lean?ref=2df2f0150c27`.
  Implementation is `rfl` (line 73). `@[simp]`.
* `Module.AEval.of_aeval_smul` — confirmed at line 70 of the same file.
  Implementation is `rfl`.

**No drift risk identified.** All four lemmas are present and have the same
signatures as documented in this memo.

The drift risk that bit S5 (`List.length_pos.mpr` renamed in v4.26.0) was a
deprecated-name issue. The four lemmas above are core API on heavily-used
modules (`AEval`, `Matrix.Charpoly`) and are not deprecation candidates.

## 8. Anti-targets (what S2 ACT must NOT do)

8.1 **Do NOT modify `xModule M`, `endo M`, or any definition.** The S1
    scaffold's API surface is final and consumed by OQ-03-OQ-02. Changing
    `endo` to e.g. `Matrix.toLin'` would race against the scaffold's
    docstring promises.

8.2 **Do NOT discharge `xModule_isTorsion` (the wrapper theorem) at the
    same time.** That's a separate ~10-line discharge (use `isTorsion_iff`
    + monic-ne-zero + `IsDomain F[X]`). Keeping it separate makes the
    PR diff reviewable.

8.3 **Do NOT add a `xModule_charpoly_eq` lemma like
    `(endo M).charpoly = M.charpoly`.** That's `Matrix.charpoly_mulVecLin`
    by another name — adding a wrapper is mere indirection.

8.4 **Do NOT discharge `xModule_has_invariantFactorChain`.** That's
    OQ-03-OQ-02's deliverable.

8.5 **Do NOT modify any `Proofs/MinpolyCharpolyOQ03.lean` (parent file)
    surface.** PR #18182 (S5) is in flight on this file. Edits here would
    cause a merge conflict.

8.6 **Do NOT touch `meta.json` / gallery files.** No theorem-count drift
    from this discharge — the public theorem count of
    `MinpolyCharpolyOQ03OQ01.lean` is unchanged; only the sorry count drops
    by 1 (S1's 3 sorries → 2).

8.7 **Do NOT add `import Mathlib.LinearAlgebra.Charpoly.ToMatrix` if it's
    already pulled in by another import.** Verify with
    `grep "import" proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean` first;
    `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic` already pulls in the
    LinearMap charpoly via transitive imports — confirm before adding.

8.8 **Do NOT extend `problem.md` / `state.md` / `knowledge.md` of the
    parent slug from this branch.** S2 ACT will own that update.

## 9. Conflict-free guarantee

This PR creates **one file in a new path** (`sessions/` subdir of the
parent slug). The path is:

```
research/problems/minpoly-charpoly-oq-03/sessions/2026-05-12-s07-prep-oq03-oq01-s2-isTorsionBy-discharge.md
```

PR #18425's session file:

```
research/problems/minpoly-charpoly-oq-03/sessions/2026-05-12-s06-prep-firstfactor-mirror-design.md
```

Different filenames; the `sessions/` directory is shared (and is created
in this PR — the worktree currently lacks it, so PR #18425 will also
create it independently). git auto-merges directory creation; no
conflict.

PR #18182's surface is `Proofs/MinpolyCharpolyOQ03.lean` — entirely
disjoint from `sessions/`.

PR #18407 (sibling slug `minpoly-charpoly-oq-02` S2 PREP) operates under
`research/problems/minpoly-charpoly-oq-02/` — different slug, no overlap.

Files NOT touched by this PR:

* `proofs/Proofs/MinpolyCharpolyOQ03.lean` (parent Lean file)
* `proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean` (child Lean file)
* `proofs/Proofs/MinpolyCharpolyOQ02.lean` (sibling Lean file)
* `src/data/proofs/minpoly-charpoly-oq-03/*` (parent gallery)
* `src/data/proofs/minpoly-charpoly-oq-03-oq-01/*` (child gallery)
* `src/data/research/problems/minpoly-charpoly-oq-03.json` (parent knowledge)
* `src/data/research/problems/minpoly-charpoly-oq-03-oq-01.json` (child knowledge)
* `research/problems/minpoly-charpoly-oq-03/problem.md`
* `research/problems/minpoly-charpoly-oq-03/state.md`
* `research/problems/minpoly-charpoly-oq-03-oq-01/problem.md`
* `research/problems/minpoly-charpoly-oq-03-oq-01/state.md`

## 10. Cheat-sheet for S2 ACT implementer

When the next researcher claims the parent slug (or directly
`minpoly-charpoly-oq-03-oq-01`) and routes to "discharge
`xModule_isTorsionBy_charpoly`", they should:

1. **Open** `proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean` to line 127–132.

2. **Confirm imports** at the file's top include:
   - `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic` (already present, gives
     `Matrix.charpoly_mulVecLin` via
     `Mathlib.LinearAlgebra.Charpoly.ToMatrix` transitively)
   - `Mathlib.Algebra.Polynomial.Module.AEval` (already present)

3. **Replace** the `by sorry` body with the primary route from §5.1:

   ```lean
   theorem xModule_isTorsionBy_charpoly (M : Matrix n n F) :
       Module.IsTorsionBy F[X] (xModule M) M.charpoly := by
     intro x
     have hC : (endo M).charpoly = M.charpoly := charpoly_mulVecLin M
     apply (AEval'.of (endo M)).symm.injective
     rw [Module.AEval.of_symm_smul, ← hC, LinearMap.aeval_self_charpoly]
     simp
   ```

4. **If §5.1 fails**, fall back to §5.2 (term-mode via `of_aeval_smul`).

5. **If both fail**, use §5.3 (explicit smul-tower unfold).

6. **Do NOT also discharge** `xModule_isTorsion` or
   `xModule_has_invariantFactorChain` in the same PR. Separate concerns
   keep the diff reviewable. Those are S3 ACT and OQ-03-OQ-02 SCAFFOLD
   territory respectively.

7. **PR title pattern**: `research(minpoly-charpoly-oq-03-oq-01): S2 ACT —
   discharge xModule_isTorsionBy_charpoly (Cayley-Hamilton via AEval')`.

8. **Build**: `./proofs/scripts/docker-build.sh Proofs.MinpolyCharpolyOQ03OQ01`
   (~30–45 min Docker cold). Build-pending PRs land per convention.

9. **Meta updates**: `proofs.MinpolyCharpolyOQ03OQ01` linecount delta +5
   to +10; theoremCount unchanged; sorryCount −1.

10. **Knowledge JSON**: append to
    `src/data/research/problems/minpoly-charpoly-oq-03-oq-01.json`'s
    `knowledge.builtItems`:
    `"xModule_isTorsionBy_charpoly (theorem, S2 ACT, unconditional):
    discharges S1 sorry via Module.AEval.of_symm_smul +
    Matrix.charpoly_mulVecLin + LinearMap.aeval_self_charpoly. ~6 tactic
    lines."`.

## 11. Honesty assessment

* **Mathematical content of S2 ACT**: zero new mathematics. Pure Mathlib
  API plumbing. The Cayley-Hamilton theorem is fully in Mathlib; we are
  transporting its statement across one definitional `rfl` chain.
* **Significance**: low-to-medium. Discharges one of three sorries in
  `MinpolyCharpolyOQ03OQ01.lean`. The remaining two (`xModule_isTorsion`
  and `xModule_has_invariantFactorChain`) are mechanically derivable once
  this one lands.
* **Originality**: none — this is the standard "Cayley-Hamilton on the
  polynomial-action module" lemma every linear-algebra textbook covers
  when motivating rational canonical form.
* **What this memo claims**: it locks the Mathlib API surface for the
  discharge so the implementer does not re-derive it. That's the entire
  value-add. ~6 LOC of S2 ACT Lean is the actual mathematical content.

## 12. Knowledge propagation candidates

After S2 ACT lands, the discharge pattern (`of_symm_smul` + algebra-hom
naturality + `aeval_self_charpoly`) generalizes to **any** matrix-module
torsion proof. Candidate downstream uses:

* `cayley-hamilton-minpoly-oq-*` family (any "M acts on K^n via minpoly"
  derivation).
* Any sibling `*-charpoly-*` slug that needs to lift CH from matrices
  to the AEval' module side.

Mention this in the S2 ACT PR body as a forward-reference; the actual
generalization belongs to a future "AEval' Cayley-Hamilton transport
lemma" infrastructure PR (out of scope here).

## Appendix A: Verification commands

```bash
# Confirm Mathlib lemma signatures at pinned rev:
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/Charpoly/Basic.lean?ref=2df2f0150c27' --jq '.content' | base64 -d | grep -n -A 3 'aeval_self_charpoly'
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/Charpoly/ToMatrix.lean?ref=2df2f0150c27' --jq '.content' | base64 -d | grep -n -A 1 'charpoly_mulVecLin'
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Polynomial/Module/AEval.lean?ref=2df2f0150c27' --jq '.content' | base64 -d | grep -n 'of_symm_smul\|of_aeval_smul'

# Confirm pinned Mathlib rev:
jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json
```
