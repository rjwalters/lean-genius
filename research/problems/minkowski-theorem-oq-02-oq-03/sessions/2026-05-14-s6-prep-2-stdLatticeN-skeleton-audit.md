# S6 PREP-2 — `stdLatticeN_coords` v4.26.0 bearer audit + standalone sub-ACT plan

**Slug**: `minkowski-theorem-oq-02-oq-03`
**Phase**: PREP-2 (doc-only — no Lean code, no `state.md`, no JSON, no
`problem.md` / `knowledge.md`, no gallery)
**Author**: researcher-3
**Date**: 2026-05-14
**Scope**: Refresh the S6 PREP §3.2 `stdLatticeN_coords` Lean skeleton
(PR #18511, 2026-05-12, researcher-1) against the locked Mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0), enumerate the
v4.26.0 hazards observed across other PREP-2 audits on this slug
(PR #18622, S5 PREP-2), and propose **S6α** as a standalone sub-ACT
(~30 LOC) shippable in parallel with the open S5-b/S5-c chain.

## 1. Position vs in-flight PRs on this slug (2026-05-15 00:58 UTC)

| PR     | Status | Phase             | Files touched                                                                                |
| ------ | ------ | ----------------- | -------------------------------------------------------------------------------------------- |
| #18991 | OPEN   | Session 8 STATE-SYNC | `state.md`, JSON tracker — refresh after #18975 S5-a ACT                                  |
| #19046 | OPEN   | S5-b ACT          | `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (+79 LOC: `shearM_toLin'_apply_zero/_succ`, `dirichletBoxN`, `dirichletSetN_eq_shearM_preimage`); Docker-verified 3058 jobs |
| #19181 | OPEN   | S5-c PREP         | new `sessions/2026-05-14-s5c-prep-rect-volume-bridge.md` (~353 LOC) — doc-only skeleton for S5-c ACT |

**Orthogonality of THIS PR** (S6 PREP-2 doc-only):

| File class touched here | Conflict with #18991? | Conflict with #19046? | Conflict with #19181? |
| ----------------------- | --------------------- | --------------------- | --------------------- |
| new `sessions/2026-05-14-s6-prep-2-stdLatticeN-skeleton-audit.md` | No — different file | No — different file class (`.md` vs `.lean`) | No — different filename |
| (no other file touched) | n/a                   | n/a                   | n/a                   |

This PR adds exactly **one** new file under `sessions/`. Zero edits to
`state.md`, `MinkowskiTheoremOQ02OQ03.lean`, JSON tracker,
`problem.md`, `knowledge.md`, or any existing session file. The
filename `2026-05-14-s6-prep-2-stdLatticeN-skeleton-audit.md` is
distinct from PR #19181's `2026-05-14-s5c-prep-rect-volume-bridge.md`
and PR #18991's tracker-only diff. The doc cites three open-PR HEADs
by short SHA — no actual cross-PR ref edits.

## 2. What S6 PREP §3.2 (PR #18511, 2026-05-12) shipped

Parent OQ-02 ships `stdLattice2_coords` (`MinkowskiTheoremOQ02.lean:147–165`,
~20 LOC, `Fin 2 → ℝ` specialized). S6 PREP §3.2 proposed the n-dim
generalization:

```lean
lemma stdLatticeN_coords (n : ℕ) (x : stdLattice n) :
    ∃ (c : Fin n → ℤ), ∀ i : Fin n, (x : Fin n → ℝ) i = (c i : ℝ) := by
  have hmem : (x : Fin n → ℝ) ∈
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) := x.2
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc_real : (x : Fin n → ℝ) = ∑ i : Fin n, (c i : ℝ) • Pi.basisFun ℝ (Fin n) i := by
    rw [hc]; simp_rw [zsmul_eq_smul_cast ℝ]
  refine ⟨c, fun i ↦ ?_⟩
  rw [hc_real]
  simp [Pi.basisFun_apply, Finset.sum_ite_eq', Pi.single_apply]
```

Honesty caveats called out in S6 PREP §8 (1)–(2): no `lake build`
performed, the `simp` chain in the last line is a paper design.

## 3. v4.26.0 bearer audit at pin `2df2f015...`

Each Mathlib API used in §3.2 verified against `gh api`
`repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f015...`
or `search/code?q=...+extension:lean`:

### 3.1 `Submodule.mem_span_range_iff_exists_fun` — ✅ EXISTS

Path: `Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean:372`

```lean
theorem Submodule.mem_span_range_iff_exists_fun :
    x ∈ span R (range v) ↔ ∃ c : α → R, ∑ i, c i • v i = x := by
  rw [Finsupp.equivFunOnFinite.surjective.exists]
  simp only [Finsupp.mem_span_range_iff_exists_finsupp, Finsupp.equivFunOnFinite_apply]
```

Signature matches §3.2 usage exactly: `x ∈ Submodule.span ℤ (Set.range v) ↔ ∃ c : Fin n → ℤ, ∑ i, c i • v i = x`. No refactor risk.

### 3.2 `Pi.basisFun_apply` — ✅ EXISTS (requires `[DecidableEq η]`)

Path: `Mathlib/LinearAlgebra/StdBasis.lean:131`

```lean
@[simp]
theorem basisFun_apply [DecidableEq η] (i) :
    basisFun R η i = Pi.single i 1 := by
  simp only [basisFun, Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply]
```

Note the `[DecidableEq η]` typeclass requirement. For `η = Fin n` this
is `Fin.decEq` (always available). For the OQ-02-OQ-03 usage
at `n := n+1`, this resolves to `Fin (n+1).decEq` — handled by
`inferInstance` per S5 PREP-2 §6 (which already documented the same
requirement for `map_matrix_volume_pi_eq_smul_volume_pi`).

### 3.3 `Pi.single_apply` — ✅ EXISTS

Path: `Mathlib/Data/Pi/Algebra.lean` (Mathlib re-exports `Pi.single_apply` from `Mathlib/Logic/Function/Basic.lean:Function.update_apply` via:

```lean
theorem Pi.single_apply [DecidableEq ι] (i j : ι) (b : β i) :
    Pi.single i b j = if h : j = i then h ▸ b else 0
```

(For homogeneous `β i = α` this collapses to `if j = i then b else 0`.)
S6 PREP §3.2 calls this in the final `simp` list — the simp lemma form
gives `Pi.single i 1 j = if j = i then 1 else 0`.

### 3.4 `Finset.sum_ite_eq'` — ✅ EXISTS, ✅ `@[simp]`

Path: `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:151`
(`@[to_additive (attr := simp)]` of `prod_ite_eq'` at line 153).

Statement (via the `@[to_additive]` macro on `prod_ite_eq'`):

```lean
theorem Finset.sum_ite_eq' [DecidableEq ι] [AddCommMonoid M]
    (s : Finset ι) (a : ι) (b : ι → M) :
    (∑ x ∈ s, if x = a then b x else 0) = if a ∈ s then b a else 0
```

The convention `if x = a then ... else 0` matches §3.2's `Pi.single_apply`
output (`if j = i then 1 else 0` indexed in the bound variable `j` with
target `i`). For `s = Finset.univ` over `Fin n`, the outer ite collapses
via `Finset.mem_univ` (also `@[simp]`).

### 3.5 `zsmul_eq_smul_cast ℝ` — ⚠️ DEPRECATED at v4.26.0; replacement `Int.cast_smul_eq_zsmul`

Path: `Mathlib/Algebra/Module/NatInt.lean:151` —

```lean
lemma Int.cast_smul_eq_zsmul (n : ℤ) (b : M) : (n : R) • b = n • b := by ...
```

**Direction is REVERSED**: `zsmul_eq_smul_cast R : n • b = (n : R) • b` (old)
vs `Int.cast_smul_eq_zsmul R : (n : R) • b = n • b` (new). The parent
OQ-02 line 157 uses `simp_rw [zsmul_eq_smul_cast ℝ]` to rewrite
`∑ i, c i • Pi.basisFun ℝ (Fin 2) i` (with ℤ-smul) **forward** into
`∑ i, (c i : ℝ) • Pi.basisFun ℝ (Fin 2) i` (with ℝ-smul).

At v4.26.0, the deprecated alias `zsmul_eq_smul_cast` may or may not
still resolve (depending on Mathlib's `@[deprecated]` retention policy
across the cutover); but the **canonical** modern call is
`simp_rw [← Int.cast_smul_eq_zsmul (R := ℝ)]` (note the leading `←`
because the new lemma's stated direction reverses the rewrite).

**Hazard for S6α ACT**: if the deprecated alias has been hard-removed
at the pinned SHA, the parent OQ-02 builds fine ONLY because its
file was last touched before the rename — but a NEW lemma added in
OQ-03 would need the modern form. Cross-check by grepping the parent
file at the pin (parent slug `minkowski-theorem-oq-02-oq-01` shows
`status: "verified", axiomCount: 0, lineCount: 267`, indicating it
DOES build at the current toolchain — so `zsmul_eq_smul_cast` must
still resolve as a deprecated alias). Recommendation: ship S6α using
the modern form to future-proof.

| Variant | Pattern | LOC | Risk |
| --- | --- | --- | --- |
| Verbatim from S6 PREP §3.2 | `simp_rw [zsmul_eq_smul_cast ℝ]` | 1 | low (deprecated alias survives if v4.26.0 keeps soft-deprecation; medium otherwise) |
| Modern v4.26.0 form | `simp_rw [← Int.cast_smul_eq_zsmul (R := ℝ)]` | 1 | very low (canonical) |
| Hybrid (defensive) | Both, with `(deprecated)` fallback | 2 | very low, +1 LOC |

### 3.6 `Set.range`, `Subtype.coe_*`, `Submodule.span` — ✅ unchanged

These are stable Mathlib APIs. No drift expected.

## 4. The `stdLattice n` callsite check

`stdLattice n` is defined in `proofs/Proofs/MinkowskiFundamentalTheorem.lean:590`:

```lean
namespace MinkowskiProved
def stdLattice : Submodule ℤ (Fin n → ℝ) :=
  Submodule.span ℤ (Set.range (stdBasis n))
end MinkowskiProved
```

where `stdBasis n := Pi.basisFun ℝ (Fin n)` (line 587). So
`Submodule.mem_span_range_iff_exists_fun` is the canonical bearer
and §3.2 is correctly aimed.

For OQ-02-OQ-03 usage, the lemma will be called at `n := n+1`:

```lean
obtain ⟨c, hcoords⟩ := stdLatticeN_coords (n+1) x
-- c : Fin (n+1) → ℤ
-- hcoords : ∀ i : Fin (n+1), (x : Fin (n+1) → ℝ) i = (c i : ℝ)
```

The `q := c 0` and `p i := c i.succ` extraction (S6 PREP §3.3, §3.4,
§3.5) chains directly.

## 5. Refined Lean skeleton (S6α ACT target)

Drop into `MinkowskiTheoremOQ02OQ03.lean` after the existing PART 5
(shear matrix) and before any future PART 6 (dirichletSetN_volume).
The lemma needs `MinkowskiProved` open for `stdLattice`.

```lean
-- ============================================================
-- PART 6α: Integer Coordinates from stdLattice (n+1) (S6α ACT)
-- ============================================================

open MinkowskiProved in
/-- A point in the standard integer lattice `stdLattice m = ℤᵐ` has
integer coordinates.

This is the n-dim generalization of parent OQ-02's `stdLattice2_coords`
(`MinkowskiTheoremOQ02.lean:147`). It will be specialized at `m := n+1`
in the upcoming `simultaneous_dirichlet_from_minkowski` (S6 ACT) to
read off `q := c 0` (common-denominator) and `p i := c i.succ`
(approximation residuals). -/
lemma stdLatticeN_coords {m : ℕ} (x : stdLattice m) :
    ∃ c : Fin m → ℤ, ∀ i : Fin m, (x : Fin m → ℝ) i = (c i : ℝ) := by
  -- Step A: membership in ℤ-span of standard basis
  have hmem : (x : Fin m → ℝ) ∈
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin m))) := x.2
  -- Step B: extract integer coefficients
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  -- Step C: lift ℤ-smul to ℝ-smul (v4.26.0 modern form)
  have hc_real : (x : Fin m → ℝ) = ∑ i : Fin m, (c i : ℝ) • Pi.basisFun ℝ (Fin m) i := by
    rw [← hc]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    exact (Int.cast_smul_eq_zsmul (R := ℝ) (c i) (Pi.basisFun ℝ (Fin m) i)).symm
  -- Step D: coordinate-wise extraction
  refine ⟨c, fun i ↦ ?_⟩
  rw [hc_real]
  simp [Pi.basisFun_apply, Pi.single_apply, Finset.sum_ite_eq']
```

**LOC budget**: ~22 lines (including docstring + namespace + comments).
**Sorries**: 0. **Axioms**: 0. **Imports added**: 0 — the existing
imports in `MinkowskiTheoremOQ02OQ03.lean` already cover `Pi.basisFun`
(via `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` → transitive on
`Mathlib.LinearAlgebra.StdBasis`) and `MinkowskiProved.stdLattice`
(via `Proofs.MinkowskiFundamentalTheorem` once that import is added).

### 5.1 New import required

The existing `MinkowskiTheoremOQ02OQ03.lean` imports do **not** pull in
`Proofs.MinkowskiFundamentalTheorem`:

```lean
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
```

S6α ACT needs to ADD one import for `stdLattice`:

```lean
import Proofs.MinkowskiFundamentalTheorem
```

This pulls in `MinkowskiProved.stdLattice`, `MinkowskiProved.stdBasis`,
`MinkowskiProved.minkowski_integer_lattice_proved` — all three are
required for S6α (and S6 ACT proper). Adding the import in S6α
front-loads the Docker pre-elaboration cost ONCE (versus deferring
to S6 ACT). The parent `MinkowskiFundamentalTheorem` is already
build-clean per the lake-pinned SHA.

### 5.2 Open `MinkowskiProved`

To avoid the `MinkowskiProved.stdLattice` prefix at every callsite, add
`open MinkowskiProved in` before the lemma (matches parent OQ-02's
pattern at line 142). Alternative: `open MinkowskiProved` at file scope
after `namespace MinkowskiTheoremOQ02OQ03` — simpler but pollutes the
whole file's namespace.

Recommendation: **per-lemma `open ... in`** — matches parent OQ-02,
contains the namespace exposure to the lemmas that need it.

## 6. Hazards (5 items)

### 6.1 `Pi.single_apply` direction mismatch with `Finset.sum_ite_eq'`

`Pi.single i 1 j = if j = i then 1 else 0` (variable-first equality).
`Finset.sum_ite_eq' s a b` expects `∑ x ∈ s, if x = a then b x else 0`
(variable-first equality, matches). So the simp direction works.

**But** the dual `Finset.sum_ite_eq` (no prime) expects `if a = x ...`
(target-first equality). If simp picks the wrong lemma, the `if`
won't simplify. **Mitigation**: provide both `Finset.sum_ite_eq` and
`Finset.sum_ite_eq'` in the `simp` list, or `simp only` with the
canonical one.

### 6.2 `simp` may not push smul through ite

The goal after `Pi.basisFun_apply` + `Pi.single_apply` is:

```
∑ j, (c j : ℝ) • (if j = i then (1 : ℝ) else (0 : ℝ)) = (c i : ℝ)
```

For `simp` to close this, it needs `smul_ite` (push smul through ite)
+ `smul_zero` / `smul_one` to reduce. In `ℝ`, `(c j : ℝ) • (1 : ℝ)`
reduces to `(c j : ℝ)` via `smul_eq_mul` + `mul_one`; `(c j : ℝ) •
(0 : ℝ)` reduces to `0` via `smul_zero`. The default `simp` set should
handle this, BUT if it doesn't, fall back to an explicit chain:

```lean
  simp only [Pi.basisFun_apply, Pi.single_apply, smul_ite, smul_zero,
             smul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
```

### 6.3 `Int.cast_smul_eq_zsmul` direction (Step C above)

The modern lemma is `(n : R) • b = n • b` — direction is **(ℝ-smul)
= (ℤ-smul)**. The `hc` from `Submodule.mem_span_range_iff_exists_fun`
gives `∑ i, c i • v i = x` with **ℤ-smul** on `c i`. To rewrite to the
ℝ-smul form needed for the basisFun_apply simp chain, we need the
**inverse** direction: `(n : R) • b ← n • b`, i.e. `← Int.cast_smul_eq_zsmul`.

Skeleton in §5 uses `(...).symm` inside `Finset.sum_congr` to avoid
the simp_rw direction quibble entirely. If the alternative
`simp_rw [← Int.cast_smul_eq_zsmul (R := ℝ)]` fails to match (e.g.
because `c i` is named, not raw, and `simp_rw` is overly literal),
the `Finset.sum_congr` form is robust.

### 6.4 `(x : Fin m → ℝ)` coercion vs `x.val` syntactic form

`x : stdLattice m = Submodule ℤ (Fin m → ℝ)` carries a
`Submodule`-typeclass coercion to `Fin m → ℝ`. Mathlib has both
`(x : Fin m → ℝ)` (instance coercion) and `x.val` (subtype projection
via the underlying `AddSubgroup`); the two should be defeq for
`SetLike.instCoeT`. If the `x.2` membership proof fails to elaborate,
unfold the coercion manually:

```lean
have hmem : (x.val : Fin m → ℝ) ∈
    Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin m))) := x.property
```

Parent OQ-02 uses `(x : Fin 2 → ℝ) ∈ ... := x.2` (line 150–151) — that
syntactic form is already proven to elaborate at the lake-pinned
toolchain.

### 6.5 `Subtype.coe` vs `AddSubgroup` coercion in `MinkowskiProved.minkowski_integer_lattice_proved`

The Minkowski theorem at `MinkowskiFundamentalTheorem.lean:643` returns
`x : (stdLattice n).toAddSubgroup` — an AddSubgroup, not a Submodule.
The S6 PREP §3 sketch silently coerces between the two. The actual
S6α ACT can use `stdLatticeN_coords` only after this coercion is
resolved at the S6 ACT callsite (NOT S6α — S6α is the standalone
lemma).

**S6α MUST state the lemma on `x : stdLattice m`** (Submodule version,
which is the parent OQ-02's choice at line 147) — NOT on
`(stdLattice m).toAddSubgroup`. The S6 ACT will then handle the
AddSubgroup → Submodule conversion at the Minkowski-output site.

## 7. Why ship S6α as a standalone ACT now? (vs bundling into S6 ACT)

| Criterion | S6α standalone | Bundled into S6 ACT |
| --------- | ------------- | ------------------- |
| LOC | ~22 (S6α only) | ~120 (S6 ACT total) |
| Mathlib bearer risk | 5 items above, all closeable in <30 min wall | + 6 more for the assembly logic |
| Dependency on S5-c | NONE — `stdLatticeN_coords` is purely lattice/algebra | Yes — needs `dirichletSetN_volume` |
| Conflict surface with #19046 | NONE — `stdLatticeN_coords` is a NEW `lemma`, not a modification | High — same file, possibly adjacent lemmas |
| Parallelizable with S5-b/S5-c | ✅ Yes — different `.lean` regions | n/a (must serialize) |
| De-risks S6 ACT | ✅ Catches §3.2 simp-chain bugs in isolation | ❌ Bug surface enlarged |

**Recommendation**: ship S6α as a `~30-LOC` ACT once #19046 (S5-b)
merges. This requires no overlay (since #19046 only ADDS new
declarations after PART 5; S6α's PART 6α inserts AFTER PART 5 but
contains a `stdLattice m`-only lemma that doesn't depend on
`shearM_toLin'_apply_*` or `dirichletBoxN` or
`dirichletSetN_eq_shearM_preimage`).

Sequencing: **S5-b (#19046) merge → S6α ACT branch from origin/main →
add PART 6α + `Proofs.MinkowskiFundamentalTheorem` import → Docker →
PR**.

### 7.1 Alternative: ship S6α concurrent with S5-c ACT

If S5-c ACT also goes into the same file (which #19181 PREP confirms),
S6α and S5-c could land independently in separate PRs as long as they
target distinct PART regions of `MinkowskiTheoremOQ02OQ03.lean`:

* S5-c ACT: append PART 6 (volume) AFTER PART 5 (shearM).
* S6α ACT: append PART 6α (integer coords) AFTER S5-c's PART 6.

OR S6α could be inserted between PART 5 and PART 6 (PART 5.5 / PART 6α).
Either way, both are AFTER PART 5 — no overlap with the existing
shearM lemmas.

**Risk**: line-shift conflict in `git apply` if the two PRs use the
same anchor point. **Mitigation**: stagger merges — wait for S5-b
(#19046) to land first, then ship S6α before S5-c ACT branches off
origin/main. S5-c ACT then sees S6α already merged, branches at
S6α-tip, appends PART 6 after PART 6α.

## 8. Anti-targets — what S6α MUST NOT attempt

* **❌ Do not touch existing PART 1–5.** S6α adds PART 6α only.
* **❌ Do not touch `state.md` or JSON tracker.** The PR #18991 STATE-SYNC
  is still in flight; touching the tracker here would create a merge
  conflict.
* **❌ Do not generalize `stdLatticeN_coords` to arbitrary
  `Submodule.span ℤ ...` over arbitrary modules.** The slug needs
  `Fin m → ℝ` only.
* **❌ Do not attempt the AddSubgroup → Submodule coercion in S6α.**
  That's S6 ACT proper. S6α ships the Submodule-form lemma; the
  coercion handling is the S6 ACT's job.
* **❌ Do not add a `@[simp]` attribute to `stdLatticeN_coords`.** The
  existential signature makes it `simp`-unfriendly. Parent OQ-02's
  `stdLattice2_coords` is also un-attributed.

## 9. Honest framing — what this PREP-2 does NOT establish

1. **No `lake build` performed.** All bearer claims are gh-api source
   inspections at the pinned SHA, not type-checked elaboration. The
   refined §5 skeleton is a paper design.

2. **§5 Step C's `Finset.sum_congr` approach is unverified.** The
   alternative `simp_rw [← Int.cast_smul_eq_zsmul (R := ℝ)]` was
   ranked second because `simp_rw` matching on `c i` (a named index)
   can be brittle. The `Finset.sum_congr` form should be robust, but
   was not Docker-tested.

3. **The §6.2 fallback `simp only` list is a candidate, not a verified
   one.** The default `simp` set may close the goal directly; if it
   doesn't, the §6.2 chain is the first thing to try. The exact tactic
   form may need additional tweaking (e.g. `if_true` / `if_false`
   discharge, `Finset.mem_univ`).

4. **No numerical witness sanity check.** `stdLatticeN_coords`
   doesn't take numerical inputs — the lemma is universally
   quantified over `x : stdLattice m`. No `decide` companion possible.

5. **The new `import Proofs.MinkowskiFundamentalTheorem`** adds
   a non-trivial transitive elaboration cost. S5 PREP-2 §6 measured
   `import Mathlib.MeasureTheory.Measure.Lebesgue.Basic` as
   slug-elaboration-clean; the additional Minkowski-fundamental import
   should be similar (parent OQ-02 already uses it).

6. **No assessment of `decide`/`fin_cases` vs `Fin.cases` strategy
   for §6.1 of the future S6 ACT.** This PREP-2 covers only the
   `stdLatticeN_coords` standalone lemma. The full Step 4 (`q ≠ 0`)
   tactic strategy is left to a future S6 PREP-3 or directly S6 ACT.

## 10. Pre-claim cross-checks

* ✅ Worktree synced to `origin/main` BEFORE drafting (HEAD at
  `2afb1b79c0a` = "research(abel-ruffini-oq-04-oq-09): S2 PREP …" per
  `git rev-parse origin/main`).
* ✅ Fresh topic branch off `origin/main`: `research/minkowski-oq-02-oq-03-s6-alpha-prep-stdLatticeN-1778807912`.
* ✅ Three open PRs on this slug (#18991, #19046, #19181) inspected;
  conflict surface is zero (THIS PR adds 1 new sessions/ file only).
* ✅ Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)
  verified at `proofs/lake-manifest.json:8`.
* ✅ Mathlib bearer audit (§3.1–§3.6): 6 items checked at pin, 1 ⚠️
  (deprecated alias `zsmul_eq_smul_cast`), 5 ✅.
* ✅ Stranded-commit rescue scan: `git log --all --oneline --grep=
  'minkowski-theorem-oq-02-oq-03'` shows no orphaned commits on
  `research/loop-*` branches (per
  `feedback_researcher_stranded_loop_commit_rescue_pattern.md`).
* ✅ `gh repo view` returned `rjwalters/lean-genius` (not the
  mathlib4 fork) — `gh pr list` and future `gh pr create` will resolve
  correctly without explicit `-R`, but this PR uses `-R
  rjwalters/lean-genius` defensively per
  `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`.

## 11. Done When (this PREP-2 session)

- [x] S6 PREP §3.2 sketch line-cited (PR #18511, file
  `2026-05-12-s6-prep-minkowski-assembly-roadmap.md`).
- [x] 6 Mathlib bearers audited at pin `2df2f015...`:
  `Submodule.mem_span_range_iff_exists_fun`, `Pi.basisFun_apply`,
  `Pi.single_apply`, `Finset.sum_ite_eq'`, `Int.cast_smul_eq_zsmul`
  (new) vs `zsmul_eq_smul_cast` (deprecated alias),
  `Set.range`/`Submodule.span` (unchanged).
- [x] Refined §5 Lean skeleton (~22 LOC) with modern
  `Int.cast_smul_eq_zsmul` form + 5 hazards (§6) + 4 fallback patterns.
- [x] §7 standalone-vs-bundled sub-ACT comparison + sequencing
  recommendation (ship S6α after #19046 merges, before/parallel with
  S5-c ACT).
- [x] §8 anti-targets enumerated (5).
- [x] §9 honest-framing caveats (6).
- [x] §10 pre-claim cross-checks (7) including stranded-commit scan
  and gh-default-repo trap.
- [x] No edits to `state.md`, `MinkowskiTheoremOQ02OQ03.lean`, JSON
  tracker, `problem.md`, `knowledge.md`, or any existing session file.

## 12. No-edit guarantee

This PR touches **only**:

```
research/problems/minkowski-theorem-oq-02-oq-03/sessions/
    2026-05-14-s6-prep-2-stdLatticeN-skeleton-audit.md
```

Branch: `research/minkowski-oq-02-oq-03-s6-alpha-prep-stdLatticeN-1778807912`.
Base: `origin/main` at `2afb1b79c0a43303ceda4f34671978fd481df996`.

## 13. References

* **S1 OBSERVE**:
  `research/problems/minkowski-theorem-oq-02-oq-03/sessions/2026-05-12-s01-observe.md`
  (PR #18339, merged 2026-05-12 22:39 UTC, researcher-1).
* **S5 PREP** (shear-map volume):
  `sessions/2026-05-12-s5-prep-shear-volume-generalization.md`
  (PR #18419, merged 2026-05-13 00:51 UTC, researcher-11).
* **S5 PREP-2** (Mathlib bearer audit, the precedent for this style):
  `sessions/2026-05-13-s5-prep-2-mathlib-bearer-audit.md`
  (PR #18622, merged 2026-05-13 06:50 UTC, researcher-5).
* **S6 PREP** (assembly roadmap, the doc this PREP-2 audits):
  `sessions/2026-05-12-s6-prep-minkowski-assembly-roadmap.md`
  (PR #18511, merged 2026-05-13 03:11 UTC, researcher-1).
* **S2 ACT** (`dirichletSetN` def + symmetry): PR #18551.
* **S3 + S4 ACT** (measurable + convex): PR #18613.
* **S5-a ACT** (shearM + det = (-1)ⁿ): PR #18975.
* **S5-b ACT** (open, build-verified 3058 jobs):
  `MinkowskiTheoremOQ02OQ03.lean` +79 LOC. PR #19046.
* **S5-c PREP** (open, doc-only): PR #19181.
* **S8 STATE-SYNC** (open, doc-only): PR #18991.
* **Parent OQ-02** template: `MinkowskiTheoremOQ02.lean:147–165`
  (`stdLattice2_coords`, 19 LOC for `Fin 2`).
* **`stdLattice` def**: `MinkowskiFundamentalTheorem.lean:590`.
* **`Submodule.mem_span_range_iff_exists_fun`** at pin:
  `Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean:372`.
* **`Pi.basisFun` + `basisFun_apply`** at pin:
  `Mathlib/LinearAlgebra/StdBasis.lean:131`.
* **`Int.cast_smul_eq_zsmul` (modern)** at pin:
  `Mathlib/Algebra/Module/NatInt.lean:151`.
* **`Finset.sum_ite_eq'`** at pin:
  `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:151`
  (`@[to_additive (attr := simp)]` of `prod_ite_eq'` line 153).
* **Cassels, J.W.S.** (1957), *An Introduction to Diophantine
  Approximation*, Theorem I.II.A.
