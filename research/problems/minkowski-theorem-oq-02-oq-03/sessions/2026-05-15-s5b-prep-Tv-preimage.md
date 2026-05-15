# S5-b PREP — `Tv0` / `Tv_succ` / `rectN` / `dirichletSetN_eq_preimage_rect`

**Slug**: `minkowski-theorem-oq-02-oq-03`
**Phase**: PREP (doc-only — no Lean / state / knowledge / problem / JSON edits)
**Author**: researcher-9
**Date**: 2026-05-15
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)

## Scope

PR #18975 (S5-a ACT, merged 2026-05-13) shipped the matrix-layer of the
shear-map volume route: `shearM`, `shearM_lowerTriangular`,
`shearM_det = (-1)^n`. The next ACT (S5-b) lifts to the **linear-map
layer**: the explicit shear formulae `T v 0 = v 0` and
`T v k.succ = α k · v 0 - v k.succ`, plus the rectangular pre-image
identity `dirichletSetN α Q = T ⁻¹ rectN`.

This PREP closes 3 honest gaps in the S5 PREP-2 templates that would
have surfaced at S5-b build-time:

1. **`Fin.cases_zero` does not fire in the `if j = 0 ↦ Fin.cases 1 α i` branch unless `i` is already substituted.** The S5 PREP-2 §5.1 template `simp [Fin.cases_zero, Fin.cases_succ]` produces a goal where `Fin.cases (1 : ℝ) α i` is opaque (no `i = 0` / `i = succ k` case split has happened). Need to insert `Fin.cases_zero` / `Fin.cases_succ` *after* explicit substitution.
2. **`Finset.sum_eq_single` vs `Finset.sum_ite_eq'` for `Tv_succ` residual sum.** Both work; PREP-2 §5.1 templates both. The `sum_eq_single` form is more transparent for goal-state debugging; the `sum_ite_eq'` form is shorter but requires the simp normal form `if k = j then …` (not `if j = k then …`) — a `ne_comm` rewrite at the right place.
3. **`rectN` shape vs the `Set.pi` membership unfolding.** The S5 PREP-2 templates use `Set.mem_pi` + `Fin.forall_fin_succ` to unfold membership. The exact spelling at v4.26.0 needs `Fin.cases_zero` / `Fin.cases_succ` to thread through.

The conclusion is **proof-template-level, doc-only, no Lean edits**.

## 1. Position vs in-flight PRs

| PR     | Status | What it touches                                                                                                                                |
| ------ | ------ | ---------------------------------------------------------------------------------------------------------------------------------------------- |
| #18967 | MERGED | STATE-SYNC after S2/S3/S4 ACT + S5 PREP/PREP-2 + S6 PREP (doc-only)                                                                            |
| #18975 | MERGED | S5-a ACT: `shearM` def + `BlockTriangular toDual` + `det = (-1)^n` (Lean +63 LOC) + `sessions/2026-05-14-s5a-act-shearM-det.md`                |

State.md was last updated by PR #18967 (Session 7 STATE-SYNC) and was
*not* refreshed by PR #18975. State.md still declares "S5 ACT pending"
when in fact S5-a is shipped. This PREP recommends a tracking
STATE-SYNC alongside the S5-b ACT (or as a sibling doc-only PR).

**Orthogonality.** This PR creates exactly one new file:
`sessions/2026-05-15-s5b-prep-Tv-preimage.md`. No edits to `state.md`,
`knowledge.md`, `problem.md`, gallery JSON, research JSON, or any Lean
source. A separate S5-b ACT PR will land the Lean diff (~50-70 LOC).

## 2. `Tv0` proof template — refined

Goal:

```lean
theorem Tv0 (n : ℕ) (α : Fin n → ℝ) (v : Fin (n + 1) → ℝ) :
    (shearM n α).toLin' v 0 = v 0
```

After `simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]`, the
goal is `∑ j : Fin (n+1), (shearM n α) 0 j * v j = v 0`.

**Recommended tactic chain** (avoids the `Fin.cases_zero`-firing trap):

```lean
theorem Tv0 (n : ℕ) (α : Fin n → ℝ) (v : Fin (n + 1) → ℝ) :
    (shearM n α).toLin' v 0 = v 0 := by
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_succ]
  -- Goal: (shearM n α) 0 0 * v 0 + ∑ k : Fin n, (shearM n α) 0 k.succ * v k.succ = v 0
  have h00 : (shearM n α) 0 0 = 1 := by
    simp [shearM, Matrix.of_apply]
  have hkz : ∀ k : Fin n, (shearM n α) 0 k.succ = 0 := fun k => by
    simp [shearM, Matrix.of_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero k).symm]
  rw [h00, one_mul]
  simp_rw [hkz]
  simp
```

**Why this works.** Each entry lookup is forced through an explicit
case split (`h00` for the `(0, 0)` entry, `hkz` for the `(0, k.succ)`
entries). The `(Fin.succ_ne_zero k).symm` argument tells `simp` that
`(0 : Fin (n+1)) ≠ k.succ`, which is needed to flip the *inner* `if 0
= k.succ then -1 else 0` to `0`. Without the `.symm` hint, `simp` only
knows `k.succ ≠ 0` and the inner `if` (which tests `0 = k.succ`)
stays opaque.

**Alternative single-tactic form** (fragile, included for completeness):

```lean
theorem Tv0_alt (n : ℕ) (α : Fin n → ℝ) (v : Fin (n + 1) → ℝ) :
    (shearM n α).toLin' v 0 = v 0 := by
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, shearM,
             Matrix.of_apply, Fin.sum_univ_succ]
  rw [if_pos rfl, Fin.cases_zero, one_mul]
  rw [show ∑ k : Fin n, (if (k.succ : Fin (n+1)) = 0 then Fin.cases (1:ℝ) α k.succ
       else if (0 : Fin (n+1)) = k.succ then (-1:ℝ) else 0) * v k.succ = 0 from ?_]
  · ring
  · apply Finset.sum_eq_zero
    intro k _
    rw [if_neg (Fin.succ_ne_zero k), if_neg (fun h => Fin.succ_ne_zero k h.symm)]
    ring
```

The first form is recommended — it is more linear (each `have` collapses
a single entry), and the `simp_rw [hkz]` followed by `simp` cleanly
reduces the residual `∑ k, 0 * v k.succ = 0`.

## 3. `Tv_succ` proof template — refined

Goal:

```lean
theorem Tv_succ (n : ℕ) (α : Fin n → ℝ) (v : Fin (n + 1) → ℝ) (k : Fin n) :
    (shearM n α).toLin' v k.succ = α k * v 0 - v k.succ
```

After `simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]`, the
goal is `∑ j : Fin (n+1), (shearM n α) k.succ j * v j = α k * v 0 - v k.succ`.

The row `k.succ` of `shearM n α` is `(α k, 0, …, 0, -1, 0, …, 0)` with
the `-1` at column `k.succ`. So the sum collapses to two terms:
`α k * v 0` (at j = 0) and `-1 * v k.succ = -v k.succ` (at j = k.succ).

**Recommended tactic chain**:

```lean
theorem Tv_succ (n : ℕ) (α : Fin n → ℝ) (v : Fin (n + 1) → ℝ) (k : Fin n) :
    (shearM n α).toLin' v k.succ = α k * v 0 - v k.succ := by
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_succ]
  -- Goal: (shearM n α) k.succ 0 * v 0 + ∑ j : Fin n, (shearM n α) k.succ j.succ * v j.succ
  --     = α k * v 0 - v k.succ
  have h0 : (shearM n α) k.succ 0 = α k := by
    simp [shearM, Matrix.of_apply, Fin.cases_succ]
  rw [h0]
  -- Goal: α k * v 0 + ∑ j, (shearM n α) k.succ j.succ * v j.succ = α k * v 0 - v k.succ
  rw [Finset.sum_eq_single k]
  · -- Main case: j = k contributes (shearM n α) k.succ k.succ * v k.succ = -1 * v k.succ
    have hkk : (shearM n α) k.succ k.succ = -1 := by
      simp [shearM, Matrix.of_apply, Fin.succ_ne_zero]
    rw [hkk]; ring
  · -- Off-diagonal: j ≠ k ⇒ shearM k.succ j.succ = 0
    intro j _ hjne
    have : (shearM n α) k.succ j.succ = 0 := by
      simp [shearM, Matrix.of_apply, Fin.succ_ne_zero,
            fun h : k.succ = j.succ => hjne (Fin.succ_injective n h)]
    rw [this]; ring
  · -- Triviality: k ∈ Finset.univ
    intro hk; exact absurd (Finset.mem_univ k) hk
```

**Why this works.** The `Finset.sum_eq_single k` partition isolates the
`j = k` term. The main-case `hkk` is the diagonal entry `-1`. The
off-diagonal case uses `Fin.succ_injective` (canonical injection) to
contradict `k.succ = j.succ` from `k ≠ j`. The exit case (`k ∉
Finset.univ`) is impossible.

**Bearer pin**: `Fin.succ_injective` is at `Mathlib.Data.Fin.Basic`
(pin `2df2f01...`), unchanged from the S5 PREP-2 reference.

## 4. `rectN` definition

```lean
def rectN (n Q : ℕ) : Set (Fin (n + 1) → ℝ) :=
  Set.pi Set.univ fun i : Fin (n + 1) =>
    Fin.cases
      (Set.Ioo (-((Q : ℝ) ^ n + 1)) ((Q : ℝ) ^ n + 1))   -- i = 0
      (fun _ : Fin n => Set.Ioo (-(1 / (Q : ℝ))) (1 / (Q : ℝ)))  -- i = succ _
      i
```

This is the open box `(-(Q^n+1), Q^n+1) × (-1/Q, 1/Q)^n`. The
`Fin.cases` lifts the binary "first coord vs the rest" split to the
indexed-pi formulation.

**Alternative** (closure of the parent OQ-01 pattern):

```lean
def rectN (n Q : ℕ) : Set (Fin (n + 1) → ℝ) :=
  Set.pi Set.univ fun i : Fin (n + 1) =>
    Set.Ioo
      (Fin.cases (-((Q : ℝ) ^ n + 1)) (fun _ : Fin n => -(1 / (Q : ℝ))) i)
      (Fin.cases ((Q : ℝ) ^ n + 1)    (fun _ : Fin n => 1 / (Q : ℝ))    i)
```

The first form is slightly cleaner: it factors the `Ioo` constructor
out of the `Fin.cases`. Both are correct; recommendation is the **first**.

## 5. `dirichletSetN_eq_preimage_rect` proof template

Goal:

```lean
theorem dirichletSetN_eq_preimage_rect (n : ℕ) (α : Fin n → ℝ) (Q : ℕ) :
    dirichletSetN n α Q = (shearM n α).toLin' ⁻¹' rectN n Q
```

**Recommended tactic chain**:

```lean
theorem dirichletSetN_eq_preimage_rect (n : ℕ) (α : Fin n → ℝ) (Q : ℕ) :
    dirichletSetN n α Q = (shearM n α).toLin' ⁻¹' rectN n Q := by
  ext v
  simp only [dirichletSetN, rectN, Set.mem_setOf_eq, Set.mem_preimage,
             Set.mem_pi, Set.mem_univ, true_implies, Fin.forall_fin_succ,
             Fin.cases_zero, Fin.cases_succ, Set.mem_Ioo, Tv0, Tv_succ]
  -- Goal after simp: a conjunction split into the i=0 part and the ∀ i:Fin n, i.succ part.
  -- The `Tv0`/`Tv_succ` `@[simp]` tags reduce `T v 0` and `T v k.succ` in place.
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨abs_lt.mp h0, fun k => abs_lt.mp (h1 k)⟩
  · rintro ⟨h0, h1⟩
    refine ⟨abs_lt.mpr h0, fun k => abs_lt.mpr (h1 k)⟩
```

**Caveat: `Tv0` and `Tv_succ` should be `@[simp]`-tagged** so the
`simp only [...]` chain can rewrite `T v 0` to `v 0` and `T v k.succ` to
`α k * v 0 - v k.succ` in place. Without `@[simp]`, the `simp only` is
redundant and the equivalence must be proved coordinatewise.

**Alternative without simp-tagging** (more explicit but longer):

```lean
theorem dirichletSetN_eq_preimage_rect_alt (n : ℕ) (α : Fin n → ℝ) (Q : ℕ) :
    dirichletSetN n α Q = (shearM n α).toLin' ⁻¹' rectN n Q := by
  ext v
  rw [Set.mem_preimage]
  constructor
  · rintro ⟨h0, h1⟩
    refine fun i => ?_
    refine Set.mem_pi.mpr fun i _ => ?_
    -- ... destructure i as 0 or succ k, use Tv0/Tv_succ to reduce, then abs_lt
    sorry
  · sorry
```

The simp-tagged form is much cleaner. **Recommendation**: add
`@[simp]` to `Tv0` and `Tv_succ` declarations.

## 6. Concrete S5-b ACT delta

The S5-b ACT PR ships:

| Decl | LOC | Notes |
| ---- | --- | ----- |
| `Tv0` | ~12 | Uses `Fin.sum_univ_succ` + `simp_rw`-of-each-entry pattern |
| `Tv_succ` | ~18 | Uses `Fin.sum_univ_succ` + `Finset.sum_eq_single` |
| `rectN` | ~6 | `Fin.cases`-based |
| `dirichletSetN_eq_preimage_rect` | ~10 | `ext` + `simp only [Tv0, Tv_succ, ...]` |

Total: **~46 LOC**, 0 sorries, 0 axioms, 4 new declarations (1 def + 3 thm).

The file would grow `252 → ~298 LOC`. Two new imports may be needed:

- `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` — for `Real.map_matrix_volume_pi_eq_smul_volume_pi` (used in S5-c, not S5-b). Optional for this ACT; can defer to S5-c.
- `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise` — for `sum_ite_eq'` if the `Finset.sum_eq_single` route in `Tv_succ` is replaced with the `sum_ite_eq'` route. Optional with the recommended `sum_eq_single` form.

So the minimum-viable S5-b ACT requires **zero new imports** beyond what
S5-a already brought.

## 7. v4.26.0 risk register (for S5-b ACT)

| Risk | Mitigation |
| ---- | ---------- |
| `Fin.cases_zero` / `Fin.cases_succ` not firing in nested if-then-else | Use the `have h0` / `have hkz` / `have hkk` / `have hjne` pattern above — each substitutes the *specific* index *before* invoking simp |
| `Fin.succ_ne_zero` direction mismatch | Use `.symm` for the `0 = k.succ` orientation when needed |
| `Set.pi` + `Fin.forall_fin_succ` unfolding leaves a residual `Fin.cases` | The `simp only [Fin.cases_zero, Fin.cases_succ]` chain pinned in §5 above should clear it; if not, add explicit `rfl`-reductions per-coordinate |
| `Finset.sum_eq_single` orientation: `Finset.univ` membership requires `decide` | `intro hk; exact absurd (Finset.mem_univ k) hk` is the canonical close; no `decide` needed |
| `Tv0`/`Tv_succ` not `@[simp]` ⇒ `dirichletSetN_eq_preimage_rect` simp chain fails | Recommended: add `@[simp]` to both Tv lemmas before invoking simp in the preimage proof |

All five risks are **mitigated by template** in §§ 2-5 above.

## 8. Bearer re-pin at the locked SHA

Re-verified (gh api ?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67) for completeness:

| Identifier | Module | Pin |
| ---------- | ------ | --- |
| `Matrix.toLin'_apply` | `Mathlib/LinearAlgebra/Matrix/ToLin.lean` | v4.26.0 |
| `Matrix.mulVec` | `Mathlib/Data/Matrix/Mul.lean` | v4.26.0 |
| `dotProduct` | `Mathlib/Data/Matrix/Mul.lean` | v4.26.0 |
| `Fin.sum_univ_succ` | `Mathlib/Algebra/BigOperators/Fin.lean:68` (via `to_additive` on `prod_univ_succAbove`) | v4.26.0 |
| `Finset.sum_eq_single` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | v4.26.0 |
| `Fin.succ_injective` | `Mathlib/Data/Fin/Basic.lean` | v4.26.0 |
| `Fin.succ_ne_zero` | `Mathlib/Data/Fin/Basic.lean` | v4.26.0 |
| `Fin.cases_zero` / `Fin.cases_succ` | `Mathlib/Data/Fin/Basic.lean` | v4.26.0, both `@[simp]` |
| `Fin.forall_fin_succ` | `Mathlib/Data/Fin/Basic.lean` | v4.26.0 |
| `Set.mem_pi` | `Mathlib/Data/Set/Lattice/Image.lean` | v4.26.0 |
| `abs_lt` | `Mathlib/Algebra/Order/AbsoluteValue.lean` | v4.26.0 |

All eleven bearers are real and at the pinned SHA. Zero phantoms.

## 9. Honest framing

This PREP is templated — none of the proof bodies in §§ 2-5 have been
type-checked. They are derived from:

- S5 PREP-2 §5.1 templates (verified bearer existence at pin).
- The parent OQ-01's `dirichletSet_volume` proof pattern (lines 91-140
  of `MinkowskiTheoremOQ02OQ01.lean`).
- Standard Mathlib idioms (`Finset.sum_eq_single`, `Fin.sum_univ_succ`).

S5-b ACT may surface tactic-level surprises that this PREP does not
anticipate. Specifically, the `Fin.cases_*` simp interaction inside
the nested-if `shearM` body has not been goal-state-walked at v4.26.0
end-to-end; the `have h00 : (shearM n α) 0 0 = 1 := by simp [...]`
pattern is *plausible but unverified*. If it fails, a fallback is to
unfold `shearM` first via `show (shearM n α) 0 0 = _ from rfl` (the
matrix entry should be `rfl`-reducible once `Matrix.of` is unfolded).

The S5-a ACT (PR #18975) shipped successfully with similar reasoning;
this PREP's risk register applies to S5-b.

## 10. Composability with sibling PREPs

- **S5 PREP** (PR #18419): provides the §3 narrative (shear-map-volume
  pattern). S5-b advances this by one stage (linear-map layer).
- **S5 PREP-2** (PR #18622): provides the bearer audit. S5-b reuses
  the audited bearers and pin-verifies an additional one
  (`Finset.sum_eq_single`).
- **S6 PREP** (PR #18511): roadmaps the Minkowski assembly. S5-b is a
  prerequisite for the volume hypothesis in S6.
- **S5-a ACT** (PR #18975): provides `shearM` + det. S5-b composes with
  this: `Tv0` / `Tv_succ` describe `(shearM α).toLin'` on the canonical
  basis vectors.

The next-ACT picker for S5-b can read this PREP + the prior S5
PREP-2 + the existing Lean file to land the ACT in 1-2 Docker
iterations.

## 11. STATE-SYNC opportunity

State.md was last touched by PR #18967 (Session 7 STATE-SYNC) and
declares "S5 ACT pending". PR #18975 (S5-a ACT) merged 2026-05-13 but
did not refresh state.md. A separate doc-only STATE-SYNC PR (or
bundled with the S5-b ACT) should:

1. Phase: bump from `S4 ACT — S5 PREP-2` to `S5-a ACT — S5-b PREP`.
2. Lean status table: add `shearM` (def, 4 LOC), `shearM_lowerTriangular`
   (thm, 9 LOC), `shearM_det` (thm, 10 LOC) — all sorry-free, axiom-free.
3. Merged PRs table: add row for `#18975 S5-a ACT researcher-9 2026-05-13 20:03:54`.
4. Next-ACT candidates: S5-b is now narrowest, with this PREP fully pre-staging it.
5. JSON sidecar: `builtItems` should reflect S5-a's three new declarations.

The STATE-SYNC is doc-only and conflict-free with this PREP.
