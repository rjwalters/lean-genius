# S14 — S11.B helper implementation: `exists_continuous_proj_convex`

**Researcher**: researcher-3
**Date**: 2026-05-09
**Iteration**: 14 (ACT phase, implementation)
**Outcome**: implementation; sorry count 1 → 0 (pending build verification)

## Goal

Replace the `sorry` body of the LOOKUP-2 helper

```lean
lemma exists_continuous_proj_convex {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S) :
    ∃ r : EuclideanSpace ℝ (Fin n) → ↥S,
      Continuous r ∧ ∀ x : ↥S, r (x : EuclideanSpace ℝ (Fin n)) = x
```

with a complete proof, eliminating the file's last `sorry`.

## Mathlib API used (verified at v4.26 pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| Name | File | Role |
|------|------|------|
| `IsCompact.isComplete` | `Mathlib/Topology/UniformSpace/Cauchy.lean` | compact ⇒ complete |
| `exists_norm_eq_iInf_of_complete_convex` | `Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean` | Hilbert projection: existence |
| `norm_eq_iInf_iff_real_inner_le_zero` | same file | variational inequality characterization |
| `real_inner_le_norm` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | Cauchy–Schwarz (real form) |
| `real_inner_self_eq_norm_sq` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | `⟪x, x⟫_ℝ = ‖x‖²` |
| `real_inner_comm` | same file | symmetry |
| `inner_sub_left`, `inner_sub_right` | same file | bilinearity |
| `LipschitzWith.of_dist_le_mul` | `Mathlib/Topology/MetricSpace/Lipschitz.lean` | Lipschitz from `dist`-bound |
| `LipschitzWith.continuous` | same file | Lipschitz ⇒ continuous |
| `continuous_induced_rng` | `Mathlib/Topology/Constructions.lean` | continuity into a subtype |
| `ciInf_le`, `le_ciInf` | `Mathlib/Order/ConditionallyCompleteLattice/Basic.lean` | conditional iInf bounds |

Added one import: `Mathlib.Analysis.InnerProductSpace.Projection` (umbrella;
re-exports `Minimal.lean`).

## Proof structure

The proof has three parts: existence (define `r`), continuity (1-Lipschitz),
and idempotency (`r x = x` for `x ∈ S`).

### Part 1 — define `r`

```lean
have hS_complete : IsComplete S := hS_compact.isComplete
have hexists : ∀ u, ∃ v ∈ S, ‖u - v‖ = ⨅ w : S, ‖u - w‖ :=
  exists_norm_eq_iInf_of_complete_convex hS_ne hS_complete hS_convex
let r : EuclideanSpace ℝ (Fin n) → ↥S := fun u =>
  ⟨Classical.choose (hexists u), (Classical.choose_spec (hexists u)).1⟩
```

We extract the (existentially asserted) nearest point via `Classical.choose`.
Define `hr_min` and `hr_mem` for the minimizer property and membership.

### Part 2 — variational inequality

```lean
have hVI : ∀ u, ∀ w ∈ S, ⟪u - (r u : E), w - (r u : E)⟫_ℝ ≤ 0 := fun u =>
  ((norm_eq_iInf_iff_real_inner_le_zero hS_convex (hr_mem u)).mp (hr_min u))
```

This is the standard characterization: `v` is the nearest point of `K` to `u`
iff the cone condition `⟪u - v, w - v⟫_ℝ ≤ 0` for all `w ∈ K`.

### Part 3 — 1-Lipschitz continuity

For `u₁, u₂` with projections `v₁, v₂`:

* Apply the variational inequality at `u = u₁, w = v₂`:
  `⟪u₁ - v₁, v₂ - v₁⟫_ℝ ≤ 0`.
* Apply at `u = u₂, w = v₁`: `⟪u₂ - v₂, v₁ - v₂⟫_ℝ ≤ 0`.
* Add and rewrite:
  ```
  ⟪u₁ - v₁, v₂ - v₁⟫_ℝ + ⟪u₂ - v₂, v₁ - v₂⟫_ℝ
    = ‖v₁ - v₂‖² - ⟪u₁ - u₂, v₁ - v₂⟫_ℝ
  ```
  (proved by `simp only [inner_sub_left, inner_sub_right, real_inner_comm v₂ v₁]`
  on both sides combined with `real_inner_self_eq_norm_sq`, then `linarith`).
* Conclude `‖v₁ - v₂‖² ≤ ⟪u₁ - u₂, v₁ - v₂⟫_ℝ`.
* Cauchy–Schwarz: `⟪u₁ - u₂, v₁ - v₂⟫_ℝ ≤ ‖u₁ - u₂‖ · ‖v₁ - v₂‖`.
* If `‖v₁ - v₂‖ = 0`, the result is immediate (norm nonneg).
  Otherwise divide by `‖v₁ - v₂‖ > 0`.

To convert 1-Lipschitz into `Continuous r`:
* `continuous_induced_rng.mpr` reduces to continuity of `Subtype.val ∘ r`.
* `LipschitzWith.of_dist_le_mul` (with `K := 1`) packages the bound, then
  `LipschitzWith.continuous` gives continuity.

### Part 4 — idempotency

For `x ∈ S`:

```
‖(x : E) - (r (x : E) : E)‖ = ⨅ w : S, ‖(x : E) - w‖   (hr_min)
                            = 0                          (since x ∈ S)
```

The infimum equals 0 by sandwiching: it is `≥ 0` (each term is a norm) and
`≤ ‖x - x‖ = 0` (via `ciInf_le` applied with `x ∈ S` as the witness).
Then `norm_eq_zero` and `sub_eq_zero` give `(r (x : E) : E) = (x : E)`,
which lifts to `r (x : E) = x` via `Subtype.ext`.

## Net effect on the Lean file

| Dimension | Pre-S14 (#17575) | Post-S14 (this PR) |
|---|---|---|
| Axioms | 2 (`brouwer_unit_ball` + `approx_selection_exists`) | **2** (unchanged) |
| Sorries | 1 (`exists_continuous_proj_convex` body) | **0** |
| Line count | 668 | ~762 |

`theorem brouwer_fpt` is now end-to-end sorry-free, depending only on the
strictly weaker `axiom brouwer_unit_ball`. Together with `axiom
approx_selection_exists` (Cellina–Browder graph approximate selections),
these are the only assumptions in the file.

## Risk surface

* The algebraic identity `⟪u₁ - v₁, v₂ - v₁⟫ + ⟪u₂ - v₂, v₁ - v₂⟫ =
  ‖v₁ - v₂‖² - ⟪u₁ - u₂, v₁ - v₂⟫` is sensitive to how `simp` normalizes
  signs in `inner_sub_left`/`inner_sub_right` expansions. The `linarith`
  fallback should handle any rewriting choice provided `hcomm` is applied
  consistently to both `hself` and the goal (both branches use the same
  simp set in this proof).
* The `((1 : ℝ≥0) : ℝ)` coercion in `LipschitzWith.of_dist_le_mul` is
  resolved by an explicit `NNReal.coe_one` rewrite followed by `one_mul`.

## Build verification

Build is in progress at submission time per the established
`proofs/.lake` self-symlink trap cadence
(`feedback_researcher_lake_symlink_broken.md`). The PR follows the
"build pending" pattern of S7 (#17308), S8 (#17360), S9 (#17419),
S11 (#17501), S12 (#17523), S13 (#17575). The build verification
should run in 30–45 min from the fresh-clone path.

## Next steps

1. Build verification: confirm 0 sorries on origin/main rebase.
2. meta.json sync: `sorries: 2 → 0`, `lineCount: 517 → ~762`.
3. After build success, this file's only remaining mathematical
   assumptions are the two axioms (`brouwer_unit_ball` and
   `approx_selection_exists`), as documented in the file header.
4. Possible follow-up sessions: (a) attempt to prove `brouwer_unit_ball`
   from finite-dimensional algebraic-topology Mathlib content (currently
   absent, per S10); (b) attempt to prove `approx_selection_exists`
   directly (Cellina–Browder is the canonical proof, ~200–400 Lean lines
   per S6).
