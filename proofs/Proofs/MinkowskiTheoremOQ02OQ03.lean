/-
# Simultaneous Dirichlet Approximation via Minkowski (OQ-03): S2 ACT seed

## What This Establishes (this revision)

This file is the n-dimensional generalisation of
`Proofs/MinkowskiTheoremOQ02OQ01.lean` (Dirichlet's approximation theorem
via Minkowski, 1D axiom-free). It targets OQ-03 of the parent
`minkowski-theorem-oq-02` slug: prove the **simultaneous Dirichlet
approximation theorem** for `n` real numbers `α : Fin n → ℝ`,

> For every `α : Fin n → ℝ` and `Q ≥ 1`, there exist integers
> `q ≥ 1`, `p : Fin n → ℤ` with `q ≤ Qⁿ` and
> `|α i · q − p i| ≤ 1/Q` for every `i`.

The construction follows Cassels (1957, Theorem I.II.A): take the
parallelepiped

```
dirichletSetN n α Q :=
  {v : Fin (n+1) → ℝ | |v 0| < Qⁿ + 1 ∧
                       ∀ i : Fin n, |α i · v 0 − v i.succ| < 1/Q}
```

apply Minkowski's lattice-point theorem to it (its volume is
`2^(n+1) · (Qⁿ + 1) / Qⁿ > 2^(n+1)`, exceeding the
`(2 : ENNReal)^(n+1)` threshold for the integer lattice in
`Fin (n+1) → ℝ`), extract a non-trivial lattice point, and read off
`q := v 0`, `p i := v i.succ`.

The parent state.md decomposes this into 5 ACT sessions:

| Session | Deliverable | Status |
|---|---|---|
| S2 | `dirichletSetN` def + `dirichletSetN_symmetric` | **this file** |
| S3 | `dirichletSetN_measurable` (open-set) | future |
| S4 | `dirichletSetN_convex` (linear-preimage of `Ioo`) | future |
| S5 | `dirichletSetN_volume` (shear-map computation) | future |
| S6 | `simultaneous_dirichlet_from_minkowski` (assembly) | future |

This revision ships **S2 ACT only** — the definition + the central
symmetry lemma, which is the cleanest sorry-free seed for the chain
and matches the parent OQ-01 file's `dirichletSet_symmetric` proof
pattern exactly. Sessions S3-S6 have been pre-staged via S5 PREP
(`sessions/2026-05-12-s5-prep-shear-volume-generalization.md`,
merged) and S6 PREP (`sessions/2026-05-12-s6-prep-minkowski-assembly-roadmap.md`,
open at the time of S2 ACT).

## Status

- `dirichletSetN`: definition in place.
- `dirichletSetN_symmetric`: sorry-free, axiom-free (6 LOC, verbatim
  generalisation of the parent OQ-01's `dirichletSet_symmetric`).
- `axiomCount`: 0.
- `sorryCount`: 0.

## References

- Parent OQ-01 (1D axiom-free Dirichlet): `Proofs/MinkowskiTheoremOQ02OQ01.lean`,
  `dirichletSet` (line 41) and `dirichletSet_symmetric` (line 48).
- Parent OQ (1D with axioms): `Proofs/MinkowskiTheoremOQ02.lean`.
- Cassels, *An Introduction to the Geometry of Numbers*, Springer 1957,
  Theorem I.II.A.
- Schmidt, *Diophantine Approximation*, Lecture Notes in Mathematics 785,
  Springer 1980, Theorem I.1A.
-/

import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace MinkowskiTheoremOQ02OQ03

-- ============================================================
-- PART 1: The n-dim Dirichlet Parallelepiped (Cassels 1957)
-- ============================================================

/-- The n-dim simultaneous-Dirichlet set after Cassels (1957, Thm I.II.A).

For `α : Fin n → ℝ` and `Q : ℕ`, this is the parallelepiped

    {v : Fin (n+1) → ℝ | |v 0| < Qⁿ + 1 ∧
                         ∀ i : Fin n, |α i · v 0 − v i.succ| < 1/Q}

with `v 0` reserved as the *common-denominator* coordinate (so
`q := v 0` after Minkowski extracts an integer point) and
`v i.succ` carrying the i-th *approximation residual*. At `n = 1`
this specialises to the parent OQ-01's `dirichletSet` modulo
indexing (`Fin 2 → ℝ` with `v 0`, `v 1`). -/
def dirichletSetN (n : ℕ) (α : Fin n → ℝ) (Q : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {v | |v 0| < ((Q : ℝ) ^ n) + 1 ∧
       ∀ i : Fin n, |α i * v 0 - v i.succ| < 1 / (Q : ℝ)}

-- ============================================================
-- PART 2: Central Symmetry (S2 ACT — this revision)
-- ============================================================

/-- **Central symmetry.** `dirichletSetN n α Q` is symmetric about
the origin: if `v` lies in the set, so does `-v`. This is one of the
three hypotheses of Minkowski's lattice-point theorem (the other two —
measurability and convexity — are handled in S3 / S4).

The proof is the verbatim n-dim generalisation of the parent OQ-01's
`dirichletSet_symmetric` (`Proofs/MinkowskiTheoremOQ02OQ01.lean:48-54`)
with the second conjunct quantified by `∀ i : Fin n` instead of being
the single `i = 1` case. -/
theorem dirichletSetN_symmetric (n : ℕ) (α : Fin n → ℝ) (Q : ℕ) :
    ∀ v ∈ dirichletSetN n α Q, -v ∈ dirichletSetN n α Q := by
  intro v ⟨hv0, hvi⟩
  refine ⟨?_, ?_⟩
  · simp only [Pi.neg_apply, abs_neg]; exact hv0
  · intro i
    simp only [Pi.neg_apply]
    rw [show α i * -v 0 - -v i.succ = -(α i * v 0 - v i.succ) by ring, abs_neg]
    exact hvi i

end MinkowskiTheoremOQ02OQ03
