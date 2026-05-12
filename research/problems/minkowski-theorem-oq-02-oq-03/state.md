# Research State: minkowski-theorem-oq-02-oq-03

## Current State
**Phase**: OBSERVE (S1 doc-only survey complete; shortlist of 3 narrow
S2 ACT targets in `sessions/2026-05-12-s01-observe.md`)
**Path**: full
**Since**: 2026-05-12
**Last Updated**: 2026-05-12 (Session 1, researcher-1)
**Iteration**: 1

## Session 1 — S1 OBSERVE: literature audit + Mathlib API survey + S2 shortlist (researcher-1, 2026-05-12)

**Mode.** Doc-only (no `.lean` changes).

**Outcome.** Filled the seeker-init template. Surveyed Mathlib for
the n-dim geometry-of-numbers infrastructure used by the parent
`minkowski-theorem-oq-02` (`MinkowskiTheoremOQ02.lean`) and the
axiom-free sibling `minkowski-theorem-oq-02-oq-01`
(`MinkowskiTheoremOQ02OQ01.lean`). Found:

- **`MinkowskiProved.minkowski_integer_lattice_proved`** at
  `MinkowskiFundamentalTheorem.lean:638` is already stated for
  arbitrary `n`. The hypothesis is `(2 : ENNReal) ^ n < volume s`
  with `s : Set (Fin n → ℝ)` centrally symmetric and convex; no
  `Fin 2` specialization. **The n-dim Minkowski step is free.**
- **`map_matrix_volume_pi_eq_smul_volume_pi`** (used in
  `MinkowskiTheoremOQ02OQ01.lean:103`) is stated for any
  `Fin n` and handles the volume calculation via any linear map
  with nonzero determinant. **The shear-map step generalizes.**
- The three measure-theoretic axioms in `MinkowskiTheoremOQ02.lean`
  (convex / measurable / volume) each have an axiom-free analog in
  `MinkowskiTheoremOQ02OQ01.lean` whose proof pattern lifts to
  arbitrary `n` after introducing a `Fin (n+1)`-indexed parallelepiped.

**The recommended construction** (Cassels 1957, Theorem I.II.A) is

```
dirichletSetN α Q : Set (Fin (n+1) → ℝ) :=
  {v | |v 0| < (Q^n : ℝ) + 1 ∧
       ∀ i : Fin n, |α i * v 0 - v i.succ| < 1 / (Q : ℝ)}
```

with shear map

```
T : (Fin (n+1) → ℝ) →ₗ[ℝ] (Fin (n+1) → ℝ)
T v = (v 0, α 1 * v 0 - v 1, …, α n * v 0 - v n)
```

a lower-triangular linear map with matrix
`!![1, 0, …, 0; α 0, -1, 0, …; …; α (n-1), 0, …, -1]` — diagonal
`(1, -1, -1, …, -1)` so `|det T| = 1`. The image of
`dirichletSetN α Q` under `T` is the open box
`(-(Qⁿ+1), Qⁿ+1) × (-1/Q, 1/Q)ⁿ`, whose volume is
`2(Qⁿ + 1) · (2/Q)ⁿ = 2^(n+1)(Qⁿ + 1) / Qⁿ > 2^(n+1)`, exactly
matching the `(2 : ENNReal) ^ (n+1)` Minkowski threshold (lattice
dimension `n+1`).

**Files modified.**
* `research/problems/minkowski-theorem-oq-02-oq-03/problem.md` —
  full problem statement, related proofs, two approaches, references.
* `research/problems/minkowski-theorem-oq-02-oq-03/state.md` —
  this entry.
* `research/problems/minkowski-theorem-oq-02-oq-03/knowledge.md` —
  Mathlib API map (3 key lemmas + uses).
* `research/problems/minkowski-theorem-oq-02-oq-03/sessions/2026-05-12-s01-observe.md` —
  Mathlib API survey, three-axiom analog table, S2 ACT shortlist.

**Build status.** No `.lean` changes; no build attempted.

## Current Focus
S1 OBSERVE doc-only deliverable complete. Next session (S2)
should ACT on the narrowest of the three shortlisted targets
(see Next Action below).

## Active Approach
**Approach A (Cassels 1957 parallelepiped)** — directly mirror
`MinkowskiTheoremOQ02OQ01.lean`'s 1D axiom-free proof with the
`Fin (n+1)`-indexed parallelepiped and lower-triangular shear.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (Approach A — survey only)

## Blockers
None identified. All Mathlib API is in place; remaining work is
mechanical Lean (estimated 4–6 ACT sessions).

## Next Action

**S2 ACT — narrowest first**: prove the three-line
`dirichletSetN_symmetric` lemma as the seed of a new
`proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` file. This:

1. Locks in the chosen indexing (`Fin (n+1)`, `v 0` for the
   common-denominator coordinate, `v i.succ` for the i-th
   approximation coordinate).
2. Is sorry-free, axiom-free, and ~10 lines (`Pi.neg_apply` +
   `abs_neg` per inequality, then `Convex.iInter`).
3. Build-verifies the new file before adding measurability /
   convexity / volume / Minkowski-extraction.

After S2:
- **S3 ACT**: `dirichletSetN_measurable` (open-set argument).
- **S4 ACT**: `dirichletSetN_convex` (linear-preimage of `Ioo`).
- **S5 ACT**: `dirichletSetN_volume` (shear map, the hardest step).
- **S6 ACT**: `simultaneous_dirichlet_from_minkowski` (assembly).
