# Knowledge Base: ballot-problem-oq-01-oq-02-oq-01-oq-02-oq-01

Uniform Fiber Transfer via `MeasureTheory.Measure.map`.

---

## Problem Understanding

Lift the parent's **event-wise** uniform fiber transfer (`uniformOn A (f⁻¹'P) =
uniformOn T P` for events `P ⊆ T`, verified in
`proofs/Proofs/BallotProblemOQ01OQ02OQ01OQ02.lean`) to the **structural**
pushforward identity for the counting measure:

    (Measure.count.restrict A).map f = c • Measure.count.restrict T

with the corollary `(uniformOn A).map f = uniformOn T`.

---

## Insights

### KEY INSIGHT — the correct hypothesis is `MapsTo`, not `SurjOn`

The parent theorem used only `SurjOn f A T` (`T ⊆ f '' A`) because it evaluated on
events `P ⊆ T`, where the behaviour of `f` outside the fibers over `T` is
irrelevant. The **global** `Measure.map` identity is tested on *all* measurable
`S ⊆ β`. If any element of `A` mapped outside `T`, that mass would land where the
RHS `c • count.restrict T` is zero — breaking the equality. The right hypothesis
is therefore **`MapsTo f A T`** (equivalently `f '' A ⊆ T`): no mass escapes `T`.
Combined with the uniform-fiber hypothesis (which, for `c > 0`, forces `SurjOn`),
this yields `f '' A = T`. This is the one genuinely new mathematical requirement
the lift introduces over the parent.

### The proof collapses onto the verified parent counting lemma

Testing on a measurable `S`, the LHS reduces — via `Measure.map_apply` then
`Measure.restrict_apply` — to `count (f⁻¹'S ∩ A)`. Using `MapsTo`,
`f⁻¹'S ∩ A = A ∩ f⁻¹'(S ∩ T)`. On the finite set this counting measure equals
`ncard`, and `BallotGeneralFiberTransfer.uniform_fiber_count` gives
`(A ∩ f⁻¹'(S∩T)).ncard = c * (S∩T).ncard`. The RHS is `c * count (S ∩ T)`. Both
sides are `(c : ℝ≥0∞) * (S ∩ T).ncard`. So the whole `Measure.map` statement is
just the already-verified `ncard` lemma dressed in measure-theoretic API — no new
combinatorics.

### The `count ↔ ncard` bridge is the only piece of new plumbing

`Measure.count s = (s.ncard : ℝ≥0∞)` for finite `s`, proved from
`Measure.count_apply_finite` + `Set.ncard_eq_toFinset_card` (both require
`MeasurableSingletonClass`). This is the adapter between the combinatorial parent
(stated in `ncard`) and the measure-theoretic target.

### The `uniformOn` corollary is one normalization step

`uniformOn s = Measure.count[|s] = (count s)⁻¹ • count.restrict s`
(`ProbabilityTheory.cond`). Pushing the map through the scalar with
`Measure.map_smul` and applying the counting identity leaves
`(count A)⁻¹ • (c • count.restrict T)`. Since `count A = c * count T` (finite,
`c > 0`), the scalar `(count A)⁻¹ * c` collapses to `(count T)⁻¹`, giving
`uniformOn T`. The ℝ≥0∞ arithmetic uses `ENNReal.mul_inv` and
`ENNReal.inv_mul_cancel` with `c ≠ 0`, `T.ncard ≠ 0`, `c` and `T.ncard` finite.

---

## Exact Mathlib API used

| Purpose | Lemma |
|---------|-------|
| pushforward on measurable set | `MeasureTheory.Measure.map_apply hf hS` |
| restriction on measurable set | `MeasureTheory.Measure.restrict_apply` |
| finite count = card | `MeasureTheory.Measure.count_apply_finite` |
| card = toFinset card | `Set.ncard_eq_toFinset_card` |
| measure extensionality | `MeasureTheory.Measure.ext` |
| scalar of measure on set | `MeasureTheory.Measure.smul_apply` |
| map of scalar multiple | `MeasureTheory.Measure.map_smul` |
| nonempty fiber ⇒ surjective | `Set.nonempty_of_ncard_ne_zero` |
| `count A = c • count T` | parent `BallotFiberTransfer.ncard_biUnion_eq_of_uniform` |
| the core counting identity | parent `BallotGeneralFiberTransfer.uniform_fiber_count` |
| `uniformOn` = conditioned count | `ProbabilityTheory.uniformOn`, `ProbabilityTheory.cond` |

---

## Dead Ends

- **`SurjOn`-only hypothesis**: insufficient for the global `Measure.map`
  identity (see KEY INSIGHT). Do not restate the parent's hypotheses verbatim.
- **Singleton-determination of `count`**: tempting ("count is a sum of Diracs")
  but unnecessary — `Measure.ext` over measurable sets plus the finite
  `count = ncard` bridge is cleaner and avoids `tsum` bookkeeping for infinite
  targets. `T` is finite, so `S ∩ T` is always finite.

---

## Sessions

### Session 2026-07-04 (Session 1) — ORIENT + scaffold

**Mode**: FRESH
**Outcome**: progress (build-pending)

**What I did**
- Read parent `BallotProblemOQ01OQ02OQ01OQ02.lean`; confirmed the verified lemma
  `uniform_fiber_count` (ncard form) is exactly the combinatorial core needed.
- Derived the correct hypothesis set (`MapsTo f A T`, not `SurjOn`) for the
  global pushforward — the one new mathematical content of the lift.
- Pinned exact Mathlib API from the local mathlib4 checkout (signatures verified,
  not compiled): `count_apply_finite`, `map_apply`, `restrict_apply`, `smul_apply`,
  `map_smul`, `ncard_eq_toFinset_card`, `nonempty_of_ncard_ne_zero`, `Measure.ext`.
- Wrote `proofs/Proofs/BallotProblemOQ01OQ02OQ01OQ02OQ01.lean`:
  - `count_eq_ncard` (finite bridge),
  - `preimage_inter_of_mapsTo` (the `MapsTo` set rewrite),
  - `count_restrict_map_eq` (MAIN — the `Measure.map` identity),
  - `uniformOn_map_eq` (corollary — `uniformOn` pushforward).

**Key findings**
- The lift adds no new combinatorics; it reduces entirely to the parent lemma
  plus the finite `count ↔ ncard` bridge.
- `MapsTo` is the essential extra hypothesis.

**Files modified**
- `proofs/Proofs/BallotProblemOQ01OQ02OQ01OQ02OQ01.lean` (new)

**Blocker this session**
- DUAL-TOOL BLACKOUT: Docker build wrapper (containerd blob I/O error) and
  Aristotle proof service ("Resource not found" / 404) both unavailable. The file
  is therefore **UNVERIFIED / build-pending** — the proof structure is complete
  and reduces to verified lemmas, but has not been machine-checked. Marked so in
  the PR body to keep the deployer from auto-merging.

**Next steps**
- Build `Proofs.BallotProblemOQ01OQ02OQ01OQ02OQ01` once Docker recovers; fix any
  coercion / lemma-argument mismatches (most likely spots: the `ENNReal.mul_inv`
  argument forms in `uniformOn_map_eq`, and `push_cast`/`nsmul_eq_mul` in
  `count_restrict_map_eq`).
- Once verified (0 sorries, 0 axioms), create the gallery entry
  `src/data/proofs/ballot-problem-oq-01-oq-02-oq-01-oq-02-oq-01/` and mark
  `status: verified`.
