# Closing the Final `hook_walk_identity` Sorry

**State as of session 33 (2026-04-27):** `BallotProblemOQ03OQ01OQ02.lean` is 14022
lines with one remaining `sorry`, on the ≥10-row × ≥10-column non-rectangular
branch of the `hook_walk_identity` dispatcher (line 13932). The file already
exceeds the Docker 32 GB build envelope. This note compares the three known
proof routes and recommends a path forward.

---

## The identity to prove

For any `μ : YoungDiagram` with `0 < μ.card`,

```
∑_{c ∈ corners μ} (hookProd μ : ℚ) / (hookProd (μ \ c) : ℚ) = (μ.card : ℚ).
```

The dispatcher already discharges every shape with `min(rows, cols) ≤ 10` plus
all rectangles, so the open case is a *non-rectangular shape with both ≥ 11
rows and ≥ 11 columns*.

---

## Route A — Greene–Nijenhuis–Wilf hook walk

Reference: Greene, Nijenhuis, Wilf, *A probabilistic proof of a formula for
the number of Young tableaux of a given shape*, Adv. Math. 31 (1979), 104–109.

**Argument.** Pick a uniform cell `(i,j) ∈ μ`; repeatedly move to a uniform cell
of the *strict* hook (arm cells `(i, j')` with `j < j' < rowLen i` and leg cells
`(i', j)` with `i < i' < colLen j`); stop when the strict hook is empty,
i.e. when the current cell is a corner. GNW prove

```
P(walk ends at c) = hookProd μ / (μ.card · hookProd (μ \ c)).
```

Summing over corners and using ∑P = 1 gives the identity directly.

**Lean cost estimate.** ~300 lines once a uniform-distribution / hitting-time
toolkit is in place. The probability machinery in Mathlib (`MeasureTheory`,
`ProbabilityTheory`) is heavy; a deterministic recasting (count weighted paths
of every length and divide by `μ.card · ∏ |strict hook|`) is probably leaner
and self-contained, but still ~400 lines.

**Pros**
- Uniform across all shapes — closes the sorry at once.
- Replaces the entire row-by-row tower (PARTS XIVc–XXVI) if reformulated.

**Cons**
- Mathlib's `ProbabilityTheory` is unfamiliar to this file; transitive imports
  may push compile time / memory further.
- The classical proof's inclusion–exclusion step on the row/column projections
  is delicate to formalize and is the actual hard core.

---

## Route B — Fomin growth diagrams (RSK)

Reference: Fomin, *Generalized Robinson–Schensted–Knuth correspondence*,
J. Soviet Math. 41 (1988), 979–991; or Sagan, *The Symmetric Group*, §3.6–3.7.

**Argument.** RSK gives a bijection between `n × n` 0-1 matrices and pairs of
SYT of the same shape. Restricting to permutation matrices yields
`n! = ∑_λ (f^λ)^2`. A growth-diagram refinement gives
`(f^λ)^2 · ∏_{u ∈ λ} h(u)^2 = (n!)^2`,
hence `f^λ · hookProd λ = n!` directly (and the hook-walk identity follows
from the corner recursion).

**Lean cost estimate.** ~600 lines including the bijection definition, but
this also produces the *full HLF* directly (no `hook_walk_identity` needed).
Some growth-diagram infrastructure may exist in `Mathlib.Combinatorics.RSK`.

**Pros**
- Combinatorial, no probability theory.
- Yields HLF directly; `hook_walk_identity` becomes a downstream corollary
  rather than a prerequisite.
- Reusable for many other Young-tableau theorems.

**Cons**
- Larger initial investment than GNW.
- Mathlib's RSK status as of 2026-04 is partial; check before committing to
  this route.

---

## Route C — Canonical LGV configuration (already scaffolded in PART V)

The OPEN comment at lines 226–264 of `BallotProblemOQ03OQ01OQ02.lean`
sets out a canonical encoding `youngLGVConfigOf μ` and reduces HLF to:

- (A) `Fintype.card (StandardYoungTableau μ) = niTupleCount (youngLGVConfigOf μ)`
  — Fomin growth bijection, ~200 lines.
- (B) `(pathMatrix (youngLGVConfigOf μ)).det · hookProd μ = μ.card.factorial`
  — Lindström / Jacobi–Trudi identity, ~200 lines.

The LGV well-formedness condition `r - 1 ≤ μ.rowLen (r - 1)` fails for tall
narrow shapes, so a transpose-duality split is needed. Taking the wider of
`μ, μᵀ` always satisfies the condition because `numRows μ + numCols μ ≤ μ.card + 1`
and the wider one has `rowLen 0 ≥ √(μ.card)` ≥ `numRows`.

**Pros**
- Reuses the already-proved `lgv_lemma_rxr` machinery (2315 lines, 0 sorries).
- Sidesteps `hook_walk_identity` entirely — gives an independent HLF proof.

**Cons**
- (A) duplicates effort with Route B; the bijection is essentially RSK/Fomin
  growth.
- (B) requires Vandermonde / Jacobi–Trudi expansion; Mathlib's
  `Matrix.det_eq_*` lemmas can help but the partition-indexed form is custom.

---

## Recommendation

1. **Modularise first.** At 14022 lines the file no longer compiles in
   Docker. Split PARTS XIVc–XXVI (the row-by-row tower, ≈ 10 000 lines) into
   `BallotProblemOQ03OQ01OQ02RowByRow.lean` so the head module fits the
   build envelope again. After modularization it is safe to add new lemmas
   on top.

2. **Then take Route B (RSK / Fomin).** It produces the strongest single
   payoff (full HLF for all shapes, kills `hook_walk_identity` as a
   corollary), and the growth-diagram bijection has independent value for
   future combinatorics work in this gallery (knuthEquivalent, Specht modules,
   etc.). Mathlib's existing partial RSK can be a head-start.

3. **Route A (GNW) is a smaller-scoped alternative** if the goal is *just*
   to retire the final sorry without restructuring the proof. Choose this
   if the modularization in step 1 turns out to be too disruptive.

4. **Route C (canonical LGV)** is the most aligned with this file's existing
   architecture but duplicates Route B's combinatorial work via (A). Worth
   pursuing only after Route B if a second independent HLF proof is desired.

---

## Concrete starting points

For Route B, the first three definitions to add (independent of the row-tower):

```
def numRows (μ : YoungDiagram) : ℕ := μ.colLen 0

def reverseRowLens (μ : YoungDiagram) (i : Fin (numRows μ)) : ℕ :=
  μ.rowLen (numRows μ - 1 - i.val)

lemma reverseRowLens_monotone (μ : YoungDiagram) :
    Monotone (reverseRowLens μ) := by
  intro i j hij
  unfold reverseRowLens
  exact μ.rowLen_anti _ _ (by have := j.is_lt; omega)
```

These are the building blocks the OPEN comment in PART V already calls for.
After modularization (step 1 above) they can be added to the head file
without straining the build envelope.
