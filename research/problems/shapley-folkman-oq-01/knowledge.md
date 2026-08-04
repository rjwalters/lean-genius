# Knowledge: shapley-folkman-oq-01

## Parent file map (`proofs/Proofs/ShapleyFolkman.lean`, 1238 lines, 0 sorries, 0 axioms)

Verified gallery proof. Statement:

```lean
theorem shapley_folkman [FiniteDimensional ℝ E]
    {N : ℕ} (S : Fin N → Set E) :
    ∀ x ∈ convexHull ℝ (∑ i, S i), ∃ decomposition, …
```

Key steps that depend essentially on `[FiniteDimensional ℝ E]`:

| Step                                | Line  | Why it needs `FiniteDimensional`                                                                  |
|-------------------------------------|-------|---------------------------------------------------------------------------------------------------|
| `excess_vertices_affine_dependent`  | 151   | `Module.finrank ℝ E + 1 < n` ⟹ any `n` points are affinely dependent (false in infinite-dim)      |
| `linearDependent_coefficients`      | 185   | `Module.finrank ℝ E < n` ⟹ any `n` vectors are linearly dependent (false in infinite-dim)        |
| `reduce_excess_by_one`              | 377   | The reduction loop terminates because `excessIndices.card` is bounded by `Module.finrank ℝ E + 1` |
| `shapley_folkman`                   | 1140  | Final assembly bound `excessIndices.card ≤ Module.finrank ℝ E`                                    |

All four steps are vacuous or trivially false when `Module.finrank ℝ E = 0`
(which is the Lean convention for non-finite-dim modules).

## Lean's `Module.finrank` convention

`Module.finrank R M` returns `0` for any `M` that is not finitely
generated as an `R`-module (`Module.finrank_eq_zero_iff` or similar):

```
theorem Module.finrank_eq_zero_of_not_FiniteDimensional :
    ¬ FiniteDimensional ℝ E → Module.finrank ℝ E = 0
```

Consequence: rewriting `[FiniteDimensional ℝ E]` to a "suitable
dimension" replacement requires either:

1. A different dimension notion that is non-zero for some
   infinite-dim spaces (e.g., Hilbert-space dimension as a
   cardinal `Module.rank`), but the Carathéodory and
   affine-independence steps still fail since they need a
   `Nat`-valued bound; or
2. A completely different proof structure (Lyapunov / Aumann).

## Three viable infinite-dim analogs (none are drop-in)

### Aumann (1965) — set-valued integral

**Statement.** Let `(Ω, μ)` be an atomless measure space and
`F : Ω → Set H` be a measurable set-valued map into a separable
Hilbert (or Banach) space `H`. Then

```
∫ F dμ := { ∫ f dμ | f : Ω → H, f measurable, f x ∈ F x μ-a.e. }
```

is convex (and closed, if `F` is integrably bounded).

**Why this is an analog of Shapley–Folkman**: replace the discrete
sum `∑ᵢ S i` with a continuous integral `∫ F dμ`. The atomless
hypothesis plays the role of "many independent summands"
(`N → ∞`).

**Mathlib status**: NOT present.

### Lyapunov (1940) — vector-measure range convexity

**Statement.** Let `μ : Σ → ℝⁿ` be an atomless vector-valued
measure (i.e., for every `A ∈ Σ` with `μ A ≠ 0` there is
`B ⊆ A` with `0 ≠ μ B ≠ μ A`). Then the range
`{ μ A | A ∈ Σ }` is convex and compact in `ℝⁿ`.

**Why this is the engine**: Aumann's theorem is proved via
Lyapunov applied to the vector measure
`A ↦ ∫_A f dμ` for each `f : Ω → H` measurable selection.

**Mathlib status**: NOT present. (Confirmed by `grep -rn
'Lyapunov\|lyapunov' Mathlib/MeasureTheory/` ⟹ zero hits.)

### Ekeland–Témam (1976) — "non-convexity index" for Banach

**Statement** (Ekeland–Témam, *Convex Analysis and Variational
Problems*, §I.4 Remark 4.10): for a Banach space `E` with
non-convexity index `ρ(E) < ∞` (essentially the Loewner-ellipsoid
ratio of the unit ball), a Shapley–Folkman-style bound holds
with `ρ(E)` in place of `Module.finrank ℝ E`.

**Why this is not a useful Lean target**: `ρ(E)` is finite iff
`E` is finite-dim, so this is just a re-parameterization of the
finite-dim theorem.

## Explicit `ℓ²` counter-example (Approach C — S2 ACT target)

Take `E = EuclideanSpace ℝ (Fin n)` (or `ℓ²(ℕ, ℝ)` for the
honest infinite-dim case), the standard basis `e i : Fin n → E`,
and define

```lean
S : Fin n → Set E := fun i => {0, EuclideanSpace.basisFun ℝ i}
```

so `Sᵢ = {0, eᵢ}` is a 2-point non-convex set.

The Minkowski sum `∑ᵢ Sᵢ` consists of vectors `∑ᵢ εᵢ · eᵢ`
with `εᵢ ∈ {0, 1}`, which are the indicator vectors of subsets
of `Fin n`.

The point `x := (1/2) ∑ᵢ eᵢ ∈ convexHull ℝ (∑ᵢ Sᵢ)` (it is the
midpoint of `0` and `∑ᵢ eᵢ = (1, 1, …, 1)`).

**Claim**: every Shapley–Folkman-style decomposition `x = ∑ᵢ xᵢ`
with `xᵢ ∈ convexHull ℝ Sᵢ` has `excessIndices = Finset.univ`
(every index is excess).

**Proof sketch**: each `convexHull ℝ Sᵢ = [0, eᵢ]` (the segment)
in coordinate `i`, with `0` in all other coordinates. So
`xᵢ = tᵢ eᵢ` for some `tᵢ ∈ [0, 1]`, and `x = ∑ᵢ tᵢ eᵢ`.
Comparing components: `tᵢ = 1/2` for all `i`. Hence `xᵢ = (1/2) eᵢ`
which is the midpoint, not an extreme point of `Sᵢ`; so `i ∈
excessIndices` for every `i`.

This gives `excessIndices.card = n`, unbounded as `n → ∞`.
In particular for `n = ω` (genuine infinite-dim), the count is
infinite.

## Mathlib API needed for Approach C

| API                                       | Location                                                      | Use                                       |
|-------------------------------------------|---------------------------------------------------------------|-------------------------------------------|
| `EuclideanSpace ℝ (Fin n)`                | `Mathlib.Analysis.InnerProductSpace.PiL2`                     | Concrete finite-dim Euclidean ambient     |
| `EuclideanSpace.basisFun`                 | `Mathlib.Analysis.InnerProductSpace.PiL2`                     | Standard basis `e i`                       |
| `Module.finrank ℝ (EuclideanSpace ℝ (Fin n))` | `Mathlib.LinearAlgebra.FiniteDimensional`                  | Equals `n` (sanity check)                  |
| `convexHull ℝ`                            | `Mathlib.Analysis.Convex.Hull`                                | Convex hull of `Sᵢ`                         |
| `Set.add` / `Finset.sum (Set.image ...)`   | `Mathlib.Algebra.Order.Pointwise`                             | Minkowski sum                              |
| `lp 2`                                    | `Mathlib.Analysis.NormedSpace.lpSpace`                        | Genuine infinite-dim Hilbert (deferred)    |

## Open meta-questions for S2+

1. **Should the counter-example be stated in `EuclideanSpace ℝ (Fin n)`
   or `lp 2`?** `EuclideanSpace ℝ (Fin n)` is finite-dim and only
   demonstrates that the bound `n` cannot be improved; `lp 2` is
   the honest infinite-dim statement but has more cumbersome API.
   **Decision**: state in `EuclideanSpace ℝ (Fin n)` first (S2-A),
   then lift to `lp 2` after the finite-dim version compiles (S2-B).

2. **Should the negative result be packaged as a `theorem` or as
   a `definition + remark`?** The natural Lean statement is a
   `theorem` of the form `∀ N, ∃ E S x, ¬ ∃ decomposition, …`,
   which is a clean `¬ ∃` (existential negation). Decision:
   `theorem`.

3. **Companion `*Aristotle.lean` file scope?**
   Since S2 is a `¬ ∃` statement using explicit constructions,
   no obvious supporting lemmas in Mathlib's idiom would benefit
   from Aristotle. Decision: skip companion for S2; create one
   only if S3+ adds Aumann-style positive content.

4. **Should the S1 OBSERVE PR also stub the Aumann statement?**
   Stating Aumann requires set-valued measurability machinery
   not in Mathlib. Decision: no stub — leave Aumann/Lyapunov
   as a separate prerequisite project (parented at
   `shapley-folkman-oq-01-oq-01` or similar in a future seeker
   iteration).

## S3-A: Lyapunov dimension one — DONE (2026-07-24, researcher-2)

`proofs/Proofs/ShapleyFolkmanOQ01Lyapunov.lean` (246 lines, 0 sorries,
0 axioms). Sierpiński's IVT for atomless measures on ℝ
(`exists_subset_measure_eq`), value-range interval theorem
(`setOf_measure_subset_eq_Icc`, `lyapunov_range_eq_Icc`), and the d = 1
Lyapunov statement (`lyapunov_range_convex`, `lyapunov_range_isCompact`),
with a Lebesgue-on-[0,1] non-vacuity witness. Mechanism: cumulative-slice
IVT (`t ↦ μ (s ∩ Iic t)` continuous ⇐ `Iio_ae_eq_Iic` + continuity from
above; exact level by `mem_range_of_exists_le_of_exists_ge`).

Key fact for S3-B: Mathlib's `NoAtoms` (singleton-null) is strictly weaker
than the splitting notion off ℝ — the countable-cocountable σ-algebra with
the 0/1 measure is `NoAtoms` but has value range `{0, 1}`. General-space
Sierpiński therefore needs a new strong-atomless predicate + greedy
exhaustion. On ℝ the weak notion suffices (this file proves it).
