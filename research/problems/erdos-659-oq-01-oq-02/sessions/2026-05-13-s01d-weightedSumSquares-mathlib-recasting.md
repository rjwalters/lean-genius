# S1d OBSERVE — `QuadraticForm.weightedSumSquares` recasting of the d≥3 Cartesian-lattice squared-distance form

**Researcher**: researcher-6
**Date**: 2026-05-13
**Phase**: OBSERVE (orthogonal angle)
**Iteration**: 1d (Mathlib API audit)
**Lines added**: doc-only, no Lean / no edits to `problem.md` / `knowledge.md` / `state.md` / `src/data/research/problems/erdos-659-oq-01-oq-02.json`
**Predecessor PRs**: #18322 (S1, MERGED), #18421 (S1b, open — Cartesian-lattice square falsification), #18431 (S1c, open — Pell-safety condition with weighted bilinear form).

## Scope and orthogonality

S1 (PR #18322 merged) committed to a Cartesian-lattice axiomatic S2 plan with `cartesianLattice_fourPointProperty` as axiom #1. S1b (PR #18421 open) refuted the naïve 4-point property by exhibiting a degenerate 4-square configuration at $d = 3$, $k = 1$. S1c (PR #18431 open) responded by introducing a *Pell-safety condition* (weighted bilinear form $B_{p,q}(v,w) = v_1 w_1 + p \cdot v_2 w_2 + q \cdot v_3 w_3$) that ranges over admissible $(p, q)$ to recover the property in a subfamily, and verified the safety condition for $N = 14$ in the $(p, q) = (2, 5)$ regime.

This S1d note is **orthogonal to S1b and S1c**: I accept both as background and focus on a different question — the *recasting* of the squared-distance form $Q_d(\delta) = \sum_{i=1}^{d} p_{i-1} \delta_i^2$ (with $p_0 = 1, p_1 = 2, p_2 = 3, p_3 = 5, \ldots$) as a direct instance of Mathlib's `QuadraticForm.weightedSumSquares`. The implication: a substantial chunk of the planned S2 *Lean implementation* can be discharged by direct API citation rather than bespoke definition. None of this changes the open mathematical content (4-point property vs Pell-safety counterexamples), but it does change what S2 has to *write down*.

**Pristine guarantee**. This iteration adds exactly one new file:

```
research/problems/erdos-659-oq-01-oq-02/sessions/2026-05-13-s01d-weightedSumSquares-mathlib-recasting.md
```

No edits to:
- `problem.md` / `knowledge.md` / `state.md`
- `src/data/research/problems/erdos-659-oq-01-oq-02.json`
- `proofs/Proofs/Erdos659OQ01OQ02.lean` (does not exist yet; S2 will create)
- Any in-flight S1b / S1c paths.

## The Mathlib API surface

`Mathlib.LinearAlgebra.QuadraticForm.Basic.lean` lines 1366–1383 give:

```lean
-- Mathlib.LinearAlgebra.QuadraticForm.Basic, line 1371
variable {ι S : Type*} {R : Type*}
variable [CommRing R] [Fintype ι]
variable [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]

/-- The weighted sum of squares with respect to some weight as a quadratic form. -/
def weightedSumSquares (w : ι → S) :
    QuadraticMap R (ι → R) R :=
  ∑ i : ι, w i • (proj (R := R) (n := ι) i i)

@[simp]
theorem weightedSumSquares_apply (w : ι → S) (v : ι → R) :
    weightedSumSquares R w v = ∑ i : ι, w i • (v i * v i) :=
  QuadraticMap.sum_apply _ _ _
```

The relevant instances for our use case:

| Instantiation | Role | Notes |
|---|---|---|
| `ι = Fin d` | $d$-dimensional sum | `[Fintype (Fin d)]` automatic |
| `R = ℤ` | Squared-distance values (over the lattice) | `[CommRing ℤ]` automatic |
| `R = ℝ` | Squared-distance values (over the EuclideanSpace embedding) | `[CommRing ℝ]` automatic |
| `S = ℕ` or `S = ℤ` | Prime weights `(1, 2, 3, 5, 7, …)` | `[DistribMulAction ℕ ℤ]` automatic |

The two scalar choices we care about are `R = ℤ` (the lattice's intrinsic integer form) and `R = ℝ` (the embedded form on `EuclideanSpace ℝ (Fin d)`); both are equally accessible.

## Recasting the d = 3 case (concrete)

The d = 3 Cartesian lattice $L_3(k)$ is defined in `knowledge.md` (S1) as

$$ L_3(k) = \{(a_1, a_2 \sqrt 2, a_3 \sqrt 3) : a_i \in \mathbb Z \cap [-k, k]\} \subset \mathbb R^3. $$

The squared Euclidean distance between $(a_1, a_2 \sqrt 2, a_3 \sqrt 3)$ and $(b_1, b_2 \sqrt 2, b_3 \sqrt 3)$ is

$$ \|p - q\|^2 = (a_1 - b_1)^2 + 2 (a_2 - b_2)^2 + 3 (a_3 - b_3)^2. $$

This is exactly $\mathtt{weightedSumSquares}\ \mathbb Z\ w\ \delta$ with

```
w = ![1, 2, 3] : Fin 3 → ℤ
δ = ![a₁ - b₁, a₂ - b₂, a₃ - b₃] : Fin 3 → ℤ
```

In Lean (planned S2 code):

```lean
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

namespace Erdos659OQ01OQ02

open QuadraticMap

/-- The d = 3 weighted-sum-of-squares form `Q_3(δ) = δ₁² + 2 δ₂² + 3 δ₃²`. -/
noncomputable def cartesianLatticeForm₃ : QuadraticMap ℤ (Fin 3 → ℤ) ℤ :=
  weightedSumSquares ℤ ![1, 2, 3]

example (δ : Fin 3 → ℤ) :
    cartesianLatticeForm₃ δ = δ 0 * δ 0 + 2 * (δ 1 * δ 1) + 3 * (δ 2 * δ 2) := by
  simp [cartesianLatticeForm₃, weightedSumSquares_apply,
        Fin.sum_univ_three]
  ring

end Erdos659OQ01OQ02
```

Expected line count for the d = 3 form: **3 lines of declaration + 4-line sanity-check `example`** ≪ the ~25-line bespoke definition the S1 state.md plan anticipated.

## Recasting general d ≥ 3

For arbitrary $d$, the prime-weighted form is `weightedSumSquares ℤ (Nat.primeWeight d)` where the weight function maps `i : Fin d` to the $i$-th prime (with the convention $p_0 = 1$ for the unweighted first coordinate). The Mathlib primality machinery provides `Nat.nth Nat.Prime` (the $n$-th prime).

```lean
/-- Prime weights for the d-dimensional Cartesian lattice:
    `w 0 = 1`, `w i = Nat.nth Nat.Prime (i - 1)` for `i ≥ 1`. -/
def primeWeight (d : ℕ) : Fin d → ℤ :=
  fun i => if i = 0 then 1 else (Nat.nth Nat.Prime (i.val - 1) : ℤ)

/-- The d-dimensional Cartesian-lattice squared-distance form. -/
noncomputable def cartesianLatticeFormD (d : ℕ) : QuadraticMap ℤ (Fin d → ℤ) ℤ :=
  weightedSumSquares ℤ (primeWeight d)
```

The `primeWeight` definition uses Mathlib's `Nat.nth Nat.Prime` (defined in `Mathlib.Data.Nat.Nth`). Sanity check:

```lean
example : (primeWeight 4 : Fin 4 → ℤ) = ![1, 2, 3, 5] := by decide  -- or `rfl`
```

(The exact tactic depends on `Nat.nth_prime_zero`, `_one`, `_two` simp lemmas; this is mechanical Mathlib bookkeeping, not research-level.)

## Equivalence to the EuclideanSpace squared distance

The `EuclideanSpace ℝ (Fin d)` `dist²` of two points in $L_d(k)$ equals the `weightedSumSquares ℝ` of their integer coordinate differences. Concretely:

```lean
/-- The embedding of `L_d(k)` into EuclideanSpace ℝ (Fin d) is given by
    `(a i) ↦ (a i) * Real.sqrt (primeWeight d i)`. -/
noncomputable def latticeEmbed (d : ℕ) (a : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  fun i => (a i : ℝ) * Real.sqrt (primeWeight d i : ℝ)

theorem dist_sq_eq_weightedSumSquares (d : ℕ) (a b : Fin d → ℤ) :
    (dist (latticeEmbed d a) (latticeEmbed d b)) ^ 2
      = ((weightedSumSquares ℤ (primeWeight d) (a - b) : ℤ) : ℝ) := by
  -- Pointwise: ((a i - b i) * √w i)² = (a i - b i)² * w i
  -- Sum over i, push the cast inward, apply weightedSumSquares_apply.
  sorry  -- (S2 deliverable; routine but not 1-liner)
```

This bridge theorem `dist_sq_eq_weightedSumSquares` is the technical reason the recasting is worth the API import: once proved (a ~10-line `simp`+`ring` proof on the explicit unfold), every statement about distinct distances in `L_d(k)` reduces to a statement about distinct *values* of `weightedSumSquares ℤ (primeWeight d)` over the box $[-2k, 2k]^d \subset \mathbb Z^d$.

The latter is a purely combinatorial / number-theoretic statement, independent of any `EuclideanSpace` / `MetricSpace` infrastructure.

## Implications for S2 implementation plan

S1 state.md's S2 plan listed `distinctDistancesD` and `fourPointPropertyD` as fresh definitions over `EuclideanSpace ℝ (Fin d)`. The recasting suggests a **two-tiered implementation**:

**Tier 1 (combinatorial layer)**: Work entirely with integer vectors `Fin d → ℤ` and the form `weightedSumSquares ℤ (primeWeight d)`. The "distinct distances" question becomes: how many distinct values does this form take over $[-2k, 2k]^d \subset \mathbb Z^d$? This is the *honest* underlying question.

**Tier 2 (EuclideanSpace layer)**: Define `latticeEmbed` and prove `dist_sq_eq_weightedSumSquares`. This bridges the combinatorial result into the gallery-standard `EuclideanSpace ℝ (Fin d)` formulation that `problem.md` requires.

The decomposition has three concrete benefits:

1. **Avoids `Real.sqrt` and `dist` in the core combinatorial lemmas** — Tier 1 is purely over ℤ, so `decide` / `omega` / `Finset.sum` simp-set are all in play. The bridge to ℝ happens once at Tier 2.
2. **Aligns with the S1c Pell-safety condition** (PR #18431) — that condition is naturally stated in terms of the *weighted bilinear form* $B_{p,q}$, which is the polar of `weightedSumSquares`. Citing the polar map `QuadraticMap.polarBilin` (Mathlib.LinearAlgebra.QuadraticForm.Basic line ~600) gives a clean Lean home for the S1c safety condition.
3. **Reuses any future Mathlib `weightedSumSquares` lemmas** — e.g. positivity over $\mathbb R^+$ weights (which the primes are) yields `cartesianLatticeFormD` is positive-definite. This was an *implicit* assumption in S1; the recasting makes it derivable.

## What this does NOT address

1. **The S1b 4-point falsification**. The square $\{(0,0,0), (1,0,0), (0,1,0), (1,1,0)\}$ in $L_3(1)$ (note: this is a unit square in the $a_1$-$a_2$ plane, all squared distances $\in \{1, 2\}$) still has only 2 distinct distances. The recasting does not rescue this; the Cartesian-lattice with weight $(1, 2, 3)$ genuinely fails the 4-point property at $d = 3$, $k = 1$. S1b is correct.
2. **The S1c Pell-safety axiom**. Whatever subfamily of $L_3(k)$ (or alternative weighting $(p, q)$) recovers the 4-point property, that condition is still axiomatic at the level of the S2 plan. The recasting does not prove the Pell-safety condition; it only provides a cleaner ambient API for *stating* it.
3. **Solymosi–Vu lower bound**. Still axiomatic. No Mathlib coverage.
4. **The asymptotic rate $\Theta(n^{2/d})$**. Still conjectural; this S1d note does not advance the bound.

## Updated S2 axiom count (after recasting)

If S2 adopts the recasting:

| Axiom | Status | After recasting |
|---|---|---|
| `cartesianLatticeFormD` is the right form | implicit in S1 plan | **derivable** via `weightedSumSquares` |
| `dist_sq_eq_weightedSumSquares` (Tier 1 ↔ Tier 2 bridge) | implicit in S1 plan | **provable** (~10-line proof) |
| `cartesianLattice_fourPointProperty` | axiom (S1 plan) | **still axiom** — but now phrased over `weightedSumSquares`, deferring to S1c Pell-safety subfamily |
| `cartesianLattice_distinctDistances_bound` | axiom (S1 plan) | **still axiom** — distinct-values count of weighted-sum-of-squares form |
| `solymosi_vu_distinct_distance_lower_bound_dim_d` | axiom (S1 plan) | **still axiom** — Solymosi–Vu absent from Mathlib |

Net axiom count: **3** (unchanged). What changes is the *infrastructure* count — two implicit assumptions in S1's plan become Mathlib API consequences.

## Three concrete next-action S2 targets

In rough order of difficulty:

**S2a (~20 lines, mechanical)**: Define `primeWeight d : Fin d → ℤ` and `cartesianLatticeFormD d : QuadraticMap ℤ (Fin d → ℤ) ℤ` as `weightedSumSquares ℤ (primeWeight d)`. Sanity-check at d = 3: `cartesianLatticeFormD 3 ![δ₁,δ₂,δ₃] = δ₁² + 2δ₂² + 3δ₃²`.

**S2b (~30 lines, routine)**: Define `latticeEmbed : Fin d → ℤ → EuclideanSpace ℝ (Fin d)` and prove `dist_sq_eq_weightedSumSquares`. Tactic skeleton: unfold `EuclideanSpace.dist`, push casts, apply `weightedSumSquares_apply`, `ring`.

**S2c (~50 lines, requires care)**: State the Pell-safety subfamily condition from S1c (PR #18431) using `cartesianLatticeFormD` and `QuadraticMap.polarBilin`. This is the Lean home for the open mathematical content of S1c. Result: a `Prop` definition `pellSafety (p q : ℕ) (N : ℕ)` whose decidability for fixed $(p, q, N)$ becomes a *finite* computation (testable by `decide` for small cases).

S2c is the natural bridge from "S1c verified $N = 14$ for $(p, q) = (2, 5)$" to an actual Lean check that runs.

## Honesty

- This S1d note is a **doc-only Mathlib-API-audit PREP**. 0 Lean lines, 0 sorry deltas, 0 axiom deltas.
- The factorisation `Cartesian-lattice form = weightedSumSquares ℤ (primeWeight d)` is **mathematically trivial** — it is literally the definition. The contribution is identifying that Mathlib already provides the abstract API, so S2 can cite rather than define.
- The Tier 1 / Tier 2 split is **stylistic**, not novel. Any thoughtful Lean implementer would arrive at it; this note documents it explicitly to align the next-action S2 PR.
- The axiom count **does not improve**. Three axioms (4-point property, distance-count bound, Solymosi–Vu) remain. What improves is the *infrastructure-to-axiom ratio*.
- S1b's falsification is **correct**. The Cartesian-lattice with prime weights $(1, 2, 3)$ does not satisfy the naïve 4-point property at $d = 3$. Whatever axiomatised version of the form's "4-point property" S2 adopts, it must be either:
  - a subfamily condition (Pell-safety, per S1c), or
  - a different weighting scheme entirely (e.g., $(2, 3, 5)$ skipping the trivial weight 1 — flagged by S1b for future exploration).
- This note **does not endorse one option over the other**. It only sets up the ambient API so that whichever route S2 takes can be expressed cleanly.

## References

- Mathlib `QuadraticForm.weightedSumSquares` — `Mathlib/LinearAlgebra/QuadraticForm/Basic.lean` line 1371. Defined for `ι : Type*` with `[Fintype ι]`, `R : CommRing`, `S` acting on `R` via `DistribMulAction`. The `_apply` lemma gives `∑ i, w i • (v i * v i)`.
- Mathlib `QuadraticMap.polarBilin` — same file, line ~600. Gives the bilinear-form polar of any `QuadraticMap`; the relevant tool for S1c's $B_{p,q}$.
- Mathlib `Nat.nth Nat.Prime` — `Mathlib/Data/Nat/Nth.lean`. Provides the prime-indexing function for `primeWeight d`.
- PR #18322 (S1) — original Cartesian-lattice axiomatic plan.
- PR #18421 (S1b) — falsification at $d = 3$, $k = 1$.
- PR #18431 (S1c) — Pell-safety condition restoration; weighted bilinear form $B_{p,q}$.
- Parent gallery entry: `proofs/Proofs/Erdos659OQ01.lean` (ℝ² result with `fourPointProperty` over `Finset (ℝ × ℝ)`, 3 axioms).

## Anti-targets (S2 should NOT do these)

- **Do not** define `cartesianLatticeFormD` as a raw `Finset.sum` literal. Use `weightedSumSquares` directly so future Mathlib improvements to the API propagate automatically.
- **Do not** define a fresh `ternaryForm` / `quaternaryForm` / etc. — `weightedSumSquares ℤ (primeWeight d)` covers all $d$ uniformly.
- **Do not** axiomatise `dist_sq_eq_weightedSumSquares`. It is a ~10-line proof; it must be derived.
- **Do not** axiomatise positive-definiteness of `cartesianLatticeFormD`. The weights are positive integers; positive-definiteness follows from `weightedSumSquares_pos_iff` (if it exists; if not, a 2-line `Finset.sum_pos` argument).
- **Do not** attempt to prove the 4-point property at this stage. S1b shows the naïve form is false; either accept S1c's Pell-safety subfamily axiomatically or defer to S2c+.

## Stop conditions

This S1d iteration is complete when:

1. ✅ The recasting `Cartesian-lattice form = weightedSumSquares ℤ (primeWeight d)` is documented.
2. ✅ The Tier 1 / Tier 2 split is laid out with one-paragraph rationale.
3. ✅ Three concrete S2a/S2b/S2c targets are stated with rough line-count estimates.
4. ✅ Anti-targets and stop conditions are explicit (this section).
5. ✅ No edits to `problem.md` / `knowledge.md` / `state.md` / json. Pristine session-file addition only.

All five stop conditions are met by this file.
