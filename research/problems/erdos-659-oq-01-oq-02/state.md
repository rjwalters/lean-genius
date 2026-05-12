# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12 (S1)
**Iteration**: 1

## Current Focus

S1 (researcher-10): OBSERVE survey for `erdos-659-oq-01-oq-02` — the seeker-extracted child of the verified gallery entry `erdos-659-oq-01` ("The O(n/√log n) Distance Bound is Sharp" in ℝ²). The sub-OQ asks the natural higher-dimensional extension:

> Can the result be extended to higher dimensions (ℝ^d with d ≥ 3)?

This iteration produces:

- `problem.md` — formal problem statement with full Lean target signatures (`distinctDistancesD`, `fourPointPropertyD`, `dim_d_lower_bound`, `dim_d_upper_bound`, `dim_d_distance_rate`); decomposition into S2–S6 deliverables; Mathlib infrastructure map.
- `knowledge.md` — historical timeline (Landau 1908 → Bernays 1912 → Erdős 1946 → Solymosi–Vu 2008 → Moree–Osburn 2006 → Guth–Katz 2015 → KMSS 2017); Cartesian-lattice construction computation; Mathlib gap table; computational verification notes for $k = 10$ in $d = 3, 4$.
- `state.md` (this file) — phase NEW → OBSERVE.

No Lean changes in S1.

## Active Approach

**The 2D result does NOT extend in the same form** — the answer for $d \ge 3$ is qualitatively different.

The parent's 2D rate $\Theta(n/\sqrt{\log n})$ rests on **Landau's binary-form theorem** (the count of integers $\le N$ representable by a positive-definite binary quadratic form is $\Theta(N/\sqrt{\log N})$). This rate is **2D-specific**:

- In 2D, binary forms have a "class-number-1 ($L$-function)" counting profile giving the $\sqrt{\log}$ factor.
- In 3D and higher, ternary/d-ary positive-definite forms represent positive density of integers (Bernays 1912, Davenport–Cassels 1937), giving a linear-in-$N$ count.

**Conjectured higher-dimensional rate**: $\Theta(n^{2/d})$ for the 4-point property in ℝ^d, $d \ge 3$.

| $d$ | Rate (4-point property) | Tool |
|----:|:-----------------------|:-----|
| 2 | $\Theta(n/\sqrt{\log n})$ | Landau (1908), Moree–Osburn (2006) |
| 3 | $\Theta(n^{2/3})$ (conjectural) | Solymosi–Vu (2008), Cartesian-lattice construction |
| 4 | $\Theta(n^{1/2})$ (conjectural) | KMSS (2017), Cartesian-lattice construction |
| $\ge 5$ | $\Theta(n^{2/d})$ (conjectural) | analogous |

### Upper bound — Cartesian lattice construction

$L_d(k) := \{(a_1, a_2 \sqrt{2}, a_3 \sqrt{3}, \ldots, a_d \sqrt{p_{d-1}}) : a_i \in \mathbb{Z} \cap [-k, k]\}$ where $p_i$ is the $i$-th prime.

Cardinality $(2k+1)^d \asymp k^d = n$. Squared distances lie in $\{Q(\delta_1, \ldots, \delta_d) = \delta_1^2 + 2 \delta_2^2 + \cdots + p_{d-1} \delta_d^2 : \delta_i \in [0, 2k]\}$, bounded by $k^2 \cdot (1 + 2 + \cdots + p_{d-1}) = O(k^2)$ values. Hence $O(n^{2/d})$ distinct distances.

### Lower bound — Solymosi–Vu transfer

The 4-point property only *restricts* the family of $n$-point sets; it cannot increase the minimum number of distinct distances over the generic distance problem. So any 4-point-property family in ℝ^d ($d \ge 3$) satisfies
$$ \mathrm{distinctDistances} \ge \Delta_d(n) \ge \Omega(n^{2/d - \epsilon}) \quad \text{(Solymosi-Vu 2008)}. $$

Matching the upper bound up to $\epsilon$.

## Blockers

None mathematical for S1 (this is an OBSERVE iteration).

Practical infrastructure constraints (deferred to S2+):

- **No Mathlib Solymosi–Vu**: the lower-bound side must be axiomatised.
- **No Mathlib Davenport–Cassels density**: not directly needed for axiomatised S2, but a prerequisite for any future formal-proof iteration.
- **Cartesian-lattice 4-point property is non-routine**: even though intuitively true (prime-multiplier separation), a Lean proof requires a careful case analysis on 4-tuple configurations. Axiomatised at S3.

## Next Action

**S2 (any researcher)**: Define `distinctDistancesD` and `fourPointPropertyD` in `proofs/Proofs/Erdos659OQ01OQ02.lean`. The structure mirrors the parent `Erdos659OQ01.lean` Section I but parameterised on `d : ℕ`.

Concrete plan:

```lean
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos659OQ01OQ02

variable {d : ℕ}

/-- Distinct positive distances determined by a finite point set in `EuclideanSpace ℝ (Fin d)`. -/
noncomputable def distinctDistancesD
    (S : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  (S.product S).image (fun ⟨p, q⟩ => dist p q) |>.filter (· > 0) |>.card

/-- The 4-point property in `d`-dimensional Euclidean space. -/
def fourPointPropertyD (S : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ T : Finset (EuclideanSpace ℝ (Fin d)),
    T ⊆ S → T.card = 4 → distinctDistancesD T ≥ 3

/-- A family of `n`-point sets in `ℝ^d` with the 4-point property for all n ≥ 4. -/
def dimDFamily (d : ℕ) (A : ℕ → Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  (∀ n, (A n).card = n) ∧ (∀ n, n ≥ 4 → fourPointPropertyD (A n))

/-- Sanity check at d = 2: the parent's 2D definitions agree (modulo Fin 2 ↔ ℝ × ℝ coercion). -/
example (S : Finset (EuclideanSpace ℝ (Fin 2))) :
    distinctDistancesD S = (S.product S).image (fun ⟨p, q⟩ => dist p q) |>.filter (· > 0) |>.card := rfl

end Erdos659OQ01OQ02
```

Expected line count: ~25 lines including docstrings. No theorems yet (those come in S3-S5).

**S3 (after S2)**: Define `cartesianLattice` and axiomatise its 4-point property + distance-count bound.
**S4 (after S3)**: Axiomatise Solymosi–Vu.
**S5 (after S4)**: Combine to prove `dim_d_distance_rate`.
**S6 (after S5)**: Gallery integration with `axiomatized` status.

## Honesty

This S1 OBSERVE iteration is a **pure survey**. It produces:

- 0 new Lean theorems
- 0 sorry deltas
- 0 axiom deltas
- 3 markdown files (`problem.md`, `knowledge.md`, this `state.md`)
- 1 gallery JSON entry (`src/data/research/problems/erdos-659-oq-01-oq-02.json`)

The provisional rate $\Theta(n^{2/d})$ is the author's synthesis from published bounds (Solymosi–Vu 2008 for the lower side, Cartesian-lattice construction for the upper). **No published paper gives the exact rate for the 4-point property in $d \ge 3$**; this OQ probes a genuinely open question in metric combinatorics.

The future Lean entry will be `status: "axiomatized"` with `axiomCount ≥ 3`.
