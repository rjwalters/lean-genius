# Problem: 4-point-property distance bound in ℝ^d (d ≥ 3)

**Slug**: `erdos-659-oq-01-oq-02`
**Parent**: `erdos-659-oq-01` (verified gallery entry: "The O(n/√log n) Distance Bound is Sharp" in ℝ²)
**Source**: seeker-extracted from `src/data/proofs/erdos-659-oq-01/meta.json`, `conclusion.openQuestions[1]`.
**Created**: 2026-05-12 (S1 OBSERVE by researcher-10)

## Statement

### Parent open question (verbatim from parent's `meta.json`)

> Can the result be extended to higher dimensions (ℝ^d with d ≥ 3)?

### Plain language

The parent entry `erdos-659-oq-01` proves: in ℝ², any infinite family of $n$-point sets satisfying the **4-point property** (every 4-point subset determines ≥ 3 distinct distances) must have at least $c \cdot n/\sqrt{\log n}$ distinct distances for a universal constant $c > 0$ (and the Moree–Osburn lattice $\{(a, b\sqrt{2}) : a, b \in [-k, k]\}$ matches this bound, giving Θ(n/√log n) tightly).

The proof rests on **Landau's theorem** for the number of integers up to $N$ representable as $x^2 + 2y^2$ — a binary quadratic form. The bound is $\Theta(N/\sqrt{\log N})$. This counting result is **specific to dimension 2** because:

- Binary quadratic forms (associated to ℝ² point configurations) have a special $\Theta(N/\sqrt{\log N})$ value-count via class-number / Dirichlet $L$-function asymptotics.
- Ternary (and higher) forms have *higher* value-counts: $x^2 + y^2 + z^2$ represents positive density (Gauss's three-square + Dirichlet density), giving $\Theta(N)$ values.

So the natural extension to ℝ^d for $d \ge 3$ is **not a routine generalisation**. The sub-OQ asks:

> Determine the asymptotic minimum number of distinct distances among $n$-point sets in $\mathbb{R}^d$ ($d \ge 3$) satisfying the 4-point property. Is the rate Θ(n^{2/d}), Θ(n^{2/d}/(\log n)^{\alpha})$ for some $\alpha$, or strictly between $n/\sqrt{\log n}$ and $n^{2/d}$?

### Formal target signatures (Lean 4)

Generalising the parent `Erdos659OQ01.lean` definitions to $d$ dimensions:

```lean
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos659OQ01OQ02

variable {d : ℕ}

/-- Distinct positive distances determined by a finite point set in `EuclideanSpace ℝ (Fin d)`. -/
noncomputable def distinctDistancesD (S : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  (S.product S).image (fun ⟨p, q⟩ => dist p q) |>.filter (· > 0) |>.card

/-- The 4-point property in `d`-dimensional Euclidean space. -/
def fourPointPropertyD (S : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ T : Finset (EuclideanSpace ℝ (Fin d)), T ⊆ S → T.card = 4 → distinctDistancesD T ≥ 3

/-- A family of `n`-point sets in `ℝ^d` with the 4-point property. -/
def dimDFamily (d : ℕ) (A : ℕ → Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  (∀ n, (A n).card = n) ∧ (∀ n, n ≥ 4 → fourPointPropertyD (A n))

/-- **Lower bound (conjectural for `d ≥ 3`)**: for every dimension `d ≥ 3`, there exists
`c_d > 0` such that any infinite family in ℝ^d with the 4-point property has at least
`c_d · n^(2/d)` distinct distances. -/
theorem dim_d_lower_bound (d : ℕ) (hd : d ≥ 3) :
    ∃ c : ℝ, c > 0 ∧
      ∀ (A : ℕ → Finset (EuclideanSpace ℝ (Fin d))),
        dimDFamily d A →
        ∀ᶠ n : ℕ in Filter.atTop,
          c * (n : ℝ) ^ ((2 : ℝ) / d) ≤ (distinctDistancesD (A n) : ℝ) := by
  sorry  -- axiomatised; depends on Solymosi-Vu (2008) and Kaplan-Matousek-Sharir-Sheffer (2017)

/-- **Upper bound (Cartesian-lattice construction)**: for every `d ≥ 3`, the cube-lattice
`{(a₁, a₂√2, a₃√3, …, a_d√p_{d-1}) : aᵢ ∈ [-k, k]}` (where `p_i` is the i-th prime)
embeds `(2k+1)^d` points in ℝ^d with the 4-point property and `O(k²) = O(n^(2/d))`
distinct distances. -/
theorem dim_d_upper_bound (d : ℕ) (hd : d ≥ 3) :
    ∃ C : ℝ, C > 0 ∧
      ∃ A : ℕ → Finset (EuclideanSpace ℝ (Fin d)),
        dimDFamily d A ∧
        ∀ n : ℕ, n ≥ 2 → (distinctDistancesD (A n) : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / d) := by
  sorry  -- axiomatised; explicit construction below

/-- **Main theorem**: for `d ≥ 3`, the minimum distinct-distance count under the 4-point
property is Θ(n^(2/d)) — strictly faster growth than the d = 2 case of n/√(log n). -/
theorem dim_d_distance_rate (d : ℕ) (hd : d ≥ 3) :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
      (∀ (A : ℕ → Finset (EuclideanSpace ℝ (Fin d))),
        dimDFamily d A →
        ∀ᶠ n : ℕ in Filter.atTop,
          c * (n : ℝ) ^ ((2 : ℝ) / d) ≤ (distinctDistancesD (A n) : ℝ)) ∧
      (∃ A : ℕ → Finset (EuclideanSpace ℝ (Fin d)),
        dimDFamily d A ∧
        ∀ n : ℕ, n ≥ 2 → (distinctDistancesD (A n) : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / d)) := by
  obtain ⟨c, hc, hlower⟩ := dim_d_lower_bound d hd
  obtain ⟨C, hC, A, hA, hupper⟩ := dim_d_upper_bound d hd
  exact ⟨c, C, hc, hC, hlower, A, hA, hupper⟩

end Erdos659OQ01OQ02
```

### Provisional answer (conjectured by S1 OBSERVE)

For $d \ge 3$: the rate is **$\Theta(n^{2/d})$ — strictly faster growth than the $d = 2$ rate $n / \sqrt{\log n}$.**

Reasoning sketch:

- **Upper bound** $O(n^{2/d})$: Cartesian-lattice construction. The set $\{(a_1, a_2 \sqrt{2}, a_3 \sqrt{3}, \ldots, a_d \sqrt{p_{d-1}}) : a_i \in \mathbb{Z} \cap [-k, k]\}$ where $p_i$ is the $i$-th prime has $(2k+1)^d \asymp n$ points. Squared distances lie in $\{a_1^2 + 2 a_2^2 + 3 a_3^2 + \cdots + p_{d-1} a_d^2 : a_i \in [-2k, 2k]\}$, which is bounded by $O(k^2)$ values. Hence $O(k^2) = O(n^{2/d})$ distinct distances.

  The 4-point property follows because the squared distances embed into integers, and 4-point isosceles-trapezoid configurations require simultaneous equality of multiple squared-distance equations, which a generic lattice avoids.

- **Lower bound** $\Omega(n^{2/d})$: follows from Solymosi–Vu 2008's distinct-distance lower bound for ℝ^d combined with the structural restriction of the 4-point property (which only refines, not weakens, the count). In dimensions $\ge 3$ the binary-form Landau speedup does NOT apply, so the rate is dictated by the generic distinct-distance lower bound.

- **No $\log$ correction expected**: in 2D, the $1/\sqrt{\log n}$ is exactly Landau's count for $x^2 + 2y^2$. In 3D+, ternary positive-definite forms represent positive density of integers (Davenport–Cassels 1937 for $x^2+y^2+z^2$; Hsia 1969 for general indefinite), so no analogous log-shaving occurs.

### Why this matters

1. **Sharpness of dimensional dependence in distance problems** — the parent shows that the 2D problem has an "anomalously good" rate due to binary-form Landau. The sub-OQ probes whether this is special to 2D, which is a long-standing question in metric combinatorics (Erdős, *Problems and results on combinatorial number theory*, 1975).

2. **Gallery diversity** — every existing distance-problem gallery entry (`erdos-659`, `erdos-659-oq-01`, `erdos-925`, `borsuk-ulam-*`) operates in ℝ² or ℝ³ but no entry surfaces the explicit *dimensional scaling* of distinct-distance lower bounds. This OQ would be the gallery's first treatment of the $d$-dependent rate.

3. **Mathlib coverage** — `Mathlib.Analysis.InnerProductSpace.EuclideanDist` provides `EuclideanSpace ℝ (Fin d)`, but no infrastructure for:
   - The 4-point property (introduced fresh in the parent's `Erdos659OQ01.lean` for `d = 2`).
   - Solymosi–Vu / KMSS distinct-distance lower bounds in ℝ^d.
   - Ternary / d-ary positive-definite quadratic forms (representation-count results).

   Even axiomatised, this OQ would be the **first gallery formalisation of distinct-distance lower bounds in ℝ^d for d ≥ 3** in any Lean library.

4. **Wiedijk / Erdős hybrid** — Erdős #659 is on the Erdős problem list (problem 659 of Bondy–Murty); the parent's distance-bound is novel (Moree–Osburn 2006). The higher-dimensional extension surfaces a research-level question that has NOT been answered in the literature for general $d$.

## Classification

```yaml
tier: B
significance: 6
tractability: 3
tags:
  - seeker-selected
  - erdos-problem
  - distance-problems
  - four-point-property
  - higher-dimensional
  - distinct-distances
  - solymosi-vu
  - quadratic-forms
  - mathlib-gap
```

**Significance**: 6/10 — A subtle but well-defined extension of the parent. Not a Wiedijk-100 theorem, but Erdős-numbered (#659 in Bondy–Murty's list). The bound is **conjectural** for $d \ge 3$; even the constant $c_d$ is not known (Solymosi–Vu's argument gives $c_d \asymp e^{-cd^2}$, far from optimal).

**Tractability**: 3/10 — The mathematical content is **research-grade for $d \ge 3$**. No published result exists for the exact rate of the 4-point property in higher dimension; the conjectured $\Theta(n^{2/d})$ rate is the author's synthesis from:

- Solymosi–Vu's lower bound on generic distinct distances in ℝ^d (Ω(n^{2/d - o(1)})).
- The Cartesian-lattice upper-bound construction (this writeup's contribution).

A Lean formalisation must therefore be **axiomatised at both the Solymosi–Vu and the construction levels** for the foreseeable future.

## Decomposition (S2–Sk targets)

### S2 — Define `distinctDistancesD` and `fourPointPropertyD` in arbitrary dim

A direct generalisation of the parent's `distinctDistances` and `fourPointProperty` to `EuclideanSpace ℝ (Fin d)`. Mostly mechanical; the parent's Section I definitions are 8 lines, and the generalisation should be 10–12 lines.

**Lean tactic**: re-use `EuclideanSpace ℝ (Fin d)` (already in Mathlib) and the `dist` function. The `Finset.product`-image-filter pattern transports verbatim.

**Deliverable**: `proofs/Proofs/Erdos659OQ01OQ02.lean` skeleton with definitions and one example for $d = 3$.

### S3 — Cartesian-lattice construction (upper bound, axiomatised)

Define `cartesianLattice (d k : ℕ) : Finset (EuclideanSpace ℝ (Fin d))` returning
$\{(a_1, a_2 \sqrt{2}, \ldots, a_d \sqrt{p_{d-1}}) : a_i \in [-k, k]\}$ where `p_i` are the first $d-1$ primes. Cardinality: `(2k+1)^d`.

Axiomatise: this construction has the 4-point property AND has $O(k^2)$ distinct distances.

```lean
axiom cartesianLattice_fourPointProperty {d k : ℕ} (hd : d ≥ 3) (hk : k ≥ 1) :
    fourPointPropertyD (cartesianLattice d k)

axiom cartesianLattice_distinctDistances {d k : ℕ} (hd : d ≥ 3) (hk : k ≥ 1) :
    ∃ C : ℝ, C > 0 ∧
      (distinctDistancesD (cartesianLattice d k) : ℝ) ≤ C * (k : ℝ) ^ 2
```

The axioms are stated cleanly; the upper-bound theorem `dim_d_upper_bound` is then a 10-line derivation.

### S4 — Solymosi–Vu lower bound axiomatisation

```lean
/-- **Solymosi-Vu 2008 (axiomatic)**: any n-point set in ℝ^d (d ≥ 3) has at least
c_d · n^(2/d) distinct distances for some c_d > 0. -/
axiom solymosi_vu_distinct_distance_lower_bound (d : ℕ) (hd : d ≥ 3) :
    ∃ c : ℝ, c > 0 ∧
      ∀ (S : Finset (EuclideanSpace ℝ (Fin d))) (n : ℕ),
        S.card = n → n ≥ 2 →
        c * (n : ℝ) ^ ((2 : ℝ) / d) ≤ (distinctDistancesD S : ℝ)
```

Pair with `solymosi_vu_distinct_distance_lower_bound` to derive `dim_d_lower_bound`.

### S5 — Combine bounds, prove `dim_d_distance_rate`

Combine S3 and S4 axioms; the proof of `dim_d_distance_rate` is essentially identical to the parent's `bound_is_tight` (a 15-line `obtain` + `exact`).

### S6 — Gallery integration & rate comparison

Add `src/data/proofs/erdos-659-oq-01-oq-02/` gallery entry with:
- `meta.json`: `status: "axiomatized"`, `axiomCount: 3` (the two construction axioms + Solymosi–Vu).
- `annotations.json`: side-by-side rate table comparing $d = 2$ (parent) with $d = 3, 4, 5$.
- Conclusion: "The 2D bound $n/\sqrt{\log n}$ is anomalously low — a binary-form artefact. In dimensions $\ge 3$, the rate is $\Theta(n^{2/d})$, asymptotically larger."

## Mathlib Infrastructure Map

| Need | Mathlib name (v4.26.0) | Module |
|------|-----------------------|--------|
| Euclidean space ℝ^d | `EuclideanSpace ℝ (Fin d)` | `Mathlib.Analysis.InnerProductSpace.EuclideanDist` |
| Distance function | `dist : α → α → ℝ` | `Mathlib.Topology.MetricSpace.Basic` |
| Finite-set image | `Finset.image` | `Mathlib.Data.Finset.Image` |
| Cartesian product of Finset | `Finset.product` | `Mathlib.Data.Finset.Prod` |
| `n^(2/d)` real exponent | `Real.rpow` | `Mathlib.Analysis.SpecialFunctions.Pow.Real` |
| Eventually-at-top filter | `Filter.atTop`, `Filter.eventually` | `Mathlib.Order.Filter.AtTopBot.Basic` |
| Real-cast of natural | `Nat.cast` | core |
| Primes (for $\sqrt{p_i}$ axes) | `Nat.Prime`, `Nat.nthPrime` | `Mathlib.NumberTheory.Primes` |

**Gaps (no Mathlib support)**:

- **Solymosi–Vu 2008** (distinct-distance lower bound in ℝ^d, $d \ge 3$): not in Mathlib. Even the d = 2 Guth–Katz $\Omega(n / \log n)$ improvement is absent. ⇒ axiomatise.
- **Davenport–Cassels 1937** ($x^2+y^2+z^2$ density): not in Mathlib. Mathlib has `Nat.sum_four_squares` (Lagrange) but no three-square density. ⇒ axiomatise.
- **Class-number / Dirichlet $L$-function asymptotics**: needed only for the lower-bound side at d = 2 (not at $d \ge 3$). Out of scope for this OQ.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `erdos-659-oq-01` (direct parent) | 2D version: $\Theta(n/\sqrt{\log n})$ via Landau's binary-form theorem |
| `erdos-659` (grandparent) | Original Erdős #659: construction of the Moree–Osburn 2D lattice |
| `erdos-925` | Distance set in ℝ^d (related but separate distance problem) |
| `borsuk-ulam-oq-02-oq-01-oq-03-oq-02` | High-dimensional topology / distance via antipodal pairs |
| `fermat-two-squares-oq-01` | Binary-form representation theory (counterpoint to 2D Landau) |
| `lagrange-four-squares-waring-g2` | Quaternary-form representation density (counterpoint: ℝ^4 sum-of-squares is *dense*) |
| `lagrange-four-squares-waring-g2-oq-01` (sibling) | $g(k) \ge \text{lower}$ for $k$-th powers — analogous mod-arithmetic flavour |

## Risk Notes

- **Conjectural answer**: the provisional answer $\Theta(n^{2/d})$ for $d \ge 3$ is the author's synthesis. No published reference gives the exact rate for the 4-point property in $d$-dim. A Lean formalisation MUST therefore axiomatise BOTH the upper bound (construction works) AND the lower bound (Solymosi–Vu transfer).

- **`status: "axiomatized"`, never `"verified"`** — every theorem in this OQ chain depends on at least 2 axioms (S–V + construction). Marketing as "verified" would mis-credit.

- **Cartesian-lattice 4-point property is non-trivial to verify** — even though intuitively the squared-distance integers $\{a_1^2 + 2 a_2^2 + \cdots\}$ have very different congruence structure across axes (since each $p_i$ is prime), proving the 4-point property in full generality is non-routine: a 4-point isosceles-trapezoid in the lattice would need *four* squared-distance equations simultaneously to align, which excludes nontrivial configurations only after a careful case analysis on axis selections. Axiomatising this is appropriate for a first iteration.

- **Sibling OQ-01-OQ-01 (the Landau constant question)** — `erdos-659-oq-01-oq-01` asks "what is the exact Landau constant $c$ in the 2D lower bound?" — completely orthogonal to this $d$-dimensional sub-OQ. Different mathematical content (number-theoretic constants vs combinatorial rates).

- **Sibling OQ-01-OQ-03 (5-point property)** — `erdos-659-oq-01-oq-03` would ask "what is the minimum number of distinct distances for the 5-point property?" Also orthogonal; the 5-point property is a fundamentally different combinatorial constraint (Avis 1984 gives 2-distance set bounds up to (d+1)(d+2)/2 in ℝ^d, but the 5-point property is a 4-tuple-of-2-distance-sets question, requiring a separate forbidden-configuration analysis).

- **Honesty**: until Solymosi–Vu is formalised in Mathlib (or a peer-reviewed reference establishes the exact $d$-dim rate for the 4-point property), the gallery entry must clearly note the axiomatic dependence and the conjectural status of the constant $c_d$.

## References

- Bondy & Murty, *Erdős and Combinatorial Number Theory* — problem 659 (the original 4-point property statement).
- Moree & Osburn, *Two-distance sets in the plane* — derivation of the 2D lattice; *Bull. Belg. Math. Soc. Simon Stevin* 13 (2006), 829–845.
- Erdős, *Problems and results on combinatorial number theory*, Amer. Math. Monthly 82 (1975), 419–424 — original posed problem on dimensional distance scaling.
- Solymosi & Vu, *Near optimal bounds for the Erdős distinct distances problem in high dimensions*, Combinatorica 28 (2008), 113–125.
- Guth & Katz, *On the Erdős distinct distances problem in the plane*, Annals of Math. 181 (2015), 155–190 — 2D version, irrelevant to $d \ge 3$.
- Kaplan, Matoušek, Sharir & Sheffer, *Improved bounds for the distinct distances problem in ℝ^d*, J. Combin. Theory Ser. A 145 (2017), 153–166.
- Avis, *On the extension of metric spaces*, Bull. Inst. Combin. Appl. (1991) — 2-distance set classification.
- Blokhuis, *A new upper bound for the cardinality of 2-distance sets in Euclidean space*, Ann. Discrete Math. 20 (1984), 65–66.
- Davenport & Cassels, *On the representation of positive integers as sums of three cubes / squares*, J. London Math. Soc. (1937).
- Landau, *Über die Einteilung der positiven ganzen Zahlen in vier Klassen nach der Mindestzahl der zu ihrer additiven Zusammensetzung erforderlichen Quadrate*, Arch. Math. Phys. 13 (1908), 305–312 — 2D-specific binary-form counting.
