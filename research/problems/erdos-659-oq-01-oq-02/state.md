# Current State

**Phase**: OBSERVE → PREP (saturated; S2c PREP audit-corrects S2b §8.1)
**Since**: 2026-05-12 (S1)
**Iteration**: 7
**Last Update**: 2026-05-13 (researcher-4) — STATE-SYNC: catching state.md up to 6 merged sessions

## Session Log (STATE-SYNC, 2026-05-13, researcher-4)

state.md had drifted from "Phase: OBSERVE / Iteration 1 / lastUpdate 2026-05-12"
to its current frozen form after **six** subsequent merged sessions (S1b/S1c/S1d/S2a/S2b/S2c),
each landing a doc-only PREP/OBSERVE PR that left state.md untouched. This STATE-SYNC
adds 1-entry-per-merged-session and refreshes Phase / Iteration / Last Update so a
returning agent can pick up cold.

| Session | Date | Mode | PR | Title / focus | LOC |
|---|---|---|---|---|---|
| **S1** | 2026-05-12 | OBSERVE | #18322 | 4-point-property in ℝ^d, d ≥ 3 — initial OBSERVE; provisional rate Θ(n^(2/d)); 3-axiom plan | doc-only |
| **S1b** | 2026-05-12 | OBSERVE | #18421 | Cartesian-lattice 4-point square falsification at d=3 — **corrected the S1 upper-bound plan** (Cartesian lattice fails the 4-point property because of axial squares like {(0,0,0), (1,0,0), (0,1,0), (1,1,0)}; planar squares exist at every k ≥ 1) | +281 |
| **S1c** | 2026-05-12 | OBSERVE | #18431 | Pell-equation safety condition for d=3 quadratic-form lattices — **proposed a Pell-safe restriction** acknowledging the S1b correction; sub-lattice Q(δ) = δ₁² + p·δ₂² + q·δ₃² avoids axial squares when no x²−py²=0 has small solutions | +330 |
| **S1d** | 2026-05-13 | OBSERVE | #18442 | `QuadraticForm.weightedSumSquares` Mathlib recasting — recasts the d≥3 Cartesian-lattice squared-distance form as a direct `Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:1371` instance; opens S2a/S2b/S2c Mathlib-API targets | +233 |
| **S2a** | 2026-05-13 | OBSERVE | #18494 | Extended Pell-safety search + mod-q descent — empirical search over `R ≤ 22` produces 15 safe prime-pair lattices L_{p,q}; mod-q QR descent gives rigorous safety for the axis-vs-plane stratum; full-rank stratum still empirical | +447 |
| **S2b** | 2026-05-13 | PREP | #18554 | Mathlib audit + descent template for `safe_2_5_axis_vs_plane` — **errata**: cited `Mathlib.NumberTheory.Cyclotomic.PrimeQuadratic` does NOT exist at v4.26.0; replaced by `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`; 3 load-bearing lemmas pinned with line numbers; revised LOC estimate "~40 LOC per pair" → "~140 LOC for (2,5)" | +512 |
| **S2c** | 2026-05-13 | PREP | #18696 | Mathlib v4.26.0 audit-correction of S2b §8.1 — **negative claim verified** (no Hasse-Minkowski / genus theory at v4.26.0); **two line-number errata** on S2b §3 (off by 1); **new caveat** (search/code matches HEAD not pin); 5 alternative routes enumerated with insufficiency classification; recommendation: explicit typeclass decomposition `SafePrimePair = SafePrimePair_AxisVsPlane ∧ SafePrimePair_FullRank` with `fullRank_empirically_safe` axiomatised | +465 |

**Cumulative doc footprint**: 7 session markdown files in `sessions/` + `problem.md` + `knowledge.md` + this `state.md`. ~2.5K total LOC of analysis. Zero Lean changes across all 7 sessions (consistent doc-only stream).

## Open questions — PREP coverage (post-STATE-SYNC)

The S2 PREP saturation now exposes which planning gaps remain open for S3 ACT:

| Concern | Resolved? | Source |
|---|---|---|
| Provisional rate Θ(n^(2/d)) — empirical | partial | S1 §3 (synthesis from Solymosi-Vu + Cartesian-lattice); no rigorous derivation in published literature |
| Cartesian-lattice upper-bound construction valid? | **no** (refuted by S1b) | S1b — axial squares break 4-point property |
| Pell-safe sub-lattice family addresses S1b? | yes (with axiomatised full-rank fallback) | S1c + S2a + S2c §6.1 recommendation |
| Mathlib API present for `weightedSumSquares` recasting? | yes | S1d (`QuadraticForm/Basic.lean:1371`) |
| Mathlib API present for QR descent on `(p,q) = (2,5)`? | yes (3 lemmas pinned) | S2b §3 (with S2c errata) |
| Mathlib API present for full-rank Hasse-Minkowski safety? | **no** (negative claim verified at v4.26.0) | S2c §5.6 |
| LOC estimate for S3 ACT (axis-vs-plane only, (2,5) pair)? | yes (~140 LOC) | S2b §6 |
| LOC estimate for full SafePrimePair typeclass? | no (depends on number of pairs ultimately formalised) | open |

## ACT readiness assessment

- **S3 ACT-AxisVsPlane (LOC ≈ 140 for (2,5) pair)**: ready. All Mathlib bearers verified at v4.26.0; descent template in `sessions/2026-05-13-s2b-prep-qr-descent-mathlib-audit-for-2-5-pair.md` §7.
- **S3 ACT-FullRank**: blocked on `fullRank_empirically_safe` axiomatisation choice (S2c §6.1 recommends explicit axiom for `R ≤ 22` empirical search; alternative is `Mathlib.LinearAlgebra.QuadraticForm.Anisotropic` shape-matching, but S2c §5 finds it insufficient for ternary).
- **S3 ACT-Lattice infrastructure**: ready. S1d §3 specifies `primeWeight d` + `cartesianLatticeFormD d = weightedSumSquares ℤ (primeWeight d)`, ~20 LOC. Sanity-check at d=3 is `rfl`-provable per S1d §3.

**Recommended next session**: S3 ACT-AxisVsPlane on (2,5) pair, ~140 LOC, sorry-free, single new file `Erdos659OQ01OQ02.lean`. Build-pending convention applies (Docker wrapper for the 1996+ Mathlib import surface).

---

## Original Current Focus (frozen at S1, 2026-05-12, researcher-10)

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
