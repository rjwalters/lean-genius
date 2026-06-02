# Current State

**Phase**: ACT (S4 ACT DISCHARGED — three axis-vs-plane sorries proved; full-rank safety remains open)
**Since**: 2026-05-29 (S4 ACT discharge via PR #20921)
**Iteration**: 12 (was 10; S6 STATE-SYNC absorbs S4 ACT #20921)
**Last Update**: 2026-06-01T20:46Z (researcher-1) — S6 STATE-SYNC: absorbs S4 ACT #20921 (researcher-1-era, merged 2026-05-29T08:45Z) into state.md head + JSON. Pre-S6 drifts: state.md head still narrates S5 STATE-SYNC (iter 10); JSON `currentState.focus` still mentions "discharge the 3 strategic sorries" though they are proved; JSON `lastUpdate: 2026-05-16T16:10Z` (pre-discharge). The S4 ACT shipped: `proofs/Proofs/Erdos659OQ01OQ02.lean` is GREEN with 0 sorries, 0 axioms for the axis-vs-plane half. Refreshes `currentState.{phase, since, iteration, focus, nextAction, lastUpdate}` accordingly.

## S6 STATE-SYNC (researcher-1, 2026-06-01, doc-only)

Claim-random landed at 2026-06-01T20:44Z (T+3d post-S4 ACT merge). Pre-S6 drifts:

| Surface | Pre-S6 status | S6 disposition |
|---------|---------------|----------------|
| state.md head `Iteration` | 10 (matches S5 STATE-SYNC, BEHIND S4 ACT #20921 = iter 11) | → 12 (S6 STATE-SYNC) |
| state.md head `Phase` | "S3 SCAFFOLD shipped → S4 PREP + S4 PREP-2 ... ACT-ready for S5 ACT discharge" (stale: discharge happened) | → "S4 ACT DISCHARGED — three axis-vs-plane sorries proved" |
| state.md head `Last Update` | "2026-05-16T16:10Z ... S5 STATE-SYNC" | → "2026-06-01T20:46Z ... S6 STATE-SYNC" |
| JSON `currentState.focus` | "S5 STATE-SYNC ... absorbs S4 PREP-2 #19128 ..." (1 S behind) | refreshed to S4 ACT absorbed narrative |
| JSON `currentState.nextAction` | "discharge the 3 strategic sorries ... per S4 PREP-2 ... explicit Nat.strongRecOn descent bodies" (stale: discharged) | refreshed to next-step menu (full-rank safety; other safe pairs; Θ(n^{2/3}) assembly) |
| JSON `currentState.iteration` | 10 | → 12 |
| JSON `currentState.since` | "2026-05-16T16:10:00.000Z" | → "2026-05-29T08:45:00.000Z" (S4 ACT merge time) |
| JSON `currentState.phase` | "ACT" | unchanged (still ACT) |
| JSON `lastUpdate` | "2026-05-16T16:10:00.000Z" | → "2026-06-01T20:46:00.000Z" |
| `sessions/` last entry | `2026-05-16-s5-statesync-absorb-s4-prep-2.md` | NEW `2026-06-01-s6-statesync-absorb-s4-act.md` |

**No Lean / no meta.json / no problem.md / no knowledge.md / no sibling-slug / no lake-manifest edits.** The S4 ACT deliverable on `origin/main` (proofs/Proofs/Erdos659OQ01OQ02.lean with three proved descent theorems, 0 sorries, 0 axioms, Docker-verified GREEN) is unchanged.

See `sessions/2026-06-01-s6-statesync-absorb-s4-act.md` for full memo.

## Next-action menu (post S4 ACT discharge)

Three concrete candidates per the S4 ACT knowledge.md entry §Next-action candidates:

1. **Full-rank safety for (2,5)** — either elementary descent for genuinely-ternary equidistant configurations not reducible to one axis vs. a coordinate plane, or honest axiomatisation. S2c PREP §6.1 recommends explicit typeclass decomposition `SafePrimePair = SafePrimePair_AxisVsPlane ∧ SafePrimePair_FullRank` with `fullRank_empirically_safe` axiomatised, since Mathlib v4.26.0 lacks ternary Hasse-Minkowski infrastructure.
2. **Generalise to other safe prime pairs** — S2a identified 15 candidates with R ≤ 22; the safe ones are {(2,5), (2,13), (3,5), (5,7), (5,13), (7,13), (11,13)}. The descent template here applies whenever both `p` and `q · (±)` are quadratic non-residues mod a common small prime.
3. **Assemble the Θ(n^{2/3}) rate** — connect `SafePrimePair_*` to a `fourPointProperty` lattice family and the distinct-distance count. Requires axiomatising or proving the distance-count bound (S3 of original plan) and the Solymosi–Vu lower bound (S4 of original plan).

---

## S5 STATE-SYNC (researcher-9, 2026-05-16, doc-only)

Claim-random landed at 2026-05-16T16:08Z (T+2d post-S4 PREP-2 merge). Pre-S5 drifts:

| Surface | Pre-S5 status | S5 disposition |
|---------|---------------|----------------|
| state.md head `Iteration` | 9 (matches S4 PREP #19028, BEHIND S4 PREP-2 #19128) | → 10 |
| state.md head `Last Update` | "2026-05-14 ... S4 PREP" | → "2026-05-16T16:10Z ... S5 STATE-SYNC" |
| JSON `lastUpdate` | `null` | → `"2026-05-16T16:10:00.000Z"` |
| JSON `currentState.focus` | "S3 ACT SCAFFOLD shipped (PR #18947, iter 8): ..." (2 iters behind) | refreshed to S4 PREP-2 absorbed |
| JSON `currentState.nextAction` | S4 PREP-2 next-action narrative | refreshed to S5 ACT discharge plan |
| JSON `currentState.iteration` | 9 (matches S4 PREP) | → 10 |
| `sessions/` last entry | `2026-05-14-s4-prep-2-explicit-descent-bodies-for-three-sorries.md` | NEW `2026-05-16-s5-statesync-absorb-s4-prep-2.md` |

**No Lean / no meta.json / no problem.md / no knowledge.md / no sibling-slug / no lake-manifest edits.** The S4 PREP-2 deliverable on `origin/main` (3 explicit descent bodies for the 3 strategic sorries in `proofs/Proofs/Erdos659OQ01OQ02.lean`) is unchanged.

See `sessions/2026-05-16-s5-statesync-absorb-s4-prep-2.md` for full memo.



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

---

## Iteration 8 (researcher-1, 2026-05-13) — S3 ACT SCAFFOLD (merged, PR #18947)

**Outcome**: built — created `proofs/Proofs/Erdos659OQ01OQ02.lean` (133
LOC; **(build pending)** convention). Ships the outer scaffold for the
axis-vs-plane safety predicate at `(p, q) = (2, 5)`:

- `def safe_A`, `def safe_B`, `def safe_C` — the three QR equations
  isolated by S2b PREP §4 (`5c² = a² + 2b²`, `2b² = a² + 5c²`,
  `a² = 2b² + 5c²`).
- `theorem safe_A_holds`, `safe_B_holds`, `safe_C_holds` —
  **3 strategic sorries** (one per equation), descent bodies deferred
  to S4 ACT.
- `def SafePrimePair_AxisVsPlane (p q : ℕ)` — composite predicate
  parameterised on the prime pair.
- `theorem safe_2_5_axis_vs_plane : SafePrimePair_AxisVsPlane 2 5` —
  derived as the conjunction of the three `safe_*_holds`.

Sorries: 3 (strategic, all in `safe_*_holds`). Axioms: 0. The build is
pending pending Docker verification (recursive `.lake` symlink in the
researcher worktree precluded local `lake build`).

## Iteration 9 (researcher-12, 2026-05-14) — S4 PREP — ZMod 5 QR helpers

**Outcome**: built (Docker-verified — see Build status below) —
extended `proofs/Proofs/Erdos659OQ01OQ02.lean` (133 → ~165 LOC) with
**two decidable ZMod 5 helpers** that compress the mod-5 step of the
S4 ACT descent proofs to a 25-case `decide`. Also dropped the stale
`import Mathlib.Data.Int.Defs` left over from S3 ACT SCAFFOLD (the
module does not exist at v4.26.0 — surfaced by the first Docker
build attempt this iteration; this iter is the first Docker
verification of the OQ02 Lean file).

### What I added

```lean
import Mathlib.Data.ZMod.Basic   -- (new import)

/-- Mod-5 step for equation A: `a² + 2b² ≡ 0 (mod 5)` ⇔ `a = 0 ∧ b = 0`. -/
lemma zmod_5_a_sq_plus_2_b_sq_eq_zero_iff (a b : ZMod 5) :
    a ^ 2 + 2 * b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
  revert a b; decide

/-- Mod-5 step for equations B and C: `a² ≡ 2b² (mod 5)` ⇔ `a = 0 ∧ b = 0`. -/
lemma zmod_5_a_sq_eq_two_b_sq_iff (a b : ZMod 5) :
    a ^ 2 = 2 * b ^ 2 ↔ a = 0 ∧ b = 0 := by
  revert a b; decide
```

### Why these helpers, and why now

S2b PREP §4 sketches the mod-5 step via
`ZMod.exists_sq_eq_two_iff` (line 74 of
`Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`) and
`ZMod.exists_sq_eq_neg_two_iff` (line 80). The character-theoretic
route works, but the mod-5 reduction itself is finite combinatorics
over the 25 pairs `(a, b) ∈ ZMod 5 × ZMod 5`. A `decide` reflection
over the underlying `Decidable` instance closes both lemmas in two
lines of tactic and is mathematically equivalent to specialising
`exists_sq_eq_{two,neg_two}_iff` at `p = 5`.

Picking the `decide` form has three advantages:

1. **No `Fact (Nat.Prime 5)` instance plumbing** — the two
   QR-reciprocity routes need it (`haveI := fact_prime_five`),
   adding 1–2 LOC per call site. The `decide` form has no instance
   requirements.
2. **Single load-bearing lemma for B and C** — both equations reduce
   modulo 5 to "`a² = 2b²` in `ZMod 5`", and the same helper
   `zmod_5_a_sq_eq_two_b_sq_iff` discharges both. (The S2b PREP §4.2
   and §4.3 paths used two separate citations.)
3. **Trivially auditable** — `decide` over a 25-case finite type is a
   first-principles proof; an auditor can re-run it without any
   number-theory background.

### What this does NOT do

- Does **not** discharge `safe_A_holds`, `safe_B_holds`,
  `safe_C_holds` — the strategic sorries from S3 ACT SCAFFOLD
  remain. Those need the integer-side descent infrastructure
  (`Nat.strongRecOn` + substitution arithmetic), which is S4 ACT
  scope.
- Does **not** introduce new axioms or change `axiomCount`.
- Does **not** touch the full-rank safety predicate (S2c PREP §6.1)
  or full SafePrimePair conjunction.

### Next action (S4 ACT)

Lift the helpers into the descent proof of `safe_A_holds`
(~30 LOC body) following the S2b PREP §5 template:

1. From `5c² = a² + 2b²` and the new
   `zmod_5_a_sq_plus_2_b_sq_eq_zero_iff`, deduce `5 ∣ a` and `5 ∣ b`
   in ℤ.
2. Substitute `a = 5a'`, `b = 5b'`; rearrange to `c² = 5(a'² + 2b'²)`;
   apply `Int.Prime.dvd_natAbs_of_coe_dvd_sq` (line 38 of
   `Mathlib/Data/Int/NatPrime.lean`) to deduce `5 ∣ c`.
3. Substitute `c = 5c'`; get `5c'² = a'² + 2b'²` — same equation,
   smaller `a.natAbs + b.natAbs + c.natAbs`.
4. `Nat.strongRecOn` on the sum to close the descent.

`safe_B_holds` and `safe_C_holds` mirror the structure with the second
helper `zmod_5_a_sq_eq_two_b_sq_iff` doing the mod-5 step.

Estimated S4 ACT size: **~40–50 LOC total** for all three discharges
(down from the S2b PREP §5 estimate of ~50 LOC, after factoring out the
two helpers).

### Build status

**Build verified by Docker wrapper** — log
`.loom/logs/researcher-12-erdos659-s4-prep-build3.log`,
`✔ Build completed successfully (3058 jobs)`. Both helpers compile
cleanly via `decide`; the only warnings are the three pre-existing
strategic sorries (lines 118/126/134) inherited from S3 ACT SCAFFOLD.

Note: the first two Docker attempts failed because I ran the script
from the main repo path (`cd /Users/rwalters/GitHub/lean-genius`),
which mounts the main repo into the container — not the worktree. The
fix was to invoke `./proofs/scripts/docker-build.sh …` from the
worktree directory (`cwd: .loom/worktrees/researcher-12`); the script
resolves `REPO_ROOT` from `BASH_SOURCE` and mounts whichever working
tree contains the script invocation. Worth noting for future builds
from worktrees with uncommitted edits.

### Blockers

None. S4 ACT is unblocked: the mod-5 step is now a two-line lemma
call; the integer descent infrastructure is standard Mathlib
(`Nat.strongRecOn`, `Int.Prime.dvd_natAbs_of_coe_dvd_sq`).
