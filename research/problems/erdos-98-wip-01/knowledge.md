# Knowledge Base: erdos-98-wip-01

## Session 2026-07-21 (researcher-1) — pinned value h 4 = 2 (first value of h exceeding 1)

**Mode**: FRESH (continue). **Outcome**: progress — `h 4 = 2` pinned exactly.
**docker-built** `Proofs.Erdos98WIP01` OK (0 sorry / 0 axiom / no `native_decide`;
`#print axioms Erdos98WIP01.h_four` = `[propext, Classical.choice, Quot.sound]` only).

Executed the recorded next step (extend the pinned values beyond `h 3`). Both bounds are new.

**Upper bound `h 4 ≤ 2`** (`h_four_le_two`).
- The classical minimum-distance witness for 4 points, the **square**, is *disqualified*:
  its 4 vertices are concyclic, and general position forbids 4 concyclic points. So the
  square is not a witness for `h 4`.
- `centeredTriangleConfig : PointConfig 4` — the equilateral triangle
  `(1,0), (−½,√3⁄2), (−½,−√3⁄2)` together with its **centroid** `(0,0)`: a 2-distance set
  (circumradius `1`, side `√3`) that survives both nondegeneracy constraints.
- `centeredTriangleConfig_dist_mem` — every pairwise distance is `1` or `√3` (dist² is `1`
  or `3`; nonnegative sqrt). Key tactic fix: `!₂[…]` coordinate accessors are reduced by
  **`norm_num`**, not by `simp only [Matrix.cons_val_*]` (those args are flagged *unused*);
  mirror `equilateral_dist_off`'s `simp only [cfg, Fin.sum_univ_two, Real.dist_eq, sq_abs]`
  then `norm_num [hs2] <;> nlinarith [hs2]` (fallback for the `√3²=3` arithmetic).
- `noThreeCollinear`/`noFourConcyclic_centeredTriangleConfig` — the centroid is interior
  (no 3 collinear); the only point equidistant from the 3 vertices is the circumcenter =
  centroid, at distance `0 ≠ 1` from itself, so no 4 concyclic. Both needed
  `set_option maxHeartbeats 1000000 in` (64 / 256 `fin_cases` branches, √3 arithmetic).
  NB: `set_option … in` goes **before** the docstring, not between docstring and theorem.
- `numDistinctDistances_centeredTriangleConfig_le` — positive distances ⊆ `{1,√3}`, card ≤ 2.

**Lower bound `h 4 ≥ 2`** (`h_four_ge_two`), the harder half — pins the exact value.
- `not_four_equidistant` — four pairwise-equidistant points are impossible in `ℝ²`. Take
  difference vectors `vₖ = p_{k+1} − p₀` (`k : Fin 3`). Equidistance gives the Gram matrix
  `⟪vᵢ,vᵢ⟫ = r²`, `⟪vᵢ,vⱼ⟫ = r²/2` (`i≠j`) via `real_inner_self_eq_norm_sq` and
  `norm_sub_sq_real`. `Fintype.linearIndependent_iff` + `sum_inner` + `real_inner_smul_left`
  turn `∑ gₖ•vₖ = 0` into the 3×3 system `r²·½(I+J)·g = 0`; cancel `r² ≠ 0`
  (`linear_combination` + `mul_eq_zero`) to get `g = 0`. Then
  `LinearIndependent.fintype_card_le_finrank` vs `finrank_euclideanSpace_fin` gives `3 ≤ 2`,
  contradiction. **First use of the ambient dimension** (all earlier bounds are metric/comb.)
- `two_le_numDistinctDistances_four` — a 1-distance 4-config would force all six distances
  equal (`Finset.card_eq_one` on the positive-distance set), i.e. four equidistant points.
- `h_four : h 4 = 2 := le_antisymm h_four_le_two h_four_ge_two`.

**Reusable idiom** (recorded for `h 5`+): a 1-distance set in `ℝ^d` has `≤ d+1` points via
the Gram/linear-independence route above. The whole lower-bound block compiled first try.

**Next**: pin `h 5` (regular pentagon is concyclic → disqualified; need a non-concyclic
5-point 2/3-distance set, or show `h 5 ≥ 3`); abstract the equidistant⟹independent lemma.

## Session 2026-07-21 (researcher-1) — pinned value h 3 = 1 via explicit equilateral triangle

**Mode**: FRESH (continue). **Outcome**: progress — 6 axiom-free declarations,
**docker-built** `Proofs.Erdos98WIP01` OK (0 sorry / 0 axiom / no `native_decide`;
`#print axioms h_three` = `[propext, Classical.choice, Quot.sound]` only).

Executed the recorded next step: pin `h 3` exactly.

- `equilateralConfig : PointConfig 3` — the unit equilateral triangle
  `(0,0), (1,0), (½, √3⁄2)`.
- `equilateralConfig_injective` — the three abscissae `0, 1, ½` already differ, so the
  `x`-coordinate alone separates every pair (`norm_num [equilateralConfig]` on the 0-th
  coordinate).
- `noThreeCollinear_equilateralConfig` — a line through all three forces `c = 0`, then
  `a = 0`, then `b·(√3⁄2) = 0`; `√3 > 0` gives `b = 0`. The `√3` coefficient makes this
  genuinely **nonlinear** (unlike the right-triangle case), needing `nlinarith [hs, …]`
  with `hs : 0 < √3` (the negated-goal × `hs` product certificate).
- `noFourConcyclic_equilateralConfig` — vacuous (`noFourConcyclic_of_le_three`).
- `inGeneralPosition_equilateralConfig` — the triangle is in general position.
- `equilateral_dist_off {i j} (hij : i ≠ j) : dist (equ i) (equ j) = 1` — every side has
  length 1: `∑ (Δcoord)² = 1` via `(√3)² = 3`, then `EuclideanSpace.dist_eq` + `Real.sqrt_one`.
- `numDistinctDistances_equilateralConfig = 1` — **first exact computation** of
  `numDistinctDistances` for an explicit config: positive distances = `{1}` (diagonal
  pairs give 0, filtered out).
- `h_three : h 3 = 1` — equilateral witness ⟹ `h 3 ≤ 1`; `h_mono` + `h_two` ⟹
  `1 = h 2 ≤ h 3`. Squeeze ⟹ `h 2 = h 3 = 1`.

**Key Lean lesson.** `EuclideanSpace.dist_sq_eq` rewrites `dist x y ^ 2` into a sum over
`x.ofLp i` coordinate accesses that `Matrix.cons_val_*` do NOT reduce (they stay
`(![…] ⟨0,⋯⟩).ofLp 0`). Use `EuclideanSpace.dist_eq` instead — its `x i` is direct
function application, reduced by `simp only [equilateralConfig] ; norm_num`. Leftover
`1/4 + (√3/2)² = 1` closes with `nlinarith [hs]` (`hs : √3² = 3`); `norm_num` alone does
NOT expand `(√3/2)²` against `hs`.

**Honesty.** Parent Erdős #98 (`h(n)/n → ∞`) remains **OPEN**; only the conjectured rate
is the open piece. The elementary envelope gives only `1 ≤ h 3 ≤ 3` — the exact value
needs the equilateral witness. PR: extends #40147.

### Next Steps
- Improve the lower-bound constant beyond `/3` toward `(n−1)/2` or `≥ n`.
- Pin `h 4`: is it `1` (needs an impossible single-distance 4-config?) or `2`?
- Attack the conjectured rate `h n / n → ∞`.

## Session 2026-07-20 (researcher-1) — MONOTONICITY of h + pinned value h 2 = 1

**Mode**: FRESH (continue) — build on the linear lower bound. **Outcome**: progress
— 5 axiom-free declarations, **docker-built** `Proofs.Erdos98WIP01` OK (8577 jobs,
0 sorry / 0 axiom / no native_decide).

Proved the first **structural comparison across cardinalities** and the first
exactly-pinned value of `h`:

- `card_triple_image` / `card_quad_image` — injective-image cardinality helpers
  (`card {e i,e j,e k} = card {i,j,k}`) via `Finset.card_image_of_injective`.
- `inGeneralPosition_comp` — a sub-configuration `P ∘ e` chosen by an **injective**
  index map `e : Fin m → Fin n` inherits general position: injectivity composes, and
  any collinear/concyclic degeneracy of `P ∘ e` transports through `e` (which preserves
  the `card = 3` / `card = 4` distinctness) to a degeneracy of `P`, contradicting `hP`.
- `numDistinctDistances_comp_le` — `numDistinctDistances (P ∘ e) ≤ numDistinctDistances P`
  (every positive sub-config distance is realized by the image pair `(e p.1, e p.2)`).
- `h_mono : Monotone h` — delete the last point (`Fin.castSucc`) of the `h_attained`
  minimizer of `h (n+1)`; the restriction is general position with `≤` distinct distances,
  so `h n ≤ numDistinctDistances ≤ h (n+1)`. Via `monotone_nat_of_le_succ`.
- `h_two : h 2 = 1` — squeeze `1 ≤ 3·h 2` (`three_mul_h_ge 2`) against
  `h 2 ≤ (2 choose 2) = 1` (`h_le_choose_two 2`); `omega` closes. First exact value,
  no explicit distance computation.

**Why this is progress**: monotonicity is a genuine structural fact none of the
pointwise bounds provides; `h_two` demonstrates the lower/upper envelope is tight at
`n = 2`. At `n = 3` the same squeeze gives only `1 ≤ h 3 ≤ 3` (pinning `h 3 = 1` needs
an explicit equilateral-triangle witness — next step).

### Next
- Pin `h 3 = 1` via an explicit equilateral triangle (numDistinctDistances = 1); with
  `h_mono` this gives `h 2 = h 3 = 1`.
- Improve the lower-bound constant beyond `/3` (combine no-3-collinear + no-4-concyclic,
  or count from two base points) toward `h n ≥ (n-1)/2` / the conjectured `≥ n`.
- The conjectured RATE `h n / n → ∞` (Erdős #98 itself) is the sole remaining open piece;
  divergence `h n → ∞` is already elementary (`tendsto_h_atTop`).

## Session 2026-07-21 (researcher-1) — ELEMENTARY LINEAR LOWER BOUND n−1 ≤ 3·h n + unconditional h(n)→∞

**Mode**: FRESH build on the now-closed existence tower. **Outcome**: progress — first
lower bound on `h n` that **grows with n**, and an **unconditional** proof of `h(n)→∞`.
Docker-built `Proofs.Erdos98WIP01` (Build succeeded, 8577 jobs); 0 sorry / 0 axiom / no
native_decide.

**The idea (elementary, uses no-4-concyclic).** Fix a base point `P b`. Any circle centred
at `P b` meets the other `n−1` points in **at most three** of them — a fourth would be four
points equidistant from `P b`, i.e. four concyclic points (centre `P b`), which
`NoFourConcyclic` forbids. So the `n−1` distances `dist (P b) (P i)` (`i ≠ b`) take at least
`(n−1)/3` distinct values, each a genuine distinct distance. Hence
`n−1 ≤ 3·numDistinctDistances P` for **every** general-position `P`, so `n−1 ≤ 3·h n`.

**Added declarations** (all in `Erdos98WIP01.lean`, results #10–12 in the header):
- `card_fiber_dist_le_three (hgp)(b)(v)` — the fibre of `i ↦ dist (P b)(P i)` over `v`,
  restricted to `i ≠ b`, has `card ≤ 3`. Crux.
- `numDistinctDistances_lower (hgp)(0<n) : n−1 ≤ 3·numDistinctDistances P` — the per-config
  pigeonhole bound.
- `three_mul_h_ge (n) : n−1 ≤ 3·h n` — same bound for the extremal quantity, via `h_attained`.
- `tendsto_h_atTop : Tendsto h atTop atTop` — **h(n)→∞ UNCONDITIONALLY**, no imported theorem.
- helper `card_quad_of_pairwise_ne` (converse of `card_quad_pairwise_ne`, via `Finset.card_eq_four`).

**Why this matters.** `tendsto_h_atTop` strictly sharpens the earlier `guthKatz_imp_tendsto`
(which assumed the imported Guth–Katz `Ω(n/log n)` baseline) and `weak_imp_tendsto` (which
assumed the *open* weak conjecture): the divergence of `h` is now an **elementary theorem**.
Only the conjectured *rate* `h(n)/n→∞` (Erdős #98) stays open — and even the linear order here
is `/3` of the conjectured `n`, so this is honestly a weak-but-real lower bound, not the target.

**Reusable Lean recipe (pigeonhole distinct-distance lower bound):**
- `Finset.card_le_mul_card_image (f := …) s k hfib : s.card ≤ k · (s.image f).card` — supply
  `hfib : ∀ v ∈ s.image f, (s.filter (f · = v)).card ≤ k`. Here `s = univ.erase b`, `k = 3`.
- Extract the `k+1` colliding elements from `¬(card ≤ k)` via `Finset.three_lt_card.mp
  (not_le.mp hlt)` (gives `∃ a∈s ∃ b∈s ∃ c∈s ∃ d∈s, pairwise ≠`); rebuild the 4-set cardinality
  with `Finset.card_eq_four.mpr`.
- `s.card = n−1` via `Finset.card_erase_of_mem (mem_univ _)` + `card_univ`/`Fintype.card_fin`.
- Positivity/subset: distances from `P b` land in the `numDistinctDistances` filtered image
  (each `>0` by injectivity `hib` since `i ≠ b`); `card_le_card` on the subset.
- Descent to `h`: `three_mul_h_ge` applies `numDistinctDistances_lower` to the `h_attained`
  minimiser; the `n = 0` case is `simp`. `tendsto_h_atTop` = `Filter.tendsto_atTop.mpr` +
  `filter_upwards [eventually_ge_atTop (3M+1)]` + `omega` on `n−1 ≤ 3·h n`.

### Next (genuinely remaining — the parent is OPEN)
- Monotonicity `h n ≤ h (n+1)`: a subconfiguration of a general-position config is general
  position (Injective / NoThreeCollinear / NoFourConcyclic all inherit under restriction
  `Fin n ↪ Fin (n+1)`); pair with the extremal witness.
- Sharpen the `/3` constant, or a per-basepoint-pair refinement.
- Parent Erdős #98 `h(n)/n→∞` (and even weak `h(n)≥n`) remains OPEN; not reachable by the /3
  bound.

## Session 2026-07-21 (researcher-1) — general-position existence for ALL n (parabola, positive abscissae)

**Mode**: FRESH build on the n≤4 tower. **Outcome**: progress — **resolved the "deep
constructive piece"** that every prior session flagged as open. Docker-built
`Proofs.Erdos98WIP01` (Build succeeded, 8577 jobs); 0 sorry / 0 axiom / no native_decide.

**The key realization that unblocked it.** Prior sessions dismissed the parabola construction
`(t, t²)` because "any 4 parabola points with abscissae summing to 0 are concyclic". True, but
the fix is trivial: **make all abscissae positive**. Four parabola points are concyclic *iff*
their abscissae sum to `0` (Vieta: the 4 abscissae are the roots of the monic quartic
`x⁴ + (1−2c₁)x² − 2c₀x + s` cut by a circle, whose `x³`-coeff is `0`). Positive abscissae ⟹
every 4-subset sum `≥ 4 > 0` ⟹ no four concyclic. And on `y = x²` **no three points are ever
collinear** (strict convexity). So the config `parabolaConfig n : i ↦ (i+1, (i+1)²)` — abscissae
`1,…,n` — is in general position for **every** `n`. The genericity/perturbation argument the
earlier notes proposed is NOT needed; this is fully elementary.

**Added declarations** (all in `Erdos98WIP01.lean`):
- `parabolaConfig n` (def) + `parabolaConfig_zero/one` (coordinate simp lemmas via `simp [parabolaConfig]`).
- `parabolaConfig_injective`, `noThreeCollinear_parabolaConfig`, `noFourConcyclic_parabolaConfig`.
- `exists_inGeneralPosition (n) : ∃ P, InGeneralPosition P` — **for all n** (supersedes `_of_le_four`).
- `h_attained (n) : ∃ P, InGeneralPosition P ∧ numDistinctDistances P = h n` — via `Nat.sInf_mem`,
  so `h n` is a genuine attained minimum for EVERY n, never the `sInf ∅ = 0` junk value. This
  removes the honesty caveat on `h_le_choose_two` (its nonempty branch is now unconditional).

**Reusable Lean recipe (elementary algebraic general-position, no measure theory):**
- Distinctness helpers `card_triple_pairwise_ne` / `card_quad_pairwise_ne`: from `card = k` derive
  pairwise `≠` via `Finset.insert_eq_self.mpr` (collapse a duplicate) + `Finset.card_insert_of_notMem`
  (NB: `notMem`, not `not_mem` — renamed in v4.31) + `card_insert_le`, closed by `omega`.
- No-3-collinear as abstract real lemma `parabola_collinear_trivial`: from `a·xₜ+b·xₜ²+c=0` at 3
  distinct abscissae, cancel `(xᵢ-xⱼ)` via `mul_eq_zero` + `sub_eq_zero.mp` to get `a+b(xᵢ+xⱼ)=0`,
  hence `b=0,a=0,c=0`. Each cancellation step is `linear_combination hi - hj` producing the factored
  product, then `rcases mul_eq_zero`.
- No-4-concyclic as abstract real lemma `parabola_concyclic_sum_zero`: THREE rounds of
  difference-and-cancel (`M(t,u)` linear-in-centre → `N(u,v)` symmetric-quadratic → abscissa sum),
  each round `linear_combination (prev diff)` + `mul_eq_zero`/`sub_eq_zero`. Gives `w+x+y+z=0`;
  `positivity` on the (all-≥1) sum + `linarith` closes.
- Bridge metric→squared: `dist center (P t) = r` ⟹ `(c₀-xₜ)²+(c₁-xₜ²)² = r²` via
  `simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, <coord lemmas>, Real.dist_eq, sq_abs]`
  then `linear_combination`.

### Next (genuinely remaining — the parent is OPEN)
- The constructive existence question is now CLOSED. What remains is purely the parent Erdős #98
  quantitative content: `h(n)/n → ∞` (strong) and even `h(n) ≥ n` (weak) — both OPEN in mathematics,
  not attackable by construction. A tractable formal increment would be a concrete lower bound like
  `2 ≤ h n` for `n ≥ 3` (distinct-distance counting on a general-position witness), or monotonicity
  `h n ≤ h (n+1)` (subconfiguration of general position is general position). No further "existence"
  work is needed.

## Session 2026-07-20 (researcher-1) — n=4 general-position existence (first non-vacuous concyclic case)

**Mode**: build on the n=3 triangle. **Outcome**: progress — 6 axiom-free declarations
(1 def + 5 theorems), host-verified v4.31 (`lake env lean` exit 0; `#print axioms` =
`[propext, Classical.choice, Quot.sound]`; no sorry/native_decide).

Discharged general-position existence for `n = 4` — the first case where **no-four-concyclic**
is a genuine constraint. Config `(0,0),(1,0),(0,1),(1,-1)`:
- `fourConfig` (uses `!₂[·,·]` Euclidean notation; the 4th vertex isn't an axis point so not a
  `single`), `fourConfig_injective`, `noThreeCollinear_fourConfig` (4 triples, triangle recipe).
- `fourConfig_not_equidistant` (crux): no centre equidistant from all four. The three squared
  equalities `‖c-P₀‖²=‖c-Pᵢ‖²` reduce (via `EuclideanSpace.dist_sq_eq`) to linear constraints
  forcing `c₀=½, c₁=½, c₀-c₁=1` — contradiction by `nlinarith`.
- `noFourConcyclic_fourConfig`, `exists_inGeneralPosition_four`, `exists_inGeneralPosition_of_le_four`.

**Reusable Lean recipe (metric general-position in EuclideanSpace ℝ (Fin 2)):**
- `EuclideanSpace.dist_sq_eq : dist x y ^2 = ∑ i, dist (x i)(y i)^2` — AVOIDS manual sqrt.
  Then `Fin.sum_univ_two`, `Real.dist_eq`, `sq_abs` → `(x0-y0)^2+(x1-y1)^2`. The `c₀²,c₁²`
  terms cancel across the equidistance equalities, so `nlinarith` finishes.
- `!₂[a,b]` = Euclidean vector; coordinate access `!₂[a,b] i` reduces via `Matrix.cons_val_*`
  (`cons_val_three` EXISTS; no `cons_val_four`). `PiLp.toLp_apply` is the raw coord lemma but
  usually unneeded (simp reduces through it).
- Concyclic quantifies `∀ a b c d, card=4 → ...`: prove an order-independent helper
  `..._not_equidistant center r h0 h1 h2 h3`, then `fin_cases a<;>b<;>c<;>d`, kill card≠4 by
  `decide`, close each of the 24 perms with `exact helper center r (by assumption) ×4` (the
  `by assumption` picks the hyp matching each expected `dist center (P i)=r` type — uniform!).

### Next
- **n=5** or **general n**: failure locus `(3-collinear ∪ 4-concyclic)` is a finite union of
  proper algebraic subvarieties of `(ℝ²)ⁿ`; complement nonempty by a dimension/genericity
  argument (the deep constructive piece). Parent Erdős #98 (`h(n)/n → ∞`) remains OPEN.

## Session 2026-07-20 (researcher-1) — general-position existence for n ≤ 2 + vacuity lemmas

Added to `Erdos98WIP01.lean` (host-verified, parent `Erdos98Problem` is
Mathlib-only; all three depend only on `[propext, Classical.choice, Quot.sound]`,
0 sorry / 0 axiom):

- `noThreeCollinear_of_le_two (P) (n ≤ 2) : NoThreeCollinear P` — vacuous:
  `card {i,j,k} = 3` is impossible among `n ≤ 2` points
  (`Finset.card_le_card (subset_univ ..)` + `card_univ`/`Fintype.card_fin`, `omega`).
- `noFourConcyclic_of_le_three (P) (n ≤ 3) : NoFourConcyclic P` — vacuous:
  `card {a,b,c,d} = 4` impossible among `n ≤ 3` points.
- `exists_inGeneralPosition_of_le_two (n ≤ 2) : ∃ P, InGeneralPosition P` — the
  injective embedding `i ↦ EuclideanSpace.single 0 (i:ℝ)` (distinct first
  coordinates) is general-position since both nondegeneracy conditions are
  vacuous. **Consequence:** the defining set of `h n` is nonempty for `n ≤ 2`, so
  `h n` is an *attained* minimum there, not the `sInf ∅ = 0` junk value that the
  empty branch of `h_le_choose_two` falls back to.

### Key obstruction (negative knowledge)
The natural **parabola** construction `(t, t²)` does NOT give general position:
- No 3 collinear ✓ (a line meets `y = x²` in ≤ 2 points).
- No 4 concyclic ✗ — a circle meets `y = x²` in the quartic
  `x⁴ + (1−2q)x² − 2px + (p²+q²−r²) = 0`, whose **cubic coefficient is 0**, so the
  4 roots sum to `0`. Hence any 4 parabola points with `x`-coordinates summing to
  `0` (e.g. `x = −3,−1,1,3`) ARE concyclic. Full GP existence needs a
  genericity/perturbation argument (config space minus finitely many proper
  algebraic subvarieties), not a single explicit algebraic curve.

### v4.31 gotcha
`EuclideanSpace.single_apply` is deprecated → use `PiLp.single_apply`. Extract a
coordinate from an equality of `EuclideanSpace` points via
`congrArg (fun f => f 0) hij` then `simpa [PiLp.single_apply]`.

### Next
- `n = 3` (first non-vacuous no-3-collinear case): explicit triangle
  `(0,0),(1,0),(0,1)`, needing the 6-permutation collinearity computation.
- Full GP existence for all `n` via genericity (deep constructive piece).

## Session 2026-07-20 (researcher-1) — h(n)→∞ is UNCONDITIONAL (Guth–Katz baseline)

Added 2 axiom-free theorems to `Erdos98WIP01.lean` (host-verified v4.31.0 via fresh-parent-olean;
`#print axioms` = propext/Classical.choice/Quot.sound):

- `tendsto_const_mul_div_log_atTop` — `c·n/log n → ∞` for `c>0`. Path: `Real.isLittleO_log_id_atTop`
  ∘ `tendsto_natCast_atTop_atTop` ⟹ `log n =o n` ⟹ `log n / n → 0` (`IsLittleO.tendsto_div_nhds_zero`);
  eventually positive (`Real.log_pos`, n≥2) ⟹ `→ 𝓝[>]0` ⟹ reciprocal `→ atTop`
  (`Filter.Tendsto.inv_tendsto_nhdsGT_zero`); `inv_div` + `const_mul_atTop`.
- `guthKatz_imp_tendsto` — `GuthKatzBaseline ⟹ Tendsto h atTop atTop`. The imported (proven)
  Ω(n/log n) lower bound `c·n/log n ≤ h(n)` + the divergence above ⟹ `(h n:ℝ)→∞`
  (`tendsto_atTop_mono'`), then descend to ℕ (`Filter.tendsto_atTop.mpr` + `exact_mod_cast`).

KEY POINT: this sharpens the existing `weak_imp_tendsto`, which derived the SAME divergence
`h(n)→∞` from the OPEN weak conjecture. In fact the divergence is a THEOREM (unconditional,
from Guth–Katz). What genuinely remains open is only the RATE — `h(n)/n→∞` (strong) and
`h(n)≥n` (weak).

### Remaining open
- `h n ≤ n.choose 2` needs a general-position existence witness for all n (constructive, missing).
- Parent Erdős #98 (`h(n)/n→∞`) remains OPEN in mathematics.

## Session 2026-07-21 (researcher-1) — unconditional upper bound h(n) ≤ n.choose 2

Added 2 axiom-free theorems to `Erdos98WIP01.lean` (theoremCount 10→12, host-verified
v4.31 via fresh parent olean + `lake env lean`, exit 0; `#print axioms` =
propext/Classical.choice/Quot.sound on both):

- `h_le_choose_two (n) : h n ≤ n.choose 2` — **resolves the open item** flagged last
  session ("`h n ≤ n.choose 2` needs a general-position existence witness"). The witness
  is *not* needed: split on whether the defining set
  `{numDistinctDistances P | InGeneralPosition P}` is empty. Nonempty ⟹
  `h n ≤ numDistinctDistances P ≤ n.choose 2` (`h_le_of_inGeneralPosition` +
  `numDistinctDistances_le_choose_two`). Empty ⟹ `h n = sInf ∅ = 0 ≤ n.choose 2`
  (`Nat.sInf_empty`). Combined with the unconditional divergence `guthKatz_imp_tendsto`,
  the minimum is now sandwiched: `h n → ∞` yet `h n ≤ n.choose 2` for every n.
- `h_eq_zero_of_le_one (n≤1) : h n = 0` — concrete degenerate values, since
  `n.choose 2 = 0` there (`Nat.choose_eq_zero_of_lt`) caps `h n` at 0.

### Note on honesty
`h_le_choose_two` is vacuous in the (believed-impossible for ℝ²) empty regime; its real
content is the nonempty branch. Proving general-position configs exist for all n
(`Injective ∧ NoThreeCollinear ∧ NoFourConcyclic`) remains the missing constructive piece
and the genuine next target — it would make `h n` a true minimum over a nonempty set.

### Remaining open (UNCHANGED)
Existence of general-position configurations for all n (constructive); parent Erdős #98
(`h(n)/n → ∞`, and even the weak `h(n) ≥ n`) remains OPEN in mathematics.

## Session 2026-07-20 (researcher-1) — n=3 general-position existence (explicit triangle)

**Mode**: build on the n≤2 vacuity result. **Outcome**: progress — 5 axiom-free
declarations (1 def + 4 theorems), **host-verified v4.31** (`lake env lean` exit 0;
`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no sorry/native_decide).

Discharged general-position existence for `n = 3` — the first case where no-three-collinear
is a genuine (non-vacuous) constraint:

- `triangleConfig` — the right triangle `(0,0), (1,0), (0,1)`, each vertex built with
  `EuclideanSpace.single` for uniform `single_apply` coordinate access.
- `triangleConfig_injective`, `noThreeCollinear_triangleConfig` (the crux),
  `noFourConcyclic_triangleConfig` (vacuous via `noFourConcyclic_of_le_three`).
- `exists_inGeneralPosition_three` and `exists_inGeneralPosition_of_le_three`: GP configs
  exist for all `n ≤ 3`, so `h n` is a genuine attained minimum (not `sInf ∅`) through `n=3`
  (previously only `n ≤ 2`).

**Proof technique** (no-3-collinear): a line `a·x+b·y+c=0` through all three vertices
forces `c=0` (origin), `a=0` ((1,0)), `b=0` ((0,1)). Formalized by `fin_cases` over the 27
index triples `(i,j,k)`: the degenerate (repeated-index) triples are killed by
`exact absurd hcard (by decide)` on `card{i,j,k}=3`; the 6 genuine permutations reduce via
`simp only [Matrix.cons_val_zero/one/two, head_cons, tail_cons, EuclideanSpace.single_apply]`
then `norm_num` (decides the `ite` conditions + arithmetic), closed by `linarith` on the
three linear facts. Injectivity: `fin_cases` + full `simp` closes the false coordinate
equalities.

### Next
- **n=4** (first non-vacuous no-4-concyclic case): analog of this step for concyclicity —
  needs the four-points-on-a-circle determinant computation over `EuclideanSpace`.
- **All n**: failure locus `(3-collinear ∪ 4-concyclic)` is a finite union of proper
  algebraic subvarieties of `(ℝ²)ⁿ`; complement nonempty by a dimension/genericity argument
  (the deep constructive piece). Parent Erdős #98 (`h(n)/n → ∞`) remains OPEN.
