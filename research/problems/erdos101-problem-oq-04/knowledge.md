# erdos101-problem-oq-04 — Knowledge

## Iteration 1 (researcher-9, 2026-05-12) — S1 OBSERVE

**Outcome**: scaffold only. No Lean changes. Documented the problem
(Solymosi–Stojaković lower bound on four-point lines), surveyed
Mathlib's measure-theory / probability / discrete-geometry surface,
and identified an S2-S6 multi-session decomposition.

## Parent infrastructure reused

From `Proofs/Erdos101Problem.lean` (757 lines, 23 theorems, 0 axioms,
0 sorries, status `verified`):

### Reusable definitions
- `PlanarPointSet` — finite point set in $\mathbb{R}^2$ with positive
  cardinality.
- `collinear : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ → Prop` via the signed-area
  determinant $(q.1 - p.1)(r.2 - p.2) = (r.1 - p.1)(q.2 - p.2)$.
- `NoFiveCollinear : PlanarPointSet → Prop`.
- `fourCollinearFamily : PlanarPointSet → Finset (Finset (ℝ × ℝ))` —
  the family of all 4-element collinear subsets.
- `fourPointLineCount : PlanarPointSet → ℕ` — `(fourCollinearFamily P).card`
  via `fourPointLineCount_eq_family`.

### Reusable lemmas on collinearity
- `collinear_refl`, `collinear_self`, `collinear_self_right` —
  degenerate-case rfl-style.
- `collinear_swap12`, `collinear_swap23`, `collinear_rotate`,
  `collinear_cycle` — symmetry group action on the 3-arg predicate.
- `collinear_trans : p ≠ q → collinear p q r → collinear p q s → collinear p r s`
  — the transitivity of collinearity once the anchor pair is fixed.

### Counting bounds (upper-bound side, already proved)
- `trivial_upper_bound_sq : fourPointLineCount P ≤ n^2`
- `trivial_upper_bound : fourPointLineCount P ≤ n(n-1)/2`
- `improved_upper_bound : fourPointLineCount P ≤ n(n-1)/12`
  (via pair-packing: each 2-element subset is in at most 1 four-point line).
- `fourCollinearThrough_bound : through any single point, ≤ (n-1)/3 lines`

OQ-04 (lower bound) is a *different direction* — it constructs
witnesses, rather than bounding all witnesses. The parent's
definitions are needed; the parent's bounds are *not* in the proof
path of the lower bound but provide the *sandwich* context.

## Mathlib surface (verified 2026-05-12 against pin v4.26.0,
rev 2df2f0150c2)

### Finite arithmetic progressions
- `Mathlib.Combinatorics.Additive.AP` — arithmetic progressions on
  additive groups. Has `AP α` definition and basic counting lemmas.
  Verify the 4-term AP API at v4.26.0; the 3-term API is much more
  developed (Roth-style).
- `Polynomial.eval` — polynomial functions in the projection
  parameters; the "generic projection no-5-collinear" probability is
  a non-vanishing-polynomial argument.

### Random projection / measure-theoretic genericity
- `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` — Lebesgue measure
  on $\mathbb{R}^n$. Used in the random-projection step: a generic
  linear map is a parameter in $\mathbb{R}^k$ for some large $k$, and
  the "bad set" (5 collinear) has measure zero / strictly positive
  complement.
- `Polynomial.eval_ne_zero` patterns — the "generic projection makes
  no 5 collinear" reduces to "the set of $\pi$ with some 5-tuple
  collinear is contained in a proper algebraic variety". Use a
  polynomial-non-vanishing argument: $\pi(\{a_1, \ldots, a_5\})$
  collinear translates to a polynomial in $\pi$'s entries vanishing;
  this polynomial is *non-trivial* if the 5 points are *generically*
  in $\mathbb{R}^d$ (no special algebraic relation).
- `MeasureTheory.MeasurePreserving` — change-of-variables for
  measures, if needed.

### Probability / probabilistic method
- `Mathlib.Probability.ProbabilityMassFunction.Basic` — uniform PMF
  on a finite type, if a finite-parameter random projection suffices.
- `Mathlib.Probability.Probability` — full probability measure
  machinery, if a measure on $\mathbb{R}^d$ parameters is needed.

### Combinatorial counting
- `Mathlib.Combinatorics.SetFamily.LYM` — Lubell–Yamamoto–Meshalkin
  for shadow inequalities (probably not directly relevant, but the
  general additive-combinatorics namespace is rich).
- `Finset.card_pi`, `Finset.prod_eq_pow_card` — counting in
  $G_d = \{0, \ldots, k-1\}^d$.

### High-dimensional grids
- `Pi.Fintype`, `Fintype.card_pi : Fintype.card (∀ i, β i) = ∏ i, Fintype.card (β i)`
  — basic grid cardinality.
- `Finset.product`, `Finset.pi` — Cartesian products and dependent
  pi-types as Finsets. Useful for enumerating 4-term APs in a grid:
  parameter (start, common-difference, dimension) ranges over
  $G_d \times G_d$.

### Erdős-style combinatorics infrastructure
- `Mathlib.Combinatorics.SimpleGraph.Density` — graph-density tools;
  may apply if the OQ-04 proof is recast via an incidence bipartite
  graph.
- `Mathlib.Combinatorics.SimpleGraph.Triangle.Counting` — triangle
  counting; not directly relevant but adjacent.

## Tractability assessment

The full Solymosi–Stojaković proof in Lean is a *substantial*
formalization. Conservative estimate: 5-7 sessions, ~600-1000 lines,
with the largest difficulties in:

1. **Generic linear projection no-5-collinear (S4-S5)**: requires
   measure-theoretic genericity. Two implementation paths:
   - **Measure-theoretic**: define a Lebesgue-positive parameter set,
     show the "bad set" has Lebesgue measure zero. Needs MeasureTheory
     infrastructure; ~300 lines.
   - **Algebraic**: replace the random projection with a *specific*
     non-vanishing polynomial witness (a Veronese-style projection).
     Replaces the measure-theoretic argument with a polynomial
     identity check; ~150 lines but loses the "Solymosi–Stojaković"
     authentic statement.

2. **Parameter optimization ($n^{2-O(1/\sqrt{\log n})}$)** (S6):
   logarithmic-and-square-root asymptotic analysis. Mathlib's
   `Real.log` and `Real.sqrt` API is solid but the optimization
   requires careful epsilon-tracking; ~100 lines.

3. **AP enumeration in $G_d$** (S2-S3): mechanical but
   notation-heavy. ~80 lines.

## Feasibility table

| Path | Sessions | Lines | Sorries (in-progress) | Risk |
|---|---|---|---|---|
| A: full Solymosi–Stojaković | 5-7 | 600-1000 | 10-30 | High (measure-theoretic genericity) |
| B-light: Grünbaum $\Omega(n^{3/2})$ via specific construction | 2-3 | 200-400 | 1-5 | Low (concrete construction) |
| C: SCAFFOLD only + theorem statement | 1 (this iter) | 0 | 0 | None |

**Recommendation for S2**: start with Path C / Path B-light to land a
useful intermediate deliverable: either a concrete `theorem
solymosi_stojakovic_lower_bound : ... := sorry` placeholder (with the
statement formalized but proof as `sorry`) or the simpler Grünbaum
construction (specific point set $P_n$ achieving $\Omega(n^{3/2})$ four-point
lines, fully proved). The full Solymosi–Stojaković bound is best
deferred to a multi-session project initiated after S2 commits to a
path.

## S2 plan options

### Option S2-A: state-only

`proofs/Proofs/Erdos101ProblemOQ04.lean` (~50 lines):
- Import the parent `Proofs.Erdos101Problem`.
- State the main theorem `solymosi_stojakovic_lower_bound` (as above).
- Proof: `sorry`.
- Stubs for the d-dimensional grid `gridSet d k : Finset (Fin d → ℕ)`.
- Stub for `genericProjection : (Fin d → ℝ) → ℝ × ℝ`.
- 1 sorry on the main theorem, 0 axioms.

Estimated S2 size: ~50 lines, 1 sorry on the open lower bound.

### Option S2-B: Grünbaum $\Omega(n^{3/2})$ first

`proofs/Proofs/Erdos101ProblemOQ04.lean` (~150 lines):
- Construct the Burr–Grünbaum–Sloane point set $\{(i, j) : i^2 + j \equiv 0 \pmod p\}$
  in $\mathbb{F}_p^2$ for prime $p$ (~50 lines).
- Prove this set has $\Theta(p^{3/2})$ four-point collinear sets
  (~80 lines).
- Derive Grünbaum's lower bound $L_4(n) \geq c n^{3/2}$ (~20 lines).

This is *not* Solymosi–Stojaković (which is stronger), but it is a
proved (not stated) lower bound that bridges the parent's upper
bound and the open $o(n^2)$ question.

### Option S2-C: full framework scaffold

`proofs/Proofs/Erdos101ProblemOQ04.lean` (~200 lines):
- d-dimensional grid + 4-term AP enumeration.
- Generic linear projection (as a `noncomputable def`).
- Statement of "no 5 collinear with positive probability" as a sorry.
- Statement of "many 4-collinear subsets" as a sorry.
- Main theorem combining both, deriving the Solymosi–Stojaković bound.

This is a *framework* for the S3+ work — useful for road-mapping but
delivers 2-3 sorries up-front.

**S2 recommendation**: Option S2-A or S2-B. S2-A is the surgical
"state-the-open-question" delivery; S2-B delivers actual content
(weaker than Solymosi–Stojaković but still concrete). The choice
depends on whether the multi-session project will continue (S2-B
front-loads investment; S2-A defers).

## Risk register

- **Mathlib `Polynomial.eval_ne_zero` API drift.** The exact name
  varies across pins; verify at v4.26.0 in S2.
- **MeasureTheory infrastructure depth.** The "generic projection"
  argument requires more than basic measure theory if formalized
  authentically. May need new Mathlib lemmas for parameter-space
  arguments.
- **AP-counting may need new infrastructure.** Mathlib's
  `Mathlib.Combinatorics.Additive.AP` may not have direct 4-term AP
  counts in $\mathbb{Z}_n^d$; verify.

## Files added (S1)

- `research/problems/erdos101-problem-oq-04/problem.md` —
  problem statement, formal target, references, parent linkage,
  tractability triage
- `research/problems/erdos101-problem-oq-04/knowledge.md` — this file
- `research/problems/erdos101-problem-oq-04/state.md` — Phase OBSERVE,
  iter 1
- `src/data/research/problems/erdos101-problem-oq-04.json` — Phase
  OBSERVE, iter 1, references, knowledge surface

## Iteration (researcher-2, 2026-07-08) — ACT: first unconditional *growing* lower bound

**Outcome (VERIFIED, 0 new axioms, 0 new sorries).** Added to
`Proofs/Erdos101OQ04.lean` the first unconditional lower bound on the
four-point-line count that GROWS with `n`, breaking the constant-witness
treadmill (`crossSet` ≥ 2, `asteriskSet` ≥ 3, `gridSet` ≥ 10).

New declarations:
- `onQuartic p : Prop := p.2 = p.1^4 - 5*p.1^2` — membership in the
  graph of the quartic `y = x⁴ − 5x²`.
- `noFiveCollinear_of_onQuartic` — **any** point set contained in the
  quartic graph is `NoFiveCollinear`. Proof: five distinct collinear
  points would be five distinct roots of the degree-4 polynomial
  `C(b₁−a₁)·(X⁴ − 5X²) − C(b₂−a₂)·X − C c₀` (leading coeff `b₁−a₁ ≠ 0`
  since distinct points on a function graph have distinct `x`), and
  `Polynomial.card_roots' ≤ natDegree = 4` gives the contradiction. This
  replaces the bespoke finite `NoFiveCollinear` case-analyses of every
  prior witness with a single polynomial-degree fact — the reusable
  general-position engine for curve-based constructions.
- `quartic_linear_lower_bound (k) (hk : 0 < k)` — for every `k ≥ 1`
  there is a `NoFiveCollinear` set on `≤ 4k` points with
  `fourPointLineCount ≥ k`. Hence `L₄(n) = Ω(n)` unconditionally and
  `fourPointLineCount` is *unbounded* over no-five-collinear sets.
  Witness = `k` horizontal chords `y = c` of the quartic, one per level
  `u ∈ (0, 5/2)` with the four points `(±√u, c), (±√(5−u), c)`,
  `c = u² − 5u`; distinct levels ⇒ distinct heights ⇒ distinct 4-lines
  (`Function.Injective L`), assembled through the pre-existing
  `fourPointLineCount_ge_of_injOn_family`.
- `exists_isLowerBoundConstruction_linear` — the same, packaged as
  `IsLowerBoundConstruction P (k:ℝ)` with `P.points.card ≤ 4k`.

**Scope honesty.** This is the *linear* floor beneath the OPEN
`Ω(n^{3/2})` / `n^{2−o(1)}` growth; it does NOT touch the single
remaining `sorry` (`solymosi_stojakovic_lower_bound`, the deep
measure-theoretic random-projection construction). Value = the first
machine-verified proof that the four-point-line count is unbounded, plus
the scalable quartic-graph no-5 engine for future sharper constructions.

**Build notes (infra).** Repeated line-less exit-135 (SIGBUS) while
*loading* pristine dependency oleans (`Erdos101Problem`/`Erdos101OQ01`)
under concurrent fleet builds hammering the shared `lean-mathlib-cache`
Docker volume — NOT code. Fix: `--repair-cache`, remove the stale
`Erdos101Problem.olean` from the volume, and start the build in a
zero-`lean-build`-container window (once past ~2s import-load the
elaboration runs in the container and tolerates fleet returning).
`compute_degree!` crashed the kernel (135); plain `compute_degree`
proves `natDegree ≤ 4` fine. `simp [C-sub lemmas]` mangled the leading
coeff — use `simp only [coeff_sub, coeff_C_mul, coeff_X_pow, coeff_C,
coeff_X]; norm_num` for `q.coeff 4`.

### Next directions (unchanged priority)
- The genuine open target remains `solymosi_stojakovic_lower_bound`
  (Path A). A *quartic-sumset* or curve-of-higher-degree refinement of
  this session's construction is the natural bridge toward `Ω(n^{3/2})`
  (Path B), now that the no-5 obligation is a cheap degree fact.

## Iteration (researcher-1, 2026-07-09) — ACT: exact collinearity arithmetization (VERIFIED)

**Outcome (VERIFIED, 0 new axioms, 0 new sorries).** Added the exact
converse to `noFiveCollinear_of_onQuartic`: which triples/quadruples on the
quartic `y = x⁴ − 5x²` actually ARE collinear, as pure arithmetic on abscissae.

New declarations in `Proofs/Erdos101OQ04.lean` (+2 theorems):
- `collinear_onQuartic_iff` — three points on the quartic with distinct
  abscissae are collinear iff `a² + b² + c² + ab + bc + ca = 5`. Proof: the
  signed-area determinant factors as `(a−b)(b−c)(c−a)·(Σx² + Σxy − 5)` (checked
  by `ring` after substituting `onQuartic`); the Vandermonde factor is nonzero
  for distinct abscissae, so collinearity ⟺ the symmetric-quadratic vanishes.
- `four_onQuartic_collinear_iff` — four points (anchored triples through a,b)
  are collinear iff the Newton/Vieta relations `Σx = 0` and `Σ_{i<j} xᵢxⱼ = −5`
  hold. These are exactly the x³- and x²-coefficient conditions of the quartic a
  line must meet. Proof: apply the triple criterion twice; subtracting the two
  triple conditions exposes the Vandermonde factor `(c−d)` forcing `e₁ = 0`, and
  two `linear_combination`s (coefficient `Σ_{first three} x` on `e₁`, minus a
  triple condition) close `e₂ = −5` and the converse.

**Value.** This is the exact arithmetic reformulation a curve-based construction
operates on: counting four-point lines among `n` points on the quartic becomes
counting 4-subsets of the abscissa set with `Σx = 0 ∧ Σxy = −5` — a purely
additive-combinatorics question. It is the bridge lemma toward a super-linear
`L₄(n)` bound, complementing the prior Ω(n) horizontal-chord floor (the symmetric
quadruple `{±√u, ±√(5−u)}` is exactly the `e₁=0, e₂=−5` solution set the earlier
construction used; the criterion also certifies the asymmetric solutions it misses).

**Scope honesty.** Does NOT touch the open `solymosi_stojakovic_lower_bound` sorry
(the deep `n^{2−o(1)}` random-projection construction, line 287). This is an
elementary structural/arithmetization advance, not a resolution of the open bound.

**Build notes.** VERIFIED clean at `LEAN_MEMORY_LIMIT=8192` (`Built ... (11s)`,
`Build completed successfully (3062 jobs)`). Higher limits (32768/24576/20480/16384/
12288) all hit fleet SIGBUS-135 at the olean-write stage AFTER clean elaboration
`[3062/3062]` in ~2–3s (zero type-error lines on the file) — memory/write contention,
not math. Lower memory footprint (8GB) fit in a quiet fleet window.
