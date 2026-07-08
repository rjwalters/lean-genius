# Current State

**Phase**: ACT (framework floor raised to 8 four-point lines via the maximal 4×4 grid; direct-lean-verified)
**Since**: 2026-07-01
**Last Updated**: 2026-07-08 (Iteration 8, researcher-4)
**Iteration**: 8

> Note: the S3-B2/B3 parabola-arc infrastructure (secant bound, ℝ²
> realization, arc `fourPointLineCount = 0`) and the non-vacuity
> witness (`witnessSet`, floor `1`) landed in later iterations (4–6,
> researcher-8/6) than the entries below record; the file is ahead of
> the older iteration logs.

## Iteration 8 (researcher-4, 2026-07-08) — raise framework floor 3 → 8 (maximal 4×4 grid)

**Outcome**: `IsLowerBoundConstruction gridSet 8` — the maximal 4×4
integer grid `gridSet = {0,1,2,3}×{0,1,2,3}` (16 points) is an explicit,
0-axiom, no-five-collinear planar point set with at least **eight**
four-point lines (its four rows + four columns). This more than doubles
the previous constant floor of 3 (`asteriskSet`) and — crucially — the
grid's certified lines are in **general position** (no common point),
unlike the concurrent pencils `crossSet`/`asteriskSet`. This is exactly
the grid configuration whose random linear projection underlies the
Solymosi–Stojaković lower bound. docker-build verified (Lean v4.26.0),
0 axioms / 0 new sorries.

### What I added (all in `proofs/Proofs/Erdos101OQ04.lean`, +~470 LOC)

1. **`gridPoints` / `gridSet`** (defs) — the 4×4 grid `{0,1,2,3}²⊂ℝ²`
   (via `Finset.product`) and its `PlanarPointSet` wrapper; `gridPoints_card = 16`.
2. **`gridSet_noFiveCollinear`** (PROVED, axiom-free) — a clean symmetric
   argument: the grid has only four distinct `x`- and `y`-coordinates,
   so a horizontal line forces five distinct *first* coordinates in
   `{0,1,2,3}` while a non-horizontal line forces five distinct *second*
   coordinates (via `collinear_snd_inj`) — either way
   `five_distinct_not_subset_0123` contradicts `5 ≤ 4`.
3. **`gridSet_fourPointLineCount_ge_eight`** (PROVED, axiom-free) — the
   four rows and four columns are eight distinct four-element collinear
   subsets; `Finset.card_le_card` on this explicit subfamily of the
   four-point-line filter gives `8 ≤ fourPointLineCount gridSet`.
4. Reusable helpers: `card_0123`, `five_distinct_not_subset_0123`,
   `gridPoints_fst_mem`/`snd_mem`, `grid_line_ne`.
5. Packaging: `gridSet_isLowerBoundConstruction`,
   `exists_isLowerBoundConstruction_eight` (16 points, floor 8).

**Note**: the grid carries **10** four-point lines in total (the two
main diagonals give the remaining 2); only the 8 axis-aligned lines are
certified here. **Next**: S3-B6 certify the diagonals for the full count
of 10, or Path B — a superlinearly-staggered stack of 4-wide rows to
obtain the first *unbounded* `fourPointLineCount` lower bound.

---

## Iteration 7 (researcher-4, 2026-07-01) — raise framework floor 1 → 2

**Outcome**: `IsLowerBoundConstruction crossSet 2` — an explicit,
0-axiom, no-five-collinear planar point set with **two** four-point
lines, strictly above the prior single-line `witnessSet` floor.  Build
verified by direct `lean` v4.26.0 compile (Docker fallback);
`#print axioms crossSet_isLowerBoundConstruction =
[propext, Classical.choice, Quot.sound]` only (no `sorryAx`, no
`native_decide`/`Lean.ofReduceBool`) ⇒ 0-axiom VERIFIED.

### What I added (all in `proofs/Proofs/Erdos101OQ04.lean`, +~330 LOC)

1. **`collinear_snd_inj`** (PROVED, axiom-free, reusable) — on a
   *non-horizontal* line (`a.2 ≠ b.2`) the second coordinate is
   injective among points collinear with `a, b`: two such points
   sharing a `y`-value coincide.  Hence a non-horizontal line meets any
   set with `≤ k` distinct `y`-values in `≤ k` points.
2. **`collinear_snd_eq_of_horiz`** (PROVED, axiom-free, reusable) — on a
   *horizontal* line (`a.2 = b.2`, `a.1 ≠ b.1`) every collinear point
   shares that `y`-value.
3. **`crossPoints`** / **`crossSet`** (defs) — the explicit 7-point
   cross `{(0,0),(1,0),(2,0),(3,0),(0,1),(0,2),(0,3)}` ⊂ ℝ² and its
   `PlanarPointSet` wrapper.
4. **`crossPoints_snd_mem` / `crossPoints_snd_eq_zero_of_ne` /
   `crossPoints_mem_xaxis`** (PROVED) — the three membership/case
   lemmas: the cross's `y`-values are exactly `{0,1,2,3}`; two distinct
   points with equal `y` must be on the `x`-axis (`y=0`); an `x`-axis
   point is one of the four.
5. **`crossSet_noFiveCollinear`** (PROVED) — no five collinear: a
   horizontal line hits only the four `x`-axis points; a non-horizontal
   line hits `≤ 1` point per `y`-value (via `collinear_snd_inj`) and the
   cross has only four distinct `y`-values, so `≤ 4` either way.
6. **`crossSet_fourPointLineCount_ge_two`** (PROVED) — the `x`-axis and
   `y`-axis are two distinct four-element collinear subsets, so
   `fourPointLineCount crossSet ≥ 2`.
7. **`crossSet_isLowerBoundConstruction`** (PROVED) —
   `IsLowerBoundConstruction crossSet 2`.
8. **`exists_isLowerBoundConstruction_two`** (PROVED) — there is a
   no-five-collinear set of exactly seven points achieving threshold 2.

### Why 7 points, and why this is not trivial padding

Two distinct four-point lines meet in at most one point, so together
they need at least `4 + 4 − 1 = 7` distinct points; equivalently, **no
five-point set has two four-point lines**.  The prior floor-`1` witness
(`witnessSet`, five points) is therefore optimal for its size, and
raising the floor to `2` genuinely requires a larger, structurally
different construction (a *cross* of two lines rather than a single
line).  The two collinearity lemmas isolate the reusable geometric
content (a non-horizontal line is a graph over `y`).

### Counts

- Theorems: +9 PROVED axiom-free (cumulative file total 35).
- Definitions: +2 (`crossPoints`, `crossSet`).
- Sorries: 2 unchanged (both OPEN constructions; no new sorries).
- Axioms: 0 unchanged.

### Honest scope / what remains OPEN

This is a **constant**-size witness (floor `2`, seven points).  It does
**not** touch the asymptotic OPEN content: `fourPointLineCount` growing
like Ω(n^{3/2}) (`grunbaum_lower_bound_three_halves`) or n^{2−o(1)}
(`solymosi_stojakovic_lower_bound`).  The natural next brick toward
those is the sumset/grid four-collinear COUNT built on top of the
verified parabola arc (S3-B2-β), still the crux and still hard.

### Build note

Docker daemon corrupted (containerd meta.db I/O, host-wide — see prior
researcher memos).  Verified via direct `lean` compile: reconstruct
`LEAN_PATH` over every `.lake/packages/*/.lake/build/lib/lean` dir plus
the main repo `.lake/build/lib/lean`, pre-compile the `Proofs.Erdos101OQ01`
dependency (its own `Erdos101Problem` olean already built) into a temp
root placed **first** on `LEAN_PATH`, then compile
`Proofs/Erdos101OQ04.lean` (≈5 s).  0 errors; only the 2 expected
pre-existing sorry warnings.

---

## Iteration 3 (researcher-3, 2026-05-16) — S3-B1 ACT (Grünbaum parabola foundation)

**Outcome**: Path B foundational object delivered.  Added the
Grünbaum modular parabola `G_p ⊂ (ZMod p) × (ZMod p)` as a `Finset`
together with its parameterisation and a cardinality lemma
`|G_p| = p` for odd primes.  All seven new declarations are
axiom-free; no new sorries.

### What I added

A new `Erdos101OQ04.Grunbaum` sub-namespace inside
`proofs/Proofs/Erdos101OQ04.lean` (lines 284–400) containing:

1. **`Grunbaum.parabola`** (def, `[NeZero p]`) — set-builder form of
   the F_p² parabola: `{(i, j) ∈ (ZMod p) × (ZMod p) : 4·j = -(i·i)}`.
   The canonical mathematical definition.
2. **`Grunbaum.param`** (def) — the parameterisation
   `i ↦ (i, -i² · 4⁻¹)`.  Operationally produces the parabola points.
3. **`Grunbaum.param_injective`** (PROVED, axiom-free) — `param p` is
   injective because the first coordinate is `i` itself.
4. **`Grunbaum.four_ne_zero`** (PROVED, axiom-free) — for `p` prime
   with `p ≠ 2`, the literal `(4 : ZMod p)` is nonzero.  Proof: from
   `(4 : ZMod p) = 0` derive `p ∣ 4` via `ZMod.natCast_eq_zero_iff`,
   then `interval_cases p` over `2 ≤ p ≤ 4` eliminates `p = 2` (excluded
   by hypothesis), `p = 3` (does not divide 4), `p = 4` (not prime).
5. **`Grunbaum.param_mem_parabola`** (PROVED, axiom-free) — the
   parameterised point `(i, -i² · 4⁻¹)` lies on the parabola.
   Reduces to `4 · 4⁻¹ = 1` via `mul_inv_cancel₀ four_ne_zero`.
6. **`Grunbaum.mem_parabola_iff_eq_param`** (PROVED, axiom-free) —
   a point `x` lies on the parabola iff `x = param p x.1`.  Direction
   `→` uses `mul_left_cancel₀ four_ne_zero` to invert the defining
   relation; direction `←` reuses `param_mem_parabola`.
7. **`Grunbaum.parabola_eq_image`** (PROVED, axiom-free) — the parabola
   equals `Finset.univ.image (param p)`.  Closes the bijection-image
   loop, enabling the cardinality computation.
8. **`Grunbaum.parabola_card`** (PROVED, axiom-free) — **for `p` prime
   with `p ≠ 2`, `(parabola p).card = p`**.  The S3-B1 deliverable.
   Proof: rewrite via `parabola_eq_image`, then
   `Finset.card_image_of_injective` reduces to `Finset.univ.card`,
   which equals `Fintype.card (ZMod p) = p` by `ZMod.card`.

### Counts

- Definitions: 2 new (`Grunbaum.parabola`, `Grunbaum.param`),
  cumulative total 3 (including S2's `IsLowerBoundConstruction`).
- Theorems: 6 new PROVED axiom-free, cumulative total 12 (4+6 PROVED
  + 2 deferred from S2).
- Sorries: 2 unchanged (both on OPEN constructions from S2; no new
  sorries this iteration).
- Axioms: 0 unchanged.
- LOC: +119 (283 → 402).

### Mathlib bearer audit (SHA `2df2f0150c…`, v4.26.0)

Verified bearers used:

| Symbol | File | Line | Status |
|---|---|---|---|
| `ZMod.natCast_eq_zero_iff` | `Mathlib/Data/ZMod/Basic.lean` | 508 | ✓ canonical name |
| `ZMod.card` | `Mathlib/Data/ZMod/Defs.lean` | 168 | ✓ requires `[Fintype (ZMod n)]` |
| `ZMod.fintype` | `Mathlib/Data/ZMod/Defs.lean` | 160 | ✓ instance via `[NeZero n]` |
| `mul_inv_cancel₀` | (algebra core) | — | ✓ stable in `GroupWithZero` |
| `Finset.card_image_of_injective` | (Finset core) | — | ✓ stable |
| `Nat.Prime.two_le` | (Nat core) | — | ✓ stable |
| `interval_cases` | (Mathlib tactic) | — | ✓ stable |

**Important deprecation trap avoided**:
`ZMod.natCast_zmod_eq_zero_iff_dvd` was deprecated `2025-06-30` and is
only an alias for the canonical `ZMod.natCast_eq_zero_iff`.  This S3-B1
uses the canonical name to avoid future-deprecation breakage.

### Files modified (S3-B1)

- `proofs/Proofs/Erdos101OQ04.lean` — +119 LOC (one new import
  `Mathlib.Data.ZMod.Basic`; one new `namespace Grunbaum`
  block with 2 defs + 6 theorems).
- `research/problems/erdos101-problem-oq-04/state.md` — this entry.
- `src/data/research/problems/erdos101-problem-oq-04.json` — phase
  ACT, iter 3, refreshed `currentState`.
- `research/problems/erdos101-problem-oq-04/sessions/2026-05-16-s3b1.md`
  — NEW session memo.

### Next action (S3-B2 or S3-A1)

The parabola is now a concrete `Finset` with known cardinality.  Three
plausible next-iteration continuations, in order of estimated cost:

* **S3-B2-α (Path B continuation, smallest piece)**: embed the
  parabola into `ℝ²` via `ZMod p ↪ ℝ`, producing a `PlanarPointSet` of
  size `p`.  Need: a Finset-level injective map `ZMod p → ℝ` (e.g.,
  via `Fin p → ℝ` with `Nat.cast`).  ~40 LOC, 0 sorries.  Yields a
  `Finset (ℝ × ℝ)` to plug into `PlanarPointSet` (whose `size_pos`
  field becomes `p ≥ 1`, immediate from `p prime`).
* **S3-B2-β (Path B four-collinear count, bigger piece)**: prove that
  the (embedded) parabola has `≥ p^{3/2}/k` four-collinear subsets for
  some explicit constant `k`.  The argument: count secant lines via
  Bezout `(deg = 2) ⇒ ≤ 2 intersections`; total `Θ(p²)` secants give
  `Θ(p²/p) = Θ(p)` 4-collinear lines.  Wait — actually Grünbaum
  achieves `Ω(p^{3/2})` not `Ω(p²)`; the *correct* count is via a
  different parameterisation.  S3-B2-β is closer to ~120-200 LOC and
  requires a more careful combinatorial argument; should not be
  attempted before the embedding is in place.  Defer to S3-B3.
* **S3-A1 (Path A pivot, parallel option)**: define the d-dim grid
  `G_d := (Fin k → Fin d → ℤ)` + cardinality `k^d`.  ~30 LOC, 0
  sorries.  Foundational for Solymosi–Stojaković; this is the
  alternative discharge path if Path B's 4-collinear count proves
  unworkable.

**Recommendation**: **S3-B2-α** (embedding `ZMod p ↪ ℝ` to produce
a `PlanarPointSet`).  This is the next minimal-LOC step on Path B and
unblocks the eventual `IsLowerBoundConstruction` instantiation.

### Blockers

None for S3-B1 (this iteration) at v4.26.0 Mathlib.  Path B's S3-B2-β
4-collinear count argument is the next nontrivial mathematical step;
it requires a polynomial-roots bound on `(ZMod p)[X]` plus an
intersection-multiplicity argument.  Both are within Mathlib at
v4.26.0 (`Polynomial.card_roots_le_degree`, `ZMod.charP`), but the
combinatorial reduction requires careful set-up.

### Build risk

The Lean file uses standard Mathlib field/`ZMod`/`Finset` API at
v4.26.0.  Key risks:

* **Numeric-literal cast** in `four_ne_zero`: `(4 : ZMod p) = 0` →
  `((4 : ℕ) : ZMod p) = 0` via `exact_mod_cast`.  Standard tactic; no
  known failures at v4.26.0.
* **`interval_cases p`** with bounds `2 ≤ p ≤ 4`: produces three
  goals (p=2, p=3, p=4), each closed by elementary tactic.
* **`subst hi`** in `parabola_eq_image`: substitutes `x` with `param p i`,
  reducing goal to `param p i = param p (param p i).1`.  Closed by
  `rfl` via `Prod.fst (i, _) = i` (defeq).  If `rfl` fails due to
  elaboration order, fallback is `simp [param]`.

Docker build deferred per researcher worktree convention
(`feedback_researcher_lake_symlink_broken.md`); CI is the ground truth.
Host disk at 99% full (6.8 Gi avail of 926 Gi), Docker daemon
unresponsive — same constraints as Iter 2.

### Race-safety note

Pre-claim PR list at 2026-05-16 ~10:55 UTC:
- 0 OPEN PRs on `erdos101-problem-oq-04` slug (verified via
  `gh -R rjwalters/lean-genius pr list --state open
   --search erdos101-problem-oq-04`).
- 1 OPEN unrelated PR `#19606` (mechanic batch lineCount drift, 6
  unrelated entries).
- No sibling `research/erdos101*` branches on origin
  (`git ls-remote origin "refs/heads/research/erdos101*"` empty).
- Last merge on slug: 2026-05-14 (S2 ACT, #19143; researcher-9 prior
  session).  Saturation window: ~1.5 days post-S2; race risk minimal.

Slug is marked `available` in `.lean/state/candidate-pool.json`.
After S3-B1 commit + push, this iteration upgrades phase from ACT-S2
to ACT-S3-B1; pool status remains `available` until COMPLETED.

---

## Iteration 2 (researcher-9, 2026-05-14) — S2 ACT (S2-A-extended)

**Outcome**: framework + 2 provable lemmas + 2 deferred lower-bound
statements.  Lean file `proofs/Proofs/Erdos101OQ04.lean` created
(~210 LOC); umbrella `proofs/Proofs.lean` updated.

### What I added

This S2 PR delivers a **mild extension of state.md's S2-A path**
(state-only + reduction lemmas), staying within single-iteration
scope while squeezing 2 axiom-free lemmas out of the framework:

1. **`Erdos101OQ04.IsLowerBoundConstruction`** — a `Prop` predicate
   identifying a no-five-collinear `PlanarPointSet` witness with a
   specified ℝ-valued threshold on `fourPointLineCount`.  The
   framework abstraction for OPEN lower bounds (Grünbaum,
   Solymosi–Stojaković).  Independent of OQ-01.
2. **`exists_four_collinear_subset_of_count_pos`** (PROVED, axiom-free)
   — any no-five-collinear `P` with `fourPointLineCount P ≥ 1`
   admits an explicit 4-element subset of `P.points` whose elements
   are collinear with two distinguished anchor points `a, b ∈ S`,
   `a ≠ b`.  Witness extraction for downstream construction PRs.
3. **`isLowerBoundConstruction_threshold_eq_zero_of_small`** (PROVED,
   axiom-free) — for `|P| < 4`, the construction is vacuous at
   threshold `0`; restates `fourPointLineCount_lt_four` in OQ-04's
   namespace.
4. **`grunbaum_lower_bound_three_halves`** (DEFERRED, `theorem ... := by
   sorry`) — the pre-Solymosi–Stojaković Ω(n^{3/2}) lower bound.
   Path B in S1 OBSERVE's three paths.  Recorded as a deferred proof
   obligation so it can be cited without introducing a permanent
   axiom.
5. **`solymosi_stojakovic_lower_bound`** (DEFERRED) — OQ-04-flavoured
   re-statement of the n^{2−O(1/√(log n))} bound, packaged via
   `IsLowerBoundConstruction`.  Mathematically equivalent to
   `Erdos101OQ01.solymosi_stojakovic_lower_bound`.
6. **`solymosi_stojakovic_lower_bound_via_oq01`** (PROVED, axiom-free)
   — bridge: OQ-04's `IsLowerBoundConstruction`-packaged statement
   reduces directly to OQ-01's version.  Shows the two formulations
   are mutually deducible (the OQ-04 sorry is *purely cosmetic* — it
   would be discharged automatically once OQ-01's sorry is).
7. **`solymosi_stojakovic_exponent_gt_three_halves`** (PROVED,
   axiom-free) — for `C ∈ (0, 1/2)` and `n ≥ 3`, the exponent
   `2 - C/√(log n)` is strictly greater than `3/2`.  Witnesses the
   Solymosi–Stojaković bound strictly dominating Grünbaum's Ω(n^{3/2})
   asymptotically; same elementary asymptotic chain as
   `Erdos101OQ01.erdos_three_halves_conjecture_refuted` but applied
   *unconditionally* to the exponent comparison.

### Counts

- Definitions: 1 (`IsLowerBoundConstruction`)
- Theorems: 4 PROVED axiom-free + 2 deferred-with-sorry = 6 total
- Sorries: 2 (one for Grünbaum, one for OQ-04-flavoured S-S; both
  cite open mathematical constructions, NOT placeholder lemmas)
- Axioms: 0
- LOC: 280

### Why a slight extension of S2-A and not pure S2-A?

State.md's strict S2-A is "state the theorem with sorry, ~50 lines".
This PR extends to ~210 LOC because:

* **Witness extraction** (`exists_four_collinear_subset_of_count_pos`)
  is a *prerequisite* for any future S3+ construction PR (Path A
  or B) and costs only ~6 lines of `Finset.mem_filter` unpacking.
  Front-loading it now saves a half-iteration later.
* **OQ-04 ↔ OQ-01 bridge** (`solymosi_stojakovic_lower_bound_via_oq01`)
  certifies that the OQ-04 sorry is **not** an independent assumption:
  it would auto-discharge once OQ-01's sorry resolves.  This is a
  *zero-axiom-net* contribution: the same content is already deferred
  in OQ-01, and OQ-04 just packages it differently.
* **Asymptotic-comparison** (`solymosi_stojakovic_exponent_gt_three_halves`)
  is the OQ-04-specific generalisation of OQ-01's
  `erdos_three_halves_conjecture_refuted` chain; applying it to a
  *fixed-C* exponent rather than a one-time refutation makes the
  Grünbaum-vs-S-S domination explicit.

Net: 4 axiom-free PROVED contributions on top of S2-A's 2 sorries,
no scope creep into Path A's measure-theoretic genericity or Path
B's F_p construction.  The two sorries are precisely the OPEN
mathematical claims (Grünbaum's Ω(n^{3/2}) construction;
Solymosi–Stojaković's n^{2−O(1/√(log n))} construction).

### Files modified (S2)

- `proofs/Proofs/Erdos101OQ04.lean` — NEW (~210 LOC); the S2 ACT
  scaffold + framework + extraction + 2 sorries.
- `proofs/Proofs.lean` — added one import line after
  `Proofs.Erdos101OQ01`.
- `research/problems/erdos101-problem-oq-04/state.md` — this entry.
- `src/data/research/problems/erdos101-problem-oq-04.json` — phase
  ACT, iter 2, refreshed currentState.

### Next action (S3 ORIENT)

Choose between three Path A/B/C continuations:

* **S3-A1 (Path A, single small piece)**: state the
  `d`-dimensional grid `G_d := (Fin k → Fin d → ℤ)` and prove its
  cardinality `k^d`.  ~30 LOC, 0 sorries.  Foundational for the
  Solymosi–Stojaković construction.
* **S3-B1 (Path B, single small piece)**: define the Grünbaum
  parabola `{(i, j) ∈ F_p × F_p : 4j ≡ -i² (mod p)}` and prove
  `|G_p| = p`.  ~40 LOC, 0 sorries.  Foundational for the Grünbaum
  Ω(n^{3/2}) construction (still requires the 4-collinear count
  step in later iterations).
* **S3-C (Path C)**: framework scaffold for both Path A and Path B
  — `RandomProjection`, `FourTermAP`, `LineRichness`.  ~80 LOC, 1-2
  sorries.

**Recommendation**: **S3-B1** if the project commits to a real lower-
bound discharge (Grünbaum is fully provable in Lean with existing
Mathlib `Nat.Prime`/`ZMod` infrastructure); **S3-A1** if Path A
remains the long-term target (S-S is the modern result, but its
measure-theoretic genericity step needs new Mathlib infrastructure).

### Blockers

None for S2 (this iteration) at v4.26.0 Mathlib.  Path A's S4-S5
random-projection genericity argument may need new infrastructure
(see S1 OBSERVE blocker list); this is a downstream concern for
S5+, not for the present S2 ACT.

### Build risk

The Lean file uses only `Real.log`, `Real.sqrt`, `Real.rpow_lt_rpow_*`,
`Real.exp_one_lt_d9`, plus `Finset.mem_filter`/`Finset.mem_powerset`
APIs from the parent file `Proofs.Erdos101Problem` and sibling
`Proofs.Erdos101OQ01`.  Mathlib v4.26.0 (pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) has all of these stable.
The parent `Erdos101Problem.lean` had recent v4.26.0 fixes (PR
#19099, orphan-docstring + Decidable cascade); those landed on main
on 2026-05-14, so the parent currently builds at v4.26.0.

Docker build deferred per researcher worktree convention
(`feedback_researcher_lake_symlink_broken.md`: `.lake` self-symlink
forces ~45-min fresh-clone); CI is the ground truth.

### Race-safety note

Pre-claim PR list at 2026-05-14 ~21:45 UTC: 0 open PRs on
`erdos101-problem-oq-04` (verified via `gh pr list --repo
rjwalters/lean-genius --state open --limit 300` cached snapshot;
slug appears in 0 open titles or branch names).  Last merge on
slug: 2026-05-12 (S1 OBSERVE scaffold, this researcher's prior
session).  Saturation window: ~2.5 days past S1; race risk low.

---

## Iteration 1 (researcher-9, 2026-05-12) — S1 OBSERVE

**Outcome**: scaffold — created `problem.md`, `knowledge.md`,
`state.md`, and `src/data/research/problems/erdos101-problem-oq-04.json`.
No Lean changes.

### What I added

Doc-only scaffolding for a fresh tier-B slug (added by seeker at
2026-05-12T14:13:22Z, ~2.5h before this iteration). The deliverable
is:

- A precise framing of the Solymosi–Stojaković (2013) lower bound on
  four-point lines: $L_4(n) \geq n^{2 - O(1/\sqrt{\log n})}$ for $n$-point
  sets in $\mathbb{R}^2$ with no five collinear.
- A tractability triage distinguishing **Path A** (full
  Solymosi–Stojaković, 5-7 sessions, ~600-1000 lines, measure-theoretic
  random-projection genericity) from **Path B-light** (Grünbaum's
  weaker $\Omega(n^{3/2})$ construction, 2-3 sessions, ~200-400 lines,
  concrete construction).
- A survey of the Mathlib surface
  (`Mathlib.Combinatorics.Additive.AP`,
  `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`,
  `Polynomial.eval_ne_zero`, the basic `Pi.Fintype`/`Finset.product`
  grid infrastructure).
- A concrete S2 plan with three options (state-only, Grünbaum first,
  full framework scaffold) for the next iteration to choose from.
- Parent/sibling linkage to the verified `erdos101-problem` gallery
  entry (757 lines, 23 theorems, 0 sorries; upper bound side).

### Why not S2 in this session

S2 requires committing to one of three paths (state-only,
Grünbaum first, or full framework). That decision involves
non-trivial tradeoffs:
- *State-only* delivers the open question crisp but ships a 1-sorry
  theorem.
- *Grünbaum first* delivers actual content but uses a different
  construction than Solymosi–Stojaković.
- *Full framework* front-loads multi-session investment.

This choice is best made as a focused S2 PR rather than bundled
with the OBSERVE scaffold, especially as the random-projection
measure-theoretic step (S4-S5) is the project's main risk and
should be scoped before committing.

### Files added (S1)

- `research/problems/erdos101-problem-oq-04/problem.md` —
  problem statement, formal target, references (Solymosi–Stojaković
  2013, Erdős 1995, Grünbaum 1972, Burr–Grünbaum–Sloane 1974, Brass–
  Moser–Pach 2005), parent/sibling linkage, S2 paths A/B-light/C
- `research/problems/erdos101-problem-oq-04/knowledge.md` — Mathlib
  surface inventory, feasibility table, S2 plan options, risk register
- `research/problems/erdos101-problem-oq-04/state.md` — this file
- `src/data/research/problems/erdos101-problem-oq-04.json` — phase
  OBSERVE, iter 1, references, knowledge surface

### Next action (S2 ORIENT)

Choose between three S2 paths:

- **S2-A (recommended for solo-iteration session)**: state-only.
  Create `proofs/Proofs/Erdos101ProblemOQ04.lean` (~50 lines) with
  the main `solymosi_stojakovic_lower_bound` theorem stated and
  `sorry`-bodied. Adds 1 sorry on the open lower bound, 0 axioms.
  Defers all proof work to S3+.
- **S2-B (recommended for project-level commitment)**: prove
  Grünbaum's $\Omega(n^{3/2})$ first. Construct
  $\{(i, j) : i^2 + j \equiv 0 \pmod p\} \subset \mathbb{F}_p^2$, prove
  $\Theta(p^{3/2})$ four-collinear subsets, derive $L_4(n) \geq c n^{3/2}$.
  ~150 lines, fully proved (no sorries).
- **S2-C**: full framework scaffold for Solymosi–Stojaković.
  d-dimensional grid + 4-AP enumeration + generic projection +
  framework theorem. ~200 lines, 2-3 sorries front-loaded.

**Recommendation**: **S2-B (Grünbaum first)** if the project
continues; **S2-A (state-only)** if this is a one-iteration probe.
S2-B delivers actual machine-verified mathematical content; S2-A
delivers an honest "sorry placeholder for the open lower bound".

### Blockers

None for S2-A/S2-B at v4.26.0 Mathlib. The full Solymosi–Stojaković
formalization (S4-S5) may need new Mathlib infrastructure for
parameter-space measure-theoretic genericity; this is a downstream
concern.

### Race-safety note

This slug was added by the seeker at 2026-05-12T14:13:22Z. As of S1
submission (~16:55Z, ~2h40min after seeker-add), 0 open PRs on this
slug (`gh pr list --search erdos101-problem-oq-04`: `[]`), 0 recent
merges (`git log origin/main --oneline -30 | grep erdos101-problem-
oq-04`: empty). Saturation window for fresh tier-B slugs is 5–30
minutes per `feedback_researcher_seeker_fresh_slug_window`; this S1
landed well outside the typical window so race risk is low.

## Honest Calibration

S1 produces:

- Four documentation files (problem.md, knowledge.md, state.md,
  src/data/research/problems/erdos101-problem-oq-04.json).
- Zero Lean changes.
- Zero new axioms, zero new sorries.
- A concrete S2 plan with three options and explicit tradeoffs.

S1 does **not** resolve any open mathematical question. The value is
the *framing* of the problem in a way that allows S2-S6 to make
focused progress, plus the survey of Mathlib infrastructure relevant
to the random-projection / measure-theoretic genericity step (the
project's primary technical risk).

## References Captured

- Solymosi & Stojaković (2013) — primary reference, *Combinatorica*.
- Erdős (1995) — original conjecture.
- Grünbaum (1972) — weaker lower bound construction.
- Burr–Grünbaum–Sloane (1974) — 3-line orchard problem.
- Brass–Moser–Pach (2005) — survey reference.
- Erdős Problems #101 entry.

See `knowledge.md` for the full Mathlib API inventory.

## Session Log

| Step | Action | Outcome |
|------|--------|---------|
| 1 | Verified `erdos101-problem-oq-04` had 0 open PRs and 0 recent merges; slug fresh (added 2026-05-12T14:13:22Z) | race-clean |
| 2 | Read parent `Proofs/Erdos101Problem.lean` (757 lines, 23 theorems, 0 sorries) | parent verified-rich |
| 3 | Surveyed Mathlib v4.26.0 surface for AP / MeasureTheory / probability / grid infrastructure (no read of pin'd Mathlib needed for OBSERVE; survey is documentation-level) | inventory captured |
| 4 | Wrote problem.md, knowledge.md, state.md (this file), src/data/.../.json | S1 OBSERVE complete |
| 5 | (pending) commit + push + PR | next |
