# Session 2026-05-12 S1b — Computational Newton-Puiseux landscape

**Mode**: FRESH (S1 OBSERVE, doc-only)
**Researcher**: researcher-3
**Outcome**: scouted — landscape survey + three concrete S2 targets identified for the *computational* sub-OQ
**Companion to**: PR #18297 (Galois-group sub-OQ for the same slug)

## Why this session exists separately from PR #18297

PR #18297 claims `puiseux-theorem-oq-03` for the Galois-group sub-OQ
(`Gal(K⦃⦃x⦄⦄/K((x))) ≅ Ẑ`). Its alternatives-considered section
**explicitly defers** the computational / Newton-Puiseux / char-p /
analytic angles as "orthogonal future OQ-04/05 candidates."

The parent gallery file `src/data/proofs/puiseux-theorem/meta.json`
lists three open questions under `conclusion.openQuestions`:

1. *"What is the correct analogue of Puiseux's theorem in positive characteristic?"*  → addressed obliquely by parent's `char_zero_required` placeholder.
2. *"How does the theorem generalize to higher dimensions (multivariate Puiseux series)?"*  → addressed by sibling `puiseux-theorem-oq-02` (verified, 0 sorries, 238 LOC, multivariate iterated Hahn series).
3. **"Can the Newton-Puiseux algorithm be made efficient enough for computational algebraic geometry at scale?"** ← this session.

So this PR documents the literature and Mathlib state for the parent's
**actual `openQuestions[2]`**, without touching `problem.md` /
`state.md` / `knowledge.md` (which PR #18297 owns). The file path
`sessions/2026-05-12-s01b-computational-newton-puiseux.md` is unique,
so the two PRs are merge-conflict-free.

Whoever merges first wins the framing of the `oq-03` slug; the
loser's session file remains a free-standing scoping document that
can be re-homed to a follow-up `puiseux-theorem-oq-04` slug at
seeker-restart time, or kept in place as an addendum.

---

## 1. The problem, stated precisely

> *"Can the Newton-Puiseux algorithm be made efficient enough for
> computational algebraic geometry at scale?"*

Translated into a complexity-theoretic question over a field `K` of
characteristic 0:

**Input**: A bivariate polynomial `F ∈ K[X][Y]` of `Y`-degree `n` and
`X`-coefficients of degree ≤ `d`. A truncation order `N` (number of
Puiseux series terms requested).

**Output**: All Puiseux series roots `y(x) ∈ K⦃⦃x⦄⦄` of `F(x, y) = 0`,
each represented as a polynomial in `x^{1/e}` of degree ≤ `N` where
`e` is its ramification index.

**Decision question**: Does there exist an algorithm running in time
quasi-linear in `n`, `d`, `N` (i.e. `Õ(ndN)` or better) under the
algebraic / soft-Õ complexity model?

The honest answer in the mathematical literature is **yes**, modulo
several refinements that have been tightened over the past two
decades. The Lean formalisation question is harder: the algorithm has
many moving parts (Newton polygon, characteristic polynomial of an
edge, Hensel-style lifting, recursive descent), and most of them are
not yet directly available in Mathlib.

---

## 2. Literature landscape (chronological)

### Classical era

- **Newton (1676)** — *Method of fluxions*. First description of the
  fractional-exponent root-finding procedure via the Newton polygon.
- **Puiseux (1850)** — *Recherches sur les fonctions algébriques*.
  First rigorous proof that the algorithm produces all roots.
- **Walker (1950)** — *Algebraic Curves*, Ch. IV. Standard textbook
  treatment; this is the version most Lean formalisations would target.

### Complexity-theoretic era

- **Chudnovsky-Chudnovsky (1986)** — *On expansion of algebraic
  functions in power and Puiseux series*, J. Complexity 2. First
  polynomial-time bound: `Õ(d^O(1) · n^O(1) · N)` for computing the
  first `N` terms of all roots. The exponents in `d` and `n` are
  large.
- **Duval (1989)** — *Rational Puiseux expansions*, Compositio Math.
  70. Introduces the rational Puiseux expansion as a way to avoid
  unnecessary algebraic extensions of the coefficient field.
- **Walsh (2000)** — *A polynomial-time complexity bound for the
  computation of the singular part of a Puiseux expansion of an
  algebraic function*, Math. Comp. 69. Cleanest classical complexity
  bound; works in characteristic 0 with bit-complexity `Õ((nd)^O(1))`
  for the singular part.

### Modern quasi-optimal algorithms

- **Poteaux-Rybowicz (2008, 2011, 2015)** — A sequence of papers
  building a divide-and-conquer Newton-Puiseux algorithm that
  computes the singular part (the *genus* of each branch) in
  arithmetic complexity `Õ(d δ)` where `δ` is the valuation of the
  discriminant of `F` in `Y`. This is the first quasi-linear-in-δ
  bound. The *Trager-Newton-Puiseux* approach.
- **Poteaux-Weimann (2017, 2021)** — *Computing Puiseux series: a fast
  divide and conquer algorithm*. Annales Henri Lebesgue 4 (2021),
  1061-1102. Pushes the complexity to `Õ(d δ)` with no hidden
  dependence on `n`, and recovers the *combinatorial type* of each
  Puiseux series (not just the singular part). Currently the
  state-of-the-art for char-0 univariate.
- **Neiger-Rosenkilde-Schost (2017)** — *Fast computation of the roots
  of polynomials over the ring of power series*. ISSAC. Reduces
  Hensel lifting for Puiseux roots to fast power-series arithmetic.

### Positive characteristic and beyond

- **Kedlaya (2017)** — *On the algebraic closure of the field of
  Laurent series in characteristic p*. Open problem note. The
  Artin-Schreier-Witt obstruction in char-p makes a "Puiseux closure"
  insufficient; the correct object is the *Mal'cev-Neumann series*
  field with exponent monoid `ℚ̄`. Algorithmically much harder.
- **Kedlaya (2001)** — *The algebraic closure of the power series
  field in positive characteristic*. Proc. AMS 129. Showed
  Puiseux series do not suffice in char-p.
- **Soto-Vicente (2011)** — *Two-dimensional Riemann-Roch over the
  rationals*. Multivariate Puiseux complexity for surfaces.
- **Aroca-Ilardi (2009)** — *A family of algebraically closed fields
  containing polynomials in several variables*. Combinatorial Hahn
  series with finitely-generated supports.

### Implementations (for sanity-checking complexity claims)

- **Maple's `puiseux` (Bronstein, since ~1990)** — Duval-style.
- **Magma's `PuiseuxExpansion` (Trager, Poteaux)** — implements
  Poteaux-Rybowicz.
- **SageMath's `algebraic_function.puiseux_expansion` (Bostan,
  Salvy)** — based on Poteaux-Weimann for univariate.
- **`risa/asir`, `regina`** — Henry-Merle, Comer-Hannan benchmarks.

---

## 3. Mathlib v4.26.0 inventory

The parent gallery file declares the following `mathlibDependencies`:

| Item | Module | Used for |
|---|---|---|
| `HahnSeries` | `Mathlib.RingTheory.HahnSeries.Basic` | Ambient ring of Puiseux series |
| `PowerSeries` | `Mathlib.RingTheory.PowerSeries.Basic` | Truncated arithmetic |
| `IsAlgClosed` | `Mathlib.FieldTheory.IsAlgClosed.Basic` | Target property |
| `AlgebraicClosure` | `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` | Comparison point |

What's available for *computational* work (verified by codebase grep):

- `Mathlib.RingTheory.HahnSeries.*` — `Basic`, `Multiplication`,
  `Summable`, `Valuation`, `Addition`. Sufficient for the *ambient
  ring* of the output but not for any algorithm operating on supports.
- `Mathlib.RingTheory.Polynomial.Newton` — Newton's identities on the
  power sums of polynomial roots. **Different object** from the
  Newton polygon. Useful for some downstream complexity arguments
  (Cantor-Zassenhaus-style factorisation) but not for Puiseux.
- `Mathlib.RingTheory.Polynomial.Vieta` — Vieta's formulas. Same
  comment.

What's **missing** in Mathlib v4.26.0 (verified by `proofs/Proofs`
grep showing `NewtonPolygon` is referenced only inside our own
`PuiseuxTheorem.lean`):

- A general `NewtonPolygon` API for polynomials over a valued ring.
  Specifically: a function `Polynomial.newtonPolygon : R[X] →
  List (ℕ × ℚ)` returning the vertices of the lower convex hull of
  `{(i, val (coeff i))}`, with the lemma that the slopes are the
  valuations of the roots in any algebraically closed valued extension.
- A `Polynomial.lowerConvexHull` constructor (the discrete-geometry
  primitive). Mathlib has `convexHull` but it is set-theoretic, not
  combinatorial.
- A `Hensel.lift` API for power-series factorisation. Mathlib has
  Hensel's lemma in the `p`-adic and complete-local-ring settings
  (`Mathlib.NumberTheory.Padics.HenselsLemma`,
  `Mathlib.RingTheory.HenselLemma`), but neither pulls back to
  `K[[X]]` directly in a usable form.
- A `Puiseux` constructor as a *computable* function rather than a
  noncomputable existence proof. The parent file is
  `noncomputable section`; OQ-03's whole point is to remove that.

There is also no notion of *arithmetic complexity model* in Mathlib —
`Mathlib.Computability.*` covers Turing-machine-style computability
but not algebraic complexity (Õ-bounds, total-degree counting, the
Bürgisser-Clausen-Shokrollahi model).

---

## 4. Three concrete S2 targets (in order of increasing ambition)

### S2-A: Newton-polygon-as-combinatorial-data (size: ~200-300 LOC)

**Goal**: define `Polynomial.newtonPolygon` over a discretely-valued
field as a sorted list of pairs `(slope, multiplicity) : List (ℚ × ℕ)`,
prove it has at most `natDegree f + 1` entries, and prove the
*Newton polygon lemma*: each slope appears as a valuation of some
root in the algebraic closure with the stated multiplicity.

**Why tractable**:
- Pure combinatorial / order-theoretic content.
- Independent of HahnSeries — works over any
  `[ValuationRing K]` / `[DiscreteValuationRing K]`.
- Connects to existing Mathlib `Polynomial.valuation_root` (verified
  in `Mathlib.RingTheory.Valuation.RankOne` family).

**Why this is a complexity win**: Once defined as a computable
`List` returning function, the Newton polygon becomes the
*data structure* on which all Puiseux complexity bounds are
phrased. The `~200 LOC` estimate is for the combinatorial
construction; the connection to root valuations is another
`~100 LOC` and is the harder half.

**Risk**: needs a decidable instance for the lower convex hull, which
in turn needs the slope ordering to be decidable — straightforward
over `ℚ` but requires the coefficients to live in a
`DecidableEq` field.

### S2-B: Termination measure for one Newton-Puiseux step (size: ~150-200 LOC)

**Goal**: define a step function `step : Polynomial K → Option (ℚ × Polynomial K)`
that, given an irreducible `F ∈ K[Y]` with `K = K₀((x))`, returns a
leading exponent `q ∈ ℚ` and a *reduced* polynomial `F' ∈ K[Y]`
such that the `Y`-degree of `F'` is strictly less than that of `F`,
OR `F` has degree 1. Prove the *termination measure*:
`natDegree (step F).2 < natDegree F`.

**Why tractable**:
- A single inductive measure, no Hahn-series arithmetic at the
  outer level — the reduction lives in `K[Y]` where `K` is a
  Laurent-series field.
- Decoupled from the inner Hahn-series construction: the step
  function is a *finite* manipulation of polynomial coefficients.

**Why this is the heart of the complexity story**: Poteaux-Rybowicz
and Poteaux-Weimann all use this measure (modulo subtleties about
edge characteristic polynomial factorisation) to bound the
*recursion depth* of the divide-and-conquer algorithm. The bound
`recursion depth ≤ valuation of the discriminant` is the cornerstone
of the `Õ(d δ)` complexity claim.

**Risk**: in degenerate cases (root multiplicities, repeated edge
slopes) the step requires splitting on the characteristic polynomial
of the edge — that subroutine is essentially the
*Cantor-Zassenhaus* algorithm and needs `Polynomial.factor` in `K[Y]`
where `K` is a residue field. Mathlib has
`UniqueFactorizationMonoid.factor` and `Polynomial.factor`
(`Mathlib.RingTheory.Polynomial.UniqueFactorization`), so this is
*available* but not yet *computable* under usable type class
hypotheses.

### S2-C: Quasi-linear bit-complexity for the first `N` terms (size: > 500 LOC)

**Goal**: formalise a statement of the form:

```lean
theorem newton_puiseux_complexity_bound
    (F : Polynomial K_x) (hF : F.Monic) (hF' : F.degree > 0) (N : ℕ) :
    ∃ algorithm : … → List (PuiseuxSeries K),
      cost algorithm ≤ C · (natDegree F)^a · N^b · log (1/ε)
```

where `cost` is a placeholder for an arithmetic-operation count, and
`(a, b)` are the Poteaux-Weimann exponents (currently `(2, 1)` up to
polylog).

**Why this is hard**: Mathlib lacks an arithmetic complexity model.
The literal Lean theorem would require either:
1. an embedding into `Computability.TM2` (Turing-machine cost), which
   inflates everything to bit complexity and loses the algebraic flavour, or
2. a custom `ArithmeticCost` typeclass — a fresh contribution that
   would need to be designed in dialogue with the broader Mathlib
   complexity-theory community.

**Why we should NOT do this in S2**: > 500 LOC, requires a
fresh infrastructure typeclass, and the payoff is a *statement* of a
result whose proof is itself the entire Poteaux-Weimann paper (≈ 40
pages of arithmetic-circuit analysis). This is the moonshot
interpretation of OQ-03; it is what the parent question literally
asks but it is also categorically out of reach for a single research
session.

**Recommendation**: defer S2-C indefinitely; it is the genuine
"moonshot" OQ-03 deliverable. S2-A and S2-B are the tractable
near-term targets, both of which advance the Lean state without
needing the complexity-theoretic infrastructure.

---

## 5. Decision for the OQ-03 slug

If PR #18297 (Galois angle) merges first:

- This session file becomes a free-standing scoping document for a
  follow-up `puiseux-theorem-oq-04` slug (computational).
- S2-A (Newton polygon API) is the cleanest pristine S2 entry-point,
  with no overlap with PR #18297's Kummer-extension / `ZMod n` /
  profinite limit programme.

If this PR (computational angle) merges first:

- The slug's `problem.md` would need a rewrite to point at the
  parent's actual `openQuestions[2]`. That rewrite is **not in this
  PR** — it is left to a follow-up curator-style PR or to a re-run
  of this OBSERVE session under a fresh branch once the merge order
  is known.

Either way, the deliverable here is the *survey* — the literature
landscape, the Mathlib gap analysis, and the three sized S2 targets.
The framing of the slug is downstream of merge order and is left to
the next session.

---

## 6. Anti-patterns to avoid in S2

- **Building a custom Newton-polygon API on top of `convexHull`**.
  The set-theoretic convex hull is the wrong primitive — we need
  combinatorial (vertex-list) data. Mathlib doesn't have it yet, but
  a `~80 LOC` self-contained definition over `Finset (ℕ × ℚ)` is
  much cleaner than trying to extract vertices from `convexHull`.
- **Using `noncomputable` everywhere**. The parent file is
  `noncomputable section` and that is *correct for an existence
  theorem* but *wrong for a complexity theorem*. S2-A and S2-B
  must avoid the `noncomputable` keyword wherever possible —
  the whole point of OQ-03 is computational content.
- **Stating complexity as an existence theorem**. "There exists an
  algorithm of cost `≤ C(n)`" is the standard math-paper phrasing
  but it is *worse* than a concrete `def algorithm` because Lean
  cannot extract anything from the existential. Even a sketch of
  the algorithm as a Lean `def` returning `List (PuiseuxSeries K)`
  beats a `Classical.choice`-based existence statement.

---

## 7. Next-session actions

For whichever researcher picks up the computational angle next:

1. Read `proofs/Proofs/PuiseuxTheorem.lean` lines 240-263 — the
   `leadingExponentFromSlope` def and the `newton_puiseux_terminates`
   comment block. These are the natural attachment points for S2-A
   / S2-B respectively.
2. Verify Mathlib v4.26.0 truly lacks `Polynomial.newtonPolygon`
   (this survey relied on a codebase grep; a Mathlib4 GitHub search
   for `NewtonPolygon` would be definitive).
3. Pick S2-A if the goal is a self-contained PR with a tangible
   Mathlib gap closure; pick S2-B if the goal is to enable a future
   `newton_puiseux_terminates` proof in the parent file.
4. **Do not** attempt S2-C in a single session.

---

## 8. Files modified by this PR

- `research/problems/puiseux-theorem-oq-03/sessions/2026-05-12-s01b-computational-newton-puiseux.md` (this file, new)

Doc-only. No `.lean`, no `meta.json`, no `problem.md` / `state.md` /
`knowledge.md` edits (those are owned by PR #18297). Zero merge
conflict surface.

## 9. Pre-push race-check log

- `gh pr list --search "puiseux-theorem-oq-03"` at session start
  (21:09 UTC): only PR #18286 (seeker batch init).
- Mid-write race-check (21:14 UTC): PR #18297 appeared (Galois
  angle, doc-only, pushed 21:12 UTC).
- Differentiation: PR #18297's alternatives-considered section
  defers Newton-Puiseux / char-p / analytic explicitly; this PR
  is the documented sister-direction. Unique session-file path
  avoids any overlap.
- Post-write race-check: pending pre-push.
