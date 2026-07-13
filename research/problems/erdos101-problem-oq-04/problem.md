# erdos101-problem-oq-04

## Problem Description

**Formalize the Solymosi–Stojaković lower-bound construction for
four-point lines.** Erdős Problem #101 asks for the asymptotic behavior
of the function $L_4(n) := \max_P |\{\ell : |\ell \cap P| = 4\}|$ where
the maximum ranges over $n$-point sets $P \subset \mathbb{R}^2$ with
no five collinear. The parent gallery formalizes the upper bound
$L_4(n) \leq n(n-1)/12$ and the per-point bound $(n-1)/3$, but leaves
the lower bound side untouched.

**Solymosi and Stojaković** (2013, *Combinatorica*) disproved Erdős's
conjectured $\Theta(n^{3/2})$ by constructing $n$-point sets achieving
$L_4(n) \geq n^{2 - O(1/\sqrt{\log n})}$ four-point lines. Their proof
uses a *random perturbation* of a high-dimensional lattice grid: the
construction begins with a $d$-dimensional grid that has many four-term
arithmetic progressions, projects to $\mathbb{R}^2$ via a generic
linear map, and verifies that with positive probability no five
projected points become collinear while a near-quadratic number of
projected four-term APs remain collinear.

The Solymosi–Stojaković construction is now the *best known* lower
bound on $L_4(n)$; combined with the parent gallery's $n(n-1)/12$
upper bound, it sandwiches the true growth rate between
$n^{2 - O(1/\sqrt{\log n})}$ and $\frac{n(n-1)}{12}$. The remaining
$o(n^2)$ question (Erdős's $\$100$ problem) is the asymptotic gap
between these two bounds.

## Formal target

The OQ-04 deliverable is the *Lean formalization* of the
Solymosi–Stojaković lower bound:

```
theorem solymosi_stojakovic_lower_bound :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      ∃ P : PlanarPointSet,
        P.points.card = n ∧
        NoFiveCollinear P ∧
        fourPointLineCount P ≥
          (n : ℝ)^(2 - ε / Real.sqrt (Real.log n))
```

A formalization of the strong form (without the $\varepsilon$) would
prove
$\liminf_{n \to \infty} \frac{\log L_4(n)}{\log n} \to 2$,
which is what Solymosi–Stojaković established.

## Why this matters

1. **Quantitative sandwich for Erdős #101.** The parent gallery
   provides the upper bound $L_4(n) \leq n(n-1)/12$ (sorry-free). A
   formal lower bound — even a weaker version like $L_4(n) \geq c n^{3/2}$
   from Grünbaum's construction (OQ-03) — would make explicit the
   non-trivial growth rate. The Solymosi–Stojaković bound is sharper
   and closes the order-of-magnitude gap to $n^{2-o(1)}$.

2. **Erdős's $\$100$ conjecture refuted (post-2013).** Erdős had
   conjectured $L_4(n) = \Theta(n^{3/2})$. Solymosi–Stojaković
   *disproved* this conjectured shape. A Lean formalization of their
   counterexample is direct documentation of a refuted classical
   conjecture — historically significant in its own right.

3. **Random-perturbation technique.** The proof uses a *generic linear
   projection* and a probabilistic-method-style "with positive
   probability" argument. Formalizing this is a step toward a broader
   Lean library for the *probabilistic method* in incidence geometry
   — a technique that recurs in Erdős-style combinatorics.

4. **High-dimensional lattice constructions.** The intermediate step
   of constructing a $d$-dimensional grid with many 4-term APs is
   itself a useful building block for related problems (e.g.,
   Behrend-style $AP_4$ lower bounds, Szemerédi's theorem cases).

## Forward path

### Path A: full Solymosi–Stojaković in Lean (~600-1000 lines)

1. Define the $d$-dimensional grid $G_d = \{0, 1, \ldots, k-1\}^d$.
2. Enumerate 4-term arithmetic progressions in $G_d$.
3. Define a *generic* linear projection $\pi : \mathbb{R}^d \to \mathbb{R}^2$.
4. Show: with positive probability over the choice of $\pi$, no five
   projected points are collinear (a measure-theoretic / dimensional
   counting argument).
5. Show: every 4-term AP in $G_d$ projects to a 4-collinear set in
   $\pi(G_d)$.
6. Count 4-term APs in $G_d$ and conclude.
7. Optimize the parameters $d, k$ to obtain the $n^{2 - O(1/\sqrt{\log n})}$
   rate.

This is a substantial multi-session formalization. Estimated:
4-6 sessions, ~600-1000 lines, ~10-30 sorries on intermediate steps.

### Path B: SCAFFOLD only (this iteration)

S1 OBSERVE scaffolds the problem documentation, surveys existing
Mathlib infrastructure, and identifies the gap between the parent's
upper-bound work and a Lean-tractable formalization of the lower
bound. No Lean changes in this iteration.

S2 ORIENT would commit to one of two tractability paths:
- **B-light**: state and prove a *weaker* lower bound (e.g., the
  trivial $L_4(n) \geq 0$ or the Grünbaum $\Omega(n^{3/2})$
  reconstruction, if more accessible).
- **B-full**: begin the d-dimensional grid + random projection
  framework with the long path A in view.

## References

- Solymosi, J. and Stojaković, M. (2013), "Many collinear $k$-tuples
  with no $k+1$ collinear points", *Combinatorica* 33: 247–258.
  [DOI:10.1007/s00493-013-2820-6](https://doi.org/10.1007/s00493-013-2820-6)
- Erdős, P. (1995), "Problems and results in combinatorial geometry",
  Problem #101 in the modern enumeration. Original conjecture
  $L_4(n) = \Theta(n^{3/2})$.
- Grünbaum, B. (1972), *Arrangements and Spreads*. Lower-bound
  construction $L_4(n) \gtrsim n^{3/2}$.
- Burr, Grünbaum, Sloane (1974), "The orchard problem". Collinear
  triples (3-line) version.
- Brass, Moser, Pach (2005), *Research Problems in Discrete Geometry*.
  §7.2 surveys the four-point line problem.
- Erdős Problems database: <https://erdosproblems.com/101>.

## Parent / Sibling Linkage

### Parent: `erdos101-problem`

The parent file `proofs/Proofs/Erdos101Problem.lean` (757 lines, 23
theorems, 0 sorries, 0 axioms, status `verified`) provides:

- `PlanarPointSet` — the data structure for finite point sets.
- `collinear : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ → Prop` — signed-area definition.
- `NoFiveCollinear : PlanarPointSet → Prop` — the global no-5-collinear
  predicate.
- `fourPointLineCount : PlanarPointSet → ℕ` — the count of four-point
  lines, via `fourCollinearFamily` (lines 601–610).
- `trivial_upper_bound : ∀ P, NoFiveCollinear P → fourPointLineCount P ≤ n(n-1)/2`.
- `improved_upper_bound : ∀ P, NoFiveCollinear P → fourPointLineCount P ≤ n(n-1)/12`.
- `fourCollinearThrough_bound : ∀ P p, NoFiveCollinear P → |through p| ≤ (n-1)/3`.

All of these definitions/theorems are *reusable* for OQ-04. The
lower-bound work starts from `fourPointLineCount` (definition agrees
with the parent's notion) and constructs witnesses to a lower bound.

### Siblings (potential)

- OQ-03 (Grünbaum, weaker lower bound $\Omega(n^{3/2})$) — does not
  yet exist as a separate slug. May be a precursor sub-target.
- OQ-01 (Szemerédi–Trotter incidence bound) — does not yet exist.
- OQ-02 (the main $o(n^2)$ question) — open, $\$100$ Erdős problem.

## Tractability triage

| Target | Feasible at v4.26.0 Mathlib? | Estimated effort |
|---|---|---|
| State Solymosi–Stojaković bound in Lean (sorry on proof) | ✅ | ~30 lines, S2 |
| Define d-dimensional grid $G_d$ | ✅ | ~20 lines, S2 |
| Enumerate 4-term APs in $G_d$ | ⚠ (depends on Mathlib finite-AP API) | ~50 lines, S3 |
| Generic linear projection (probabilistic) | ⚠ (depends on Mathlib MeasureTheory.Generic / Polynomial.eval_ne_zero) | ~100-200 lines, S4 |
| "No five collinear with positive probability" | ⚠ (measure-theoretic, may need new infrastructure) | ~200-400 lines, S5+ |
| Count 4-APs and conclude | ✅ | ~50 lines, S5 |
| Parameter optimization ($n^{2-O(1/\sqrt{\log n})}$) | ⚠ (log/sqrt analysis) | ~50 lines, S6 |

**Verdict**: tractable as a multi-session project (3-5 sessions for
the framework + statement + weaker variant; 5-7 sessions for the
full quantitative bound). The hardest steps are the generic projection
argument and the no-5-collinear probability bound; both require
careful interaction with Mathlib's measure-theory and probability
infrastructure.

## Honest assessment of contribution boundary

This is a *known classical result* (Solymosi–Stojaković 2013). The
mathematical content is settled; the Lean contribution is the
formalization itself. Significance derives from:

1. Providing a **machine-verified lower bound** complementing the
   parent's machine-verified upper bound — a quantitative sandwich
   for an Erdős problem.
2. Documenting the **random-perturbation incidence-geometry
   technique** in Lean, which transfers to other problems.
3. Demonstrating that Mathlib's measure theory + probability +
   discrete geometry layers can carry a real combinatorial-geometry
   theorem.

The *interesting* part of the formalization is the random-projection
"no 5 collinear" probability argument (S4-S5). The *necessary but
mechanical* parts are the grid / AP enumeration and the parameter
optimization (S2-S3, S6).
