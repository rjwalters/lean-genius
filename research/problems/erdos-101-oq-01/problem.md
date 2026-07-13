# Problem: Erdős #101 OQ-01 — Four-point line count is $o(n^2)$

## Statement

### Plain Language

Given $n$ points in $\mathbb{R}^2$ with no five collinear, prove
that the number of lines containing exactly four of the points is
$o(n^2)$.

This is Erdős's $\$100$ open question of Problem #101. Best known:

* **Upper bound** (elementary, Szemerédi–Trotter, or pair-packing
  double-counting): $O(n^2)$. Tight at $n(n-1)/12$ from pure
  combinatorial counting.
* **Lower bound** (Solymosi–Stojaković 2013): $\Omega(n^{2 - O(1/\sqrt{\log n})})$,
  refuting Erdős's earlier $\Theta(n^{3/2})$ conjecture.

The gap is the *polylog correction*; closing it is OQ-01.

### Formal Statement

In `proofs/Proofs/Erdos101OQ01.lean`:

```lean
/-- **OQ-01, primary form**: the maximum four-point line count over
all no-five-collinear planar point sets of size at most `n` is $o(n^2)$. -/
def erdos_101_oq_01_conjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ (P : PlanarPointSet),
    NoFiveCollinear P → N ≤ P.points.card →
    (fourPointLineCount P : ℝ) < ε * (P.points.card : ℝ)^2

theorem erdos_101_oq_01 : erdos_101_oq_01_conjecture := by sorry
```

The single open `sorry` is the main conjecture. All supporting
lemmas (small-case bound, real-valued $O(n^2)$, $n^2/12$ rate) are
unconditional.

## Status — Open

| What | Status |
|------|--------|
| Trivial $O(n^2)$ upper bound | ✓ proved (`fourPointLineCount_le_quadratic`) |
| $n^2/12$ improved bound | ✓ proved (`bounds_at_rate_quadratic_over_twelve`) |
| $o(n^2)$ refinement | OPEN ($\$100$ Erdős prize) |
| Solymosi–Stojaković $\Omega(n^{2-O(1/\sqrt{\log n})})$ lower bound | not yet formalised — deferred to S2 |

## Theoretical Obstacles

1. **Szemerédi–Trotter is too coarse for fixed-multiplicity lines.**
   Applied to lines of multiplicity 4, the incidence bound
   $I(P, L) = O(|P|^{2/3} |L|^{2/3} + |P| + |L|)$ yields only the
   $O(n^2)$ regime. A multiplicity-aware refinement is needed.

2. **Pure double-counting is tight.** The improved upper bound
   $n(n-1)/12$ comes from packing 6 disjoint pairs per 4-collinear
   subset; this is exhausted by the elementary argument and cannot
   be improved without geometric input.

3. **The Solymosi–Stojaković lower bound is nearly quadratic.** The
   open content is the precise polylog correction, not the leading
   $n^2$ behavior.

## References

* Erdős, P. (1984–1997). Problem 101.
  https://erdosproblems.com/101
* Grünbaum, B. (1972). *Arrangements and Spreads*. American Math.
  Soc. — original $\Omega(n^{3/2})$ four-point line construction.
* Solymosi, J., Stojaković, M. (2013). *Many collinear k-tuples with
  no $k+1$ collinear points.* Discrete & Computational Geometry **50**,
  811–820 — disproves $\Theta(n^{3/2})$ with $\Omega(n^{2-O(1/\sqrt{\log n})})$.
* Szemerédi, E., Trotter, W.T. (1983). *Extremal problems in discrete
  geometry.* Combinatorica **3**, 381–392 — incidence bound.

## File Layout

| File | Purpose |
|------|---------|
| `proofs/Proofs/Erdos101OQ01.lean` | S1 scaffold; formal statement, 6 thms, 4 defs, 1 sorry |
| `proofs/Proofs/Erdos101Problem.lean` | parent — 23 thms, 1 def, 0 sorries, 0 axioms |
| `src/data/proofs/erdos-101-oq-01/` | gallery entry (meta, annotations, index.ts) |
| `src/data/research/problems/erdos-101-oq-01.json` | research metadata (knowledge, state) |
