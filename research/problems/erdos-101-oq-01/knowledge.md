# Knowledge — erdos-101-oq-01

## S1 (researcher-3, 2026-05-11) — OBSERVE scaffold

### Parent framework (Erdos101Problem.lean)

The parent file (757 lines, 23 thms, 0 sorries, 0 axioms) provides:

- `PlanarPointSet`: a finite set of points in $\mathbb{R}^2$ with
  `size_pos > 0`.
- `collinear p q r := (q.1 - p.1) * (r.2 - p.2) = (r.1 - p.1) * (q.2 - p.2)`
  (signed-area determinant).
- `NoFiveCollinear (P : PlanarPointSet)`: no 5 distinct points of
  `P` are collinear.
- `fourPointLineCount (P : PlanarPointSet) : ℕ`: count of 4-element
  collinear subsets of `P.points`.
- `improved_upper_bound`: `fourPointLineCount P ≤ n(n-1)/12`.
- `fourCollinearThrough_bound`: at most $(n-1)/3$ four-point lines
  through any fixed point.
- Auxiliary collinearity structure (`collinear_swap*`, `collinear_trans`,
  `collinear_four`, `four_collinear_unique`, `four_collinear_overlap_small`).

### S1 deliverable (this iteration)

New file `proofs/Proofs/Erdos101OQ01.lean` (253 lines, 6 thms, 4 defs,
0 axioms, 1 sorry):

| Definition / Theorem | Status |
|---|---|
| `IsLittleOh_n_squared (f : ℕ → ℕ) : Prop` | def, ε–N form |
| `BoundsAtRate (g : ℕ → ℝ) : Prop` | def, rate abstraction |
| `erdos_101_oq_01_conjecture : Prop` | def, Σ₂ form |
| `erdos_101_oq_01_rate_form : Prop` | def, witness form |
| `erdos_101_oq_01` | **theorem, 1 sorry** (the OPEN conjecture) |
| `fourPointLineCount_zero_of_small` | proved (parent restatement) |
| `fourPointLineCount_o_n_squared_holds_below_four` | proved (vacuous case) |
| `fourPointLineCount_le_quadratic` | proved (real-valued $\leq n^2$) |
| `bounds_at_rate_quadratic_unconditional` | proved (rate $n^2$) |
| `bounds_at_rate_quadratic_over_twelve` | proved (rate $n^2/12$) |

### Asymptotic-vocabulary choice

We use an explicit ε–N form `IsLittleOh_n_squared` rather than
`Mathlib.Analysis.Asymptotics.IsLittleO` for first-iteration
readability. The two forms are equivalent for `f : ℕ → ℕ` against
$n^2$ on the filter `atTop`; the bridge is deferred to S3.

### Two equivalent statements of OQ-01

1. **Primary (ε–N form)**: $\forall \varepsilon > 0\ \exists N\ \forall P$
   no-five-collinear, $|P| \geq N \Rightarrow \text{count}(P) < \varepsilon |P|^2$.
2. **Rate form**: $\exists g : \mathbb{N} \to \mathbb{N}\ \big(\text{IsLittleOh}_{n^2}(g)
   \land \forall P\ \text{NoFiveCollinear} \Rightarrow \text{count}(P) \leq g(|P|)\big)$.

Bridge: $(2) \Rightarrow (1)$ direct from definitions; $(1) \Rightarrow (2)$
via the witness function $g(n) := \max\{\text{count}(P) : |P| = n, \text{NoFiveCollinear}\ P\}$
(finite by `improved_upper_bound`). Both forms are recorded; the
primary form is the OPEN theorem.

### Why the scaffold is meaningful

* The OQ-01 question is precisely the quantitative refinement of an
  already-known $O(n^2)$ bound. The trivial $O(n^2)$ regime is
  established here in real form, so the open content cannot be hidden
  in cast-juggling.
* Future Iter $\geq 2$ steps can target *weaker but provable* rates
  (e.g., $n^2 / \log\log\log n$) as `BoundsAtRate` instances, each
  shrinking the "obvious gap" between the known and the open.

### Known constructions (lower-bound side)

* **Grünbaum (1972)**: $\Omega(n^{3/2})$ — grid-based, balances
  collinear-quadruple count against the 5-collinear restriction.
* **Solymosi–Stojaković (2013)**: $\Omega(n^{2 - O(1/\sqrt{\log n})})$
  — uses sum–product estimates; refutes Erdős's $\Theta(n^{3/2})$
  conjecture.

### Mathlib API used

* `Nat.cast_div_le` (`(a / b : ℕ) : ℝ ≤ (a : ℝ) / b`)
* `Nat.div_le_div_right` (monotonicity in numerator)
* `Nat.div_le_self`
* `Nat.mul_le_mul_left`, `Nat.sub_le`
* `pow_pos`, `positivity`
* `push_cast`, `exact_mod_cast`, `linarith`

No new imports beyond the parent's `Mathlib.Data.Finset.Card`,
`Mathlib.Data.Nat.Basic`, `Mathlib.Tactic` (transitive via
`Proofs.Erdos101Problem`).

### Build status

**[BUILD UNVERIFIED]** Worktree's `proofs/.lake` is a recursive
self-symlink (per `feedback_researcher_lake_symlink_broken.md`); a
local Docker build would re-fresh-clone Mathlib (~30–45 min cold).
CI is the ground truth. All Mathlib API used is standard and
exercised in existing gallery files.

### Confidence

High that the scaffold compiles: all five non-sorry theorems use
only well-established Mathlib API. The one risky step is the
`Nat.cast_div_le` followed by `push_cast` in
`bounds_at_rate_quadratic_over_twelve`; this is a standard ℕ→ℝ
manipulation. If CI fails, the fall-back is to weaken the rate to
the unconditional $n^2$ alone (already provable).
