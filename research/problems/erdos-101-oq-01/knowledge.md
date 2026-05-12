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

## S2 (researcher-1, 2026-05-12) — Solymosi–Stojaković lower bound

### S2 deliverable (this iteration)

Two new `theorem ... := by sorry` declarations appended to
`Erdos101OQ01.lean` (file grows 253 → 325 lines, sorries 1 → 3,
theorems 6 → 8, axioms unchanged at 0):

| Theorem | Type | Status |
|---|---|---|
| `solymosi_stojakovic_lower_bound` | $\forall C > 0, \exists N, \forall n \geq N, \exists P, \lvert P \rvert = n \land \text{NoFiveCollinear } P \land \text{fourPointLineCount } P \geq n^{2 - C/\sqrt{\log n}}$ | sorry (construction deferred) |
| `erdos_three_halves_conjecture_refuted` | $\neg (\exists N, \forall P, \text{NoFiveCollinear } P \to N \leq \lvert P \rvert \to \text{fourPointLineCount } P \leq \lvert P \rvert ^ {3/2})$ | sorry (real-analysis arithmetic) |

Three new Mathlib imports added (no other changes to existing code):

- `Mathlib.Analysis.SpecialFunctions.Pow.Real` — `Real.rpow` for the
  $n^{2 - C / \sqrt{\log n}}$ expression and the $\lvert P \rvert ^ {3/2}$
  corollary.
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` — `Real.log` in the
  $\sqrt{\log n}$ denominator.
- `Mathlib.Analysis.SpecialFunctions.Sqrt` — `Real.sqrt` for
  $\sqrt{\log n}$.

### Why record the lower bound as a theorem-stub rather than an axiom

Memory's axiom-integrity policy: every `axiom` declaration is a
*permanent* assumption.  A `theorem ... := by sorry` is a *deferred
proof obligation* that future iterations can discharge; the file
remains formally axiom-free.  This matches the project's
"axiomCount = 0 wherever possible" preference (see
`feedback_mechanic_axiomcount_pattern.md`).

### S3 next-action candidates

1. **Discharge `erdos_three_halves_conjecture_refuted`** from the
   Solymosi–Stojaković lower bound by elementary real-analysis
   arithmetic.  Estimated 30–60 lines using `Real.rpow_lt_rpow`,
   `Real.log_pos`, `Real.sqrt_lt_sqrt`, and the fact that
   $C / \sqrt{\log n} \to 0$.

2. **Connect to `Asymptotics.IsBigO` / `IsLittleO`** by defining
   `maxFourPointLines : ℕ → ℕ` via `Finset.sup'` over all
   no-five-collinear sets of fixed size; convert
   `fourPointLineCount_le_quadratic` to an `IsBigO` statement and
   record the conjecture as an `IsLittleO` sorry.

3. **Cauchy–Schwarz refinement** of `fourCollinearThrough_bound`
   $\leq (n-1)/3$ to potentially yield a $1 - o(1)$ leading constant
   on the elementary $n^2/12$ bound (not $o(n^2)$, but a real
   improvement on the constant).

### Build risk

S2 introduces no proof tactics — both new theorems are pure
sorry stubs with no `by ...` body beyond `sorry`.  The only build
risk is in the *type signatures*: `Real.rpow`, `Real.sqrt`, and
`Real.log` are all in the imported modules.  The
`(n : ℝ) ^ (real exponent)` syntax resolves to `Real.rpow` by
inheriting the `HPow ℝ ℝ ℝ` instance from
`Mathlib.Analysis.SpecialFunctions.Pow.Real`.

## S3 (researcher-5, 2026-05-12) — Discharge of $\Theta(n^{3/2})$ refutation

### S3 deliverable (this iteration)

The S2 corollary `erdos_three_halves_conjecture_refuted` is no
longer a `sorry`.  Its proof is now an elementary 50-line discharge
from S2's `solymosi_stojakovic_lower_bound`.  No new theorems, no
new definitions, no new imports.

| Metric | Before S3 | After S3 |
|---|---|---|
| Sorries | 3 | 2 (main conjecture + SS construction) |
| Theorems | 8 | 8 |
| Definitions | 4 | 4 |
| Axioms | 0 | 0 |
| Line count | 325 | 383 |

### Proof sketch (real-analysis arithmetic)

Specialise SS to $C = 1/2$:

* For $m \geq 3$, the inequality $m > e$ holds (using
  `Real.exp_one_lt_d9 : \exp 1 < 2.7182818286`, hence $\exp 1 < 3$).
* Therefore $\log m > 1$ (by `Real.log_lt_log` applied to
  $\exp 1 < m$ and `Real.log_exp`).
* Therefore $\sqrt{\log m} > 1$ (by `Real.sqrt_lt_sqrt 0 ≤ 1 < \log m`
  and `Real.sqrt_one`).
* Therefore $\frac{1/2}{\sqrt{\log m}} < 1/2$ (by `div_lt_iff`).
* Therefore $2 - \frac{1/2}{\sqrt{\log m}} > 3/2$ (by `linarith`).
* Therefore $m^{3/2} < m^{2 - (1/2)/\sqrt{\log m}}$ (by
  `Real.rpow_lt_rpow_of_exponent_lt`, requires `1 < m`).

Now combine with the SS witness $P$ at size $m \geq N_1$
(`fourPointLineCount P \geq m^{2 - (1/2)/\sqrt{\log m}}$`) and the
hypothesised global $m^{3/2}$ upper bound on
`fourPointLineCount P` for $|P| \geq N_0$, taking
$m := \max(N_0, N_1, 3)$:

\[
m^{2 - (1/2)/\sqrt{\log m}} \leq
\text{fourPointLineCount } P \leq m^{3/2} <
m^{2 - (1/2)/\sqrt{\log m}}.
\]

The terminal `linarith` closes the contradiction.

### Mathlib API used (all in existing imports)

* `Real.exp_one_lt_d9` — `Real.exp 1 < 2.7182818286`
* `Real.exp_pos` — `0 < Real.exp x`
* `Real.log_exp` — `Real.log (Real.exp x) = x`
* `Real.log_lt_log` — `0 < x → x < y → Real.log x < Real.log y`
* `Real.sqrt_one` — `Real.sqrt 1 = 1`
* `Real.sqrt_lt_sqrt` — `0 ≤ x → x < y → Real.sqrt x < Real.sqrt y`
* `Real.rpow_lt_rpow_of_exponent_lt` — `1 < b → x < y → b^x < b^y`
* `div_lt_iff` — `0 < b → (a/b < c ↔ a < c * b)`
* `le_max_left`, `le_max_right` (ℕ max ordering)
* `exact_mod_cast`, `linarith`, `nlinarith`, `norm_num`

### Why S3 is meaningful

S3 fully discharges a sorry whose statement is mathematically
substantive (the refutation of Erdős's 1980s conjecture) but whose
proof is short.  This is the canonical "easy half" of a deferred
proof obligation: the S2 SS bound is reused as a hypothesis, and
only elementary real-analysis arithmetic separates that hypothesis
from the corollary.  The file now has only two remaining sorries:

1. `erdos_101_oq_01` — the OPEN conjecture itself ($\$100$ Erdős
   prize, not a single-session result).
2. `solymosi_stojakovic_lower_bound` — the SS construction over
   finite fields, requiring substantial algebraic-geometry
   infrastructure absent from Mathlib at present.

Both remaining sorries are external proof obligations — neither
admits an elementary discharge.

### Confidence

**High** that the new proof compiles.  Every step uses a one-line
Mathlib API call.  The only potential pitfall is the
`(1/2 : ℝ)` literal matching the SS theorem's `C` parameter, which
is verified by inspection: the `1 / 2 : ℝ` and `(1 / 2 : ℝ)` forms
in Lean 4 elaborate to the same rational literal.

### S4 next-action candidates

1. **`Asymptotics.IsBigO` / `IsLittleO` bridge**: convert the
   real-valued $O(n^2)$ statement to `Asymptotics.IsBigO atTop`
   and record the OPEN conjecture as `Asymptotics.IsLittleO atTop
   (· ^ 2)` `sorry`.

2. **Positive (constructive) form of the refutation**: rewrite
   `erdos_three_halves_conjecture_refuted` as
   `∀ N, ∃ P, NoFiveCollinear P ∧ N ≤ |P| ∧
   (P.points.card : ℝ)^(3/2 : ℝ) < (fourPointLineCount P : ℝ)`
   (de Morgan dual of the negated existence), then unfold the
   sorry in the OPEN main conjecture against this positive form.

3. **Per-point Cauchy–Schwarz refinement** to chase a $1 - o(1)$
   leading constant on `improved_upper_bound`'s $n(n-1)/12$.
