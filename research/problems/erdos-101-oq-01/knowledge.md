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

## S12 (researcher-1, 2026-05-24) — IsBigO / IsLittleO bridge to Mathlib idiom

### S12 deliverable (this iteration)

Three artifacts inserted into `Erdos101OQ01.lean` after
`bounds_at_rate_quadratic_over_twelve` (pre-edit L204 end), before the
S2 doc block (pre-edit L208 onward). All five S9 + S10 audit-flagged
bugs (F/G/H/I/J) inlined per S10 PREP §5.1–§5.3.

| Artifact | Type | LOC | Sorries | Notes |
|---|---|---|---|---|
| `maxFourPointLines (n : ℕ) : ℕ := n*(n-1)/12` | noncomputable def | ~3 | 0 | aggregator surrogate |
| `maxFourPointLines_isBigO_n_squared` | theorem | ~17 | 0 | Bug-I fix: single-norm `rw [Real.norm_of_nonneg]` |
| `fourPointLineCount_le_max (P) (hP : NoFiveCollinear P)` | theorem | ~8 | 0 | Bug-G fix: load-bearing `NoFiveCollinear` |
| `isLittleOh_n_squared_iff_isLittleO (g : ℕ → ℕ)` | lemma | ~28 | 0 | Bug-H fix: first materialisation |
| `erdos_101_oq_01_isLittleO_form` | def | ~6 | 0 | Bug-F fix: existential, not concrete |
| `erdos_101_oq_01_rate_form_iff_isLittleO` | theorem | ~10 | 0 | uses bridge lemma |
| `erdos_101_oq_01_isLittleO` | theorem | ~4 | 1 | OPEN, the main conjecture in Mathlib idiom |

Two new imports: `Mathlib.Analysis.Asymptotics.Defs` +
`Mathlib.Order.Filter.AtTopBot.Basic`.

### Counter deltas

| Metric | Pre-S12 | Post-S12 | Δ |
|---|---|---|---|
| Sorries | 2 | 3 | +1 |
| Axioms | 0 | 0 | 0 |
| Theorems | 9 | 13 | +4 |
| Lemmas | 0 | 1 | +1 |
| Defs | 4 | 6 | +2 |
| LOC | 471 | 603 | +132 (~78 body + ~54 docstrings) |

### Why the artifact-(i) IsBigO body uses a single `Real.norm_of_nonneg`

`Asymptotics.IsBigO.of_norm_le` has signature:
```
theorem IsBigO.of_norm_le {g : α → ℝ} (h : ∀ x, ‖f x‖ ≤ g x) : f =O[l] g
```
Note `g x`, **not** `‖g x‖`. After `apply IsBigO.of_norm_le; intro n`,
the goal is:
```
⊢ ‖(maxFourPointLines n : ℝ)‖ ≤ (n : ℝ)^2
```
There is **only one** `‖·‖` to collapse (on the LHS). Using
`rw [Real.norm_of_nonneg (by positivity)]` collapses it cleanly; no
`show |·| ≤ |·|`, no `rw [abs_of_nonneg, abs_of_nonneg]` (the second
`abs_of_nonneg` would have no target).

This is the canonical "bearer existence audited, bearer shape not"
pitfall — S9 PREP §6 verified the lemma's *name* but not its
*hypothesis shape* (one norm, not two). S10 PREP §4 caught it via
goal-state walking.

### Why the artifact-(ii) bridge's `←` direction needs `c := ε/2` + `max N₀ 1` lift

Going from Mathlib's `Asymptotics.IsLittleO atTop ↑g (·^2)` (`≤`-form)
to slug's `IsLittleOh_n_squared g` (strict `<`-form) requires a strict
gap. Mathlib's form gives `∀ c > 0, ∀ᶠ n, (g n : ℝ) ≤ c * (n : ℝ)^2`.
To establish slug's `(g n : ℝ) < ε * (n : ℝ)^2`, we:

1. Instantiate Mathlib's `c` at `ε / 2`, giving
   `(g n : ℝ) ≤ (ε/2) * (n : ℝ)^2`.
2. Lift `N` to `max N₀ 1` so that `(n : ℝ)^2 > 0` (the `n = 0` vacuous
   case would fail strict `<`).
3. `nlinarith` (with `hn_sq_pos : 0 < (n : ℝ)^2` in context) closes
   `(g n : ℝ) ≤ (ε/2) * (n : ℝ)^2 → (g n : ℝ) < ε * (n : ℝ)^2`.

The `→` direction is *direct*: slug's strict `<` is *stronger* than
Mathlib's `≤`, so `linarith` after `Real.norm_of_nonneg` on each side
closes it without any `c := ε/2` trick.

S6 PREP §"S6 ACT scope" originally got the direction-mapping
*backward* (assigning the `ε/2` trick to the `→` direction); S7 PREP
§3 corrected it.

### Why the per-`P` corollary needs `NoFiveCollinear` as a load-bearing hypothesis

Without `hP : NoFiveCollinear P`, the bound
`fourPointLineCount P ≤ maxFourPointLines |P|` is refutable. Counterexample:
9 collinear points on a single line. Then:
- `fourPointLineCount P = C(9, 4) = 126` (every 4-element subset of the 9
  is collinear).
- `maxFourPointLines 9 = 9 * 8 / 12 = 72 / 12 = 6`.

So `126 > 6`, contradicting the bound.

The hypothesis routes through `improved_upper_bound P hP` (parent file),
which itself depends on `NoFiveCollinear` to prove
`fourPointLineCount P ≤ |P| * (|P| - 1) / 12`. S9 PREP Bug-G first
surfaced this — the S8 STATE-SYNC narrative's "per-P corollary" omitted
`hP` and would have been refuted at 9 collinear points.

### Why artifact (iii) is the existential form, not concrete IsLittleO on `maxFourPointLines`

S8 STATE-SYNC's narrative §3 had artifact (iii) as a *concrete*
`IsLittleO` statement: `Asymptotics.IsLittleO atTop ↑maxFourPointLines
(·^2)`. This is **unsound**: `maxFourPointLines n = n*(n-1)/12` has
ratio `n*(n-1)/12 / n² → 1/12`, which is *nonzero*. The IsLittleO
statement would be **false** at this surrogate.

The correct artifact (iii) is the *existential*: `∃ g : ℕ → ℕ,
Asymptotics.IsLittleO atTop ↑g (·^2) ∧ BoundsAtRate ↑g`. The witness
`g` is the (unknown) o(n²) rate that OQ-01 conjectures exists; the
existential is OPEN, sorry-able.

S9 PREP Bug-F first surfaced this — the S8 narrative description of
artifact (iii) would have been false-on-elaboration at the
`maxFourPointLines / n²` ratio limit.

### Build risk

Build NOT verified locally (worktree's `.lake` is a self-symlink).
Forecast ≤ 2 Docker iterations per S10 §8 gate 7. Likely iter-2 fix
sources:

1. `Real.norm_of_nonneg` vs `Real.norm_natCast` normalisation: fall
   back to `simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity)]`.
2. `nlinarith` in artifact (ii) ← direction: fall back to explicit
   `calc` chain (S10 §11 ~3 extra LOC).

### Why S12 is meaningful

S12 is the **first** session in the S6–S10 PREP chain that actually
edits `Erdos101OQ01.lean` — the prior six iterations (S6 plan + S7
audit + S8 STATE-SYNC + S9 audit + S10 audit + S11 STATE-SYNC) were
all doc-only, surfacing successive layers of audit-flagged bugs in the
queued recipe. S12 lands the recipe verbatim with all five corrections
inlined.

The slug now has two equivalent open statements of OQ-01: the original
ε–N `erdos_101_oq_01` and the Mathlib-idiom existential
`erdos_101_oq_01_isLittleO`. The iff `erdos_101_oq_01_rate_form_iff_isLittleO`
certifies their equivalence. Downstream consumers can cite OQ-01 in
Mathlib idiom directly.

### S13 next-action candidates

1. **Mechanic iter-2** (if S12 PR's Docker build fails): apply fallback
   per session-file §4.
2. **True-sup `maxFourPointLines`**: replace surrogate `n*(n-1)/12`
   with `Finset.sup'` over no-five-collinear point sets of fixed size
   (~15 LOC).
3. **Cauchy–Schwarz refinement** of `fourCollinearThrough_bound`
   $\leq (n-1)/3$ for a $1 - o(1)$ leading constant on the $n^2/12$
   elementary bound.
4. **Witness extraction at small `n`** via `decide`/`native_decide`
   on small finite combinatorics; supplies certified gallery examples.
5. **Downstream integration**: search proofs/ for places where
   `Asymptotics.IsLittleO`-style consumption would benefit from the
   new bridge.
