# Knowledge Base: lovasz-local-lemma-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

- The research-pool *title* "Finite Symmetric Thresholds" is a misnomer: that
  rational/combinatorial surrogate is already fully complete in
  `Proofs/LovaszLocalLemma.lean` (0 sorries, 0 axioms). The authoritative goal
  (problem.md) is the **measure-theoretic** probabilistic LLL, which is still
  open and research-grade.
- `lllThreshold d = dᵈ/(d+1)^{d+1}` is the exact maximum of `x(1-x)ᵈ` over
  `x ∈ [0,1)`, attained at `x = 1/(d+1)`. It equals `(1/(d+1))·(d/(d+1))ᵈ`
  (`lllThreshold_eq_product`).

---

## Insights

### Chain-rule scaffold + hypothesis-clean reduction (researcher-6, 2026-07-02→03) — NEW

- **The LLL induction skeleton is a pure, independence-free chain rule.**
  `Proofs/LovaszLocalLemmaOQ01ChainRule.lean` (gallery
  `lovasz-local-lemma-oq-01-chain-rule`, 0-axiom/0-sorry): for any measurable
  family over any `IsProbabilityMeasure`,
  `μ(⋂_{i<n} A i) = ∏_{k<n} μ[A k | ⋂_{j<k} A j]` (`cond_chain_avoidance`, by
  induction + `cond_mul_eq_inter` telescope). At the complements this is the
  survival-product form; `avoidance_pos_iff` reduces avoidance positivity to
  "every conditional survival probability ≠ 0".
- **The positive-history side condition is redundant.** The criterion
  `avoidance_pos_of_failure_cond_lt_one` originally assumed BOTH (a) every history
  `⋂_{j<k}(A j)ᶜ` has positive measure and (b) every failure conditional `< 1`.
  `hist_pos_of_failure_cond_lt_one` proves (a) follows from (b): induction on `n`,
  empty history = whole space (`μ=1`), each step multiplies by the positive
  survival conditional `1 − failure` (`mul_ne_zero` on
  `μ(hist ∩ (A n)ᶜ) = μ[(A n)ᶜ|hist]·μ(hist)`). Hence
  `avoidance_pos_of_failure_cond_lt_one'`: **failure conditionals `< 1` alone ⇒
  avoidance positive**. The LLL's sole obligation is now the per-event bound.
- **Reusable Lean gotcha.** `cond_mul_eq_inter h s μ : μ[s|hist]·μ hist = μ(hist∩s)`
  where `h : MeasurableSet hist`. To telescope the *complement* history you must
  pass `measurableSet_hist (fun i => (hA i).compl) n` (measurability of
  `⋂_{j<n}(A j)ᶜ`), NOT `measurableSet_hist hA n` (that's the un-complemented
  history and the rewrite pattern won't match).
- **`1 − c ≠ 0` for `c < 1` in ℝ≥0∞:** `rw [Ne, tsub_eq_zero_iff_le, not_le]`.
  `Finset.self_mem_range_succ n : n ∈ range (n+1)`;
  `Nat.lt_succ_of_lt` lifts `range n` membership into `range (n+1)`.

### Union-bound extreme (researcher-5, 2026-07-02) — NEW

- **The dependency-free (first-moment) avoidance bound is fully provable and
  elementary.** New file `Proofs/LovaszLocalLemmaOQ01UnionBound.lean` (0 sorry /
  0 axiom; axioms = propext/choice/Quot only), gallery entry
  `lovasz-local-lemma-oq-01-union-bound`: for an *arbitrary* Fintype-indexed
  measurable family over an `IsProbabilityMeasure` (no independence),
  `1 - ∑ i, μ (A i) ≤ μ (⋂ i, (A i)ᶜ)`, hence `0 < μ (⋂ i, (A i)ᶜ)` whenever
  `∑ μ (A i) < 1` (uniform version: `(Fintype.card ι) * p < 1`).
- **Route (no independence machinery).** `Set.compl_iUnion` (De Morgan) →
  `measure_iUnion_fintype_le` (finite subadditivity = the union bound) →
  `prob_compl_eq_one_sub` + `tsub_le_tsub_left` (1 − · is antitone in ℝ≥0∞) →
  `tsub_pos_iff_lt` for positivity at the subcritical threshold. Contrast with the
  base case, which needed generated σ-algebras + `iIndep.meas_iInter`.
- **`IsProbabilityMeasure` must be assumed here** (there is no independence
  hypothesis to derive it from, unlike the base case's `iIndepSet.isProbabilityMeasure`).
- **Framing payoff.** The union bound (`∑ μ < 1`, any dependency) and the
  independent product formula (`∏(1 − μ)`, full independence) are the two
  *computable extremes* bracketing the LLL. The open OQ-01 target is exactly the
  statement that a bounded local dependency degree `d` relaxes the crude global
  threshold `n·p < 1` to the `n`-independent local budget `e·p·(d+1) ≤ 1`.

### Measure-theoretic front (researcher-11, 2026-07-02) — NEW

- **The `d = 0` base case of the symmetric LLL is fully provable over a real
  probability space.** New file `Proofs/LovaszLocalLemmaOQ01.lean` (0 sorry /
  0 axiom): for a mutually independent measurable family `A : ι → Set Ω`
  (`iIndepSet A μ`, `ι` a `Fintype`) with `μ (A i) < 1` for all `i`,
  `0 < μ (⋂ i, (A i)ᶜ)`, and in fact `μ (⋂ i, (A i)ᶜ) = ∏ i, (1 - μ (A i))`.
  This is the independent regime that every LLL induction bottoms out to.
- **Complement-independence route.** Mathlib has *no* direct
  complement-independence lemma for `iIndepSet`. The working path:
  `iIndepSet_iff_iIndep` (event independence ⟺ independence of the σ-algebras
  `generateFrom {A i}`), then `iIndep.meas_iInter` applied to the complements
  `(A i)ᶜ`, which are measurable in `generateFrom {A i}` via
  `(measurableSet_generateFrom (mem_singleton _)).compl`. This is a clean,
  reusable pattern and a natural upstream Mathlib contribution
  (`iIndepSet.meas_iInter_compl`).
- **ENNReal bookkeeping.** `prob_compl_eq_one_sub` (needs `IsProbabilityMeasure`,
  obtained from `hind.isProbabilityMeasure`) rewrites `μ (A i)ᶜ = 1 - μ (A i)`;
  positivity of the ENNReal product via `zero_lt_iff` + `Finset.prod_ne_zero_iff`
  + `tsub_pos_iff_lt`. `IsProbabilityMeasure` need not be assumed — it follows
  from `iIndepSet`.

### Rational-surrogate front (earlier sessions)

- **Threshold monotonicity** `T(d+1) ≤ T(d)` (and the chain `T(d) ≤ T(c)` for
  `1 ≤ c ≤ d`) holds and is now formalized. It subsumes the universal bound
  `T(d) ≤ 1/4` because `T(1) = 1/4`.
- Monotonicity reduces (after cross-multiplication) to the elementary
  polynomial inequality `(a+1)^{2d+2} ≤ aᵈ(a+2)^{d+2}`, which yields to a single
  application of Bernoulli `(1-1/(a+1)²)ᵈ ≥ 1 - d/(a+1)²` plus the residual
  `(a²+a+1)(a+2)² ≥ (a+1)⁴` (difference `a³+3a²+4a+3`). No real analysis / `exp`
  needed — stays entirely in ℚ.
- Reusable Lean pattern: to clear an `xᵈ`-power inequality of the form
  `c ≤ (p/q)ᵈ`, rewrite with `div_pow` then `le_div_iff₀ (0 < qᵈ)`, multiply
  through by the residual denominator with `mul_le_mul_of_nonneg_right`, and
  hand the opaque `pᵈ`, `qᵈ` factors to `nlinarith` as atoms.
- `div_le_div_iff` is gone in this Mathlib; use **`div_le_div_iff₀`**
  `(hb : 0<b) (hd : 0<d) : a/b ≤ c/d ↔ a*d ≤ c*b`. Likewise `le_div_iff` →
  `le_div_iff₀`.

---

## Dead Ends

- Trying to prove `(a+1)^{2d+2} ≤ aᵈ(a+2)^{d+2}` term-by-term fails: the
  base-power factor `((a+1)²)ᵈ ≥ (a(a+2))ᵈ` points the *wrong* way; the
  `(a+2)²` vs `(a+1)²` factor is what compensates, so the Bernoulli/ratio
  argument is required rather than monotonicity of `xⁿ`.
- The measure-theoretic LLL is NOT a quick increment: Mathlib supplies
  `iIndepSet`, `ProbabilityMeasure`, `cond`, but no LLL, and a real proof spans
  multiple sessions. (Update 2026-07-02: the *independent* `d = 0` base case is
  now done and verified; only the bounded-dependency-degree inductive step
  remains open.)

### Chain-rule scaffold (researcher-6, 2026-07-02) — NEW

- **The conditional-probability chain rule is the independence-free skeleton of
  the LLL induction, and it is fully provable now.** New file
  `Proofs/LovaszLocalLemmaOQ01ChainRule.lean` (0 sorry / 0 axiom), gallery entry
  `lovasz-local-lemma-oq-01-chain-rule`: for an arbitrary measurable family
  `A : ℕ → Set Ω` over any `IsProbabilityMeasure`,
  `μ (⋂ i∈range n, A i) = ∏ k∈range n, μ[A k | ⋂ j∈range k, A j]`
  (`cond_chain_avoidance`). No independence, no dependency graph, no LLL bound.
- **Route (pure telescoping, no positivity side conditions).** Induction on `n`;
  the history at `n+1` splits off the newest event via `Finset.range_add_one` +
  `Finset.set_biInter_insert` + `Set.inter_comm`; the one-step multiplication
  rule `cond_mul_eq_inter : μ[t|s]·μ s = μ(s∩t)` (holds even when `μ s = 0`)
  extends the product, and `Finset.prod_range_succ` absorbs the new factor. Base
  case `μ univ = 1 = ∏∅`. Histories are measurable via
  `Finset.measurableSet_biInter`.
- **Survival/avoidance form + criterion.** Instantiating at the complements
  (`avoidance_eq_prod_survival_cond`) gives
  `μ(⋂ (A i)ᶜ) = ∏ k, μ[(A k)ᶜ | ⋂_{j<k}(A j)ᶜ]` — the honest measure-theoretic
  analogue of the rational surrogate `∏(1 − xᵢ)`. Then `avoidance_pos_iff`:
  `0 < μ(⋂ (A i)ᶜ) ↔ ∀ k, μ[(A k)ᶜ | history] ≠ 0` (finite ℝ≥0∞ product positive
  iff no factor vanishes, via `zero_lt_iff` + `Finset.prod_ne_zero_iff`). This is
  the exact reduction the LLL discharges.
- **Bridge to the standard LLL bound.** `survival_cond_eq_one_sub`: on a
  positive-measure history, `cond_isProbabilityMeasure` makes conditioning a prob
  measure, so `μ[(A k)ᶜ | history] = 1 − μ[A k | history]` (`prob_compl_eq_one_sub`).
  `avoidance_pos_of_failure_cond_lt_one`: history positive ∧ each failure
  conditional `< 1` ⇒ avoidance positive — the exact shape the LLL induction
  produces (symmetric regime: `μ[A k|history] ≤ 2p < 1` under `e·p·(d+1) ≤ 1`).
- **What remains open, sharpened.** The scaffold isolates precisely the missing
  ingredient: a strong-induction bound `μ[A i | ⋂_{j∈S} A_jᶜ] ≤ 2p` (equivalently
  each conditional survival `≥ 1 − 2p > 0`) for all `i, S`, under a
  measure-theoretic dependency (conditional independence of `A i` from
  non-neighbours). Plug that into `avoidance_pos_of_failure_cond_lt_one`.
- **Key API note.** `Finset.range_succ` is deprecated → use `Finset.range_add_one`.
  `cond_mul_eq_inter (hms) (t) (μ)` needs `[IsFiniteMeasure μ]` only (not
  probability), and holds unconditionally including the measure-zero case, which
  is why the chain rule needs NO positive-measure hypotheses.

### Quantitative lower bound (researcher-4, 2026-07-03) — NEW

- **The chain-rule reduction upgrades from positivity to the quantitative LLL
  bound with one order-theoretic step.** New file
  `Proofs/LovaszLocalLemmaOQ01Quantitative.lean` (0 sorry / 0 axiom), gallery entry
  `lovasz-local-lemma-oq-01-quantitative`: if `μ[A k | ⋂_{j<k}(A j)ᶜ] ≤ bₖ < 1`
  for all `k < n`, then `∏ₖ (1 − bₖ) ≤ μ(⋂ᵢ (A i)ᶜ)` (`avoidance_ge_prod_one_sub`).
  This is the honest measure-theoretic form of `μ(⋂ Aᵢᶜ) ≥ ∏(1 − xᵢ)`: the parent
  proof's rational surrogate `∏(1 − xᵢ)` is a *verified lower bound on the real
  avoidance probability*, not just an analogue.
- **Route (reuses the chain-rule scaffold, no new probability).** `rw
  [avoidance_eq_prod_survival_cond hA]` turns the RHS into `∏ₖ μ[(A k)ᶜ | history]`;
  `Finset.prod_le_prod'` (finite-product monotonicity in a canonically ordered
  comm monoid — works directly for ℝ≥0∞) reduces to the factorwise bound; on each
  history (positive via `hist_pos_of_failure_cond_lt_one`, since `bₖ < 1` ⇒
  `μ[A k|history] < 1`) `survival_cond_eq_one_sub` gives `survival = 1 − failure`,
  and `tsub_le_tsub_left (hfail k hk) 1` gives `1 − bₖ ≤ 1 − μ[A k|history]`.
- **Symmetric form.** `avoidance_ge_one_sub_pow`: constant `bₖ = p` collapses via
  `Finset.prod_const` + `Finset.card_range` to `(1 − p)ⁿ ≤ μ(⋂ (A i)ᶜ)` — the
  multiplicative counterpart of the union-bound extreme's additive `1 − np`.
- **Positivity subsumed.** `avoidance_pos_of_prod_one_sub_pos` re-derives the
  chain-rule entry's `avoidance_pos_of_failure_cond_lt_one'` from the strictly
  stronger quantitative bound (`∏(1 − bₖ) > 0` via `zero_lt_iff` +
  `Finset.prod_ne_zero_iff` + `tsub_eq_zero_iff_le`).
- **Key API note.** `Finset.prod_le_prod'` (the multiplicative/`OrderedCommMonoid`
  lemma) applies to ℝ≥0∞ products of the form `∏ f ≤ ∏ g` given `∀ i ∈ s, f i ≤ g i`
  — no nonnegativity side goals, unlike the ordered-semiring `Finset.prod_le_prod`.
  Membership propagation `m < k < n ⟹ m ∈ range n` needs `lt_trans` on the two
  `Finset.mem_range` facts.
- **What remains open (unchanged).** The per-event bounds `bₖ` are hypotheses;
  deriving them from a measure-theoretic dependency structure (`bₖ = 2p` under
  `e·p·(d+1) ≤ 1`) is the open target. This entry guarantees the quantitative LLL
  conclusion then follows with no further probability theory.

### Euler condition ⇒ tight threshold bridge (researcher-4, 2026-07-03) — NEW

- **The memorable symmetric condition `e·p·(d+1) ≤ 1` is implied by the tight
  threshold `p ≤ T(d) = dᵈ/(d+1)^{d+1}`, and now this is machine-checked.** New file
  `Proofs/LovaszLocalLemmaOQ01EulerThreshold.lean` (0 sorry / 0 axiom), gallery entry
  `lovasz-local-lemma-oq-01-euler-threshold`: `euler_condition_implies_lllThreshold`
  proves `e·p·(d+1) ≤ 1 → p ≤ (lllThreshold d : ℝ)` for `d ≥ 1` and any real `p`
  (no `0 ≤ p` needed — negative `p` is trivial since `T(d) > 0`). This links the
  parent proof's ℚ-valued tight threshold front to the Euler condition used
  throughout the OQ-01 measure-theoretic entries.
- **Core inequality: `(1 + 1/d)ᵈ ≤ e`** (`one_add_inv_pow_le_exp_one`). This is the
  single fact that puts the constant `e` into the LLL. Route:
  `Real.add_one_le_exp (1/d) : 1/d + 1 ≤ exp(1/d)` → `pow_le_pow_left₀ (by positivity)
  hstep d` raises to the dᵗʰ power → `← Real.exp_nat_mul` rewrites `exp(1/d)^d =
  exp(d·(1/d))`, and `mul_one_div; div_self (d ≠ 0)` gives `d·(1/d) = 1`, so RHS `= e`.
- **Chain to the threshold.** `succ_pow_le_exp_mul`: clear the denominator
  (`1+1/d = (d+1)/d`, `div_pow`, `div_le_iff₀`) to get `(d+1)ᵈ ≤ e·dᵈ`.
  `lllThreshold_cast`: `(lllThreshold d : ℝ) = dᵈ/(d+1)^{d+1}` via
  `simp only [lllThreshold, if_neg (d≠0)]; push_cast; ring`.
  `inv_exp_mul_le_lllThreshold`: `1/(e(d+1)) ≤ T(d)` — after
  `div_le_div_iff₀ .. ..; one_mul; pow_succ` the goal is `(d+1)ᵈ·(d+1) ≤ dᵈ·(e·(d+1))`,
  closed by `nlinarith [mul_le_mul_of_nonneg_right succ_pow_le_exp_mul (le_of_lt hd1)]`.
  Final bridge: `le_div_iff₀` turns `e·p·(d+1) ≤ 1` into `p ≤ 1/(e(d+1))`, then
  `le_trans` with the threshold bound.
- **Reusable Lean gotchas.** `lllThreshold` lives in namespace `ProbMethod.LovaszLocal`
  (NOT `LovaszLocalLemma`) — `open ProbMethod.LovaszLocal`. `pow_le_pow_left` is gone /
  unknown here; use `pow_le_pow_left₀ (ha : 0 ≤ a) (hab : a ≤ b) : ∀ n, aⁿ ≤ bⁿ`.
  `Real.exp_nat_mul : exp(↑n * x) = exp x ^ n` (so `← Real.exp_nat_mul` collapses
  `exp x ^ n`). `Real.add_one_le_exp x : x + 1 ≤ exp x`.
- **Honest scope.** This is elementary real analysis about *which hypothesis is
  stronger* (Euler form is a slightly conservative consequence of the tight
  threshold: `1/(e(d+1)) < T(d)` strictly), NOT a proof that either hypothesis forces
  positive avoidance. The measure-theoretic symmetric LLL induction (deriving the
  per-event conditional bounds `bₖ = 2p` under `e·p·(d+1) ≤ 1`, to feed
  `avoidance_ge_prod_one_sub` from the quantitative entry) remains the open target.
- **Shared-repo build note.** Fresh researcher worktrees have no `.lake`/`node_modules`;
  typecheck a single file via `cp` into MAIN `proofs/Proofs/` + `LAKE_UNSAFE=1 lake env
  lean <file>` against MAIN's cached mathlib oleans. Under heavy concurrent load (70+
  lean procs) expect transient `invalid header` / `configuration is invalid` errors —
  retry with backoff; a clean pass confirms.

### Dependency-graph induction step over ARBITRARY subset histories (researcher-4, 2026-07-03) — NEW

- **The whole prefix-history scaffold cannot reach the real LLL — and here is why + the fix.**
  Every prior OQ-01 measure-theoretic file (chain-rule, quantitative, union-bound,
  base case, and the concurrent Independence file) conditions on the *prefix* history
  `⋂_{j<k} Aⱼᶜ` because the chain rule needs a total order. But the Erdős–Lovász
  induction bounds `Pr[Aᵢ | ⋂_{j∈S} Aⱼᶜ]` for an **arbitrary** subset `S`, split into
  neighbours `S₁` and non-neighbours `S₂` of `Aᵢ` — unstructured sets, never prefixes.
  New file `Proofs/LovaszLocalLemmaOQ01DependencySplit.lean` (0 sorry / 0 axiom;
  axioms = propext/choice/Quot only), gallery entry
  `lovasz-local-lemma-oq-01-dependency-split`, supplies the two per-event moves of that
  step over arbitrary finite subset histories.
- **`cond_mono_num` — conditional prob is monotone in the numerator, and Mathlib has NO
  such lemma.** `E ⊆ F → μ[E | H] ≤ μ[F | H]` for any measurable `H`. Two `cond_apply`
  rewrites to `(μ H)⁻¹ · μ(H ∩ ·)`, then a single `gcongr` (via `measure_mono` +
  `Set.inter_subset_inter`). Natural upstream Mathlib contribution. Corollary
  `cond_inter_le : μ[E ∩ F | H] ≤ μ[E | H]` is the neighbour-factor drop.
- **`cond_failure_eq_measure_of_indep_subset` — the non-neighbour collapse over an
  ARBITRARY subset.** `IndepSet Aᵢ (⋂_{j∈S} Aⱼᶜ) μ` + positive history ⇒
  `μ[Aᵢ | ⋂_{j∈S} Aⱼᶜ] = μ(Aᵢ)`. Same proof as the concurrent Independence file's
  prefix version (`cond_apply`, `IndepSet.measure_inter_eq_mul`, `ENNReal.inv_mul_cancel`)
  but over a `Finset` `S` instead of `range n` — the version the dependency-graph
  induction genuinely needs. The only missing ingredient the prefix version lacked was
  general biInter measurability: `measurableSet_survival` (= `Finset.measurableSet_biInter`
  on the complements). This proves the prefix restriction was incidental to the scaffold,
  not intrinsic.
- **`cond_failure_le_measure_of_indep_num`** combines the two: drop the neighbour factor
  `T` from the numerator (`cond_inter_le`), then collapse the independent sub-history
  (`cond_failure_eq_measure_of_indep_subset`) ⇒
  `μ[Aᵢ ∩ (⋂_{j∈T} Aⱼᶜ) | ⋂_{j∈S₂} Aⱼᶜ] ≤ μ(Aᵢ)`. This is the LLL induction step's
  **numerator** bound.
- **Honest scope / still open.** The remaining hard piece is the recursive **denominator**
  lower bound `μ[⋂_{S₁} Aⱼᶜ | ⋂_{S₂} Aⱼᶜ] ≥ ∏_{j∈S₁}(1 − xⱼ)`, obtained by well-founded
  recursion on `|S₁|`, where the dependency-degree hypothesis enters. This file isolates
  exactly the unconditional / local-independence parts of the induction step so the open
  target is now sharply the denominator recursion.
- **Lean gotchas.** `IndepSet` and `IndepSet.measure_inter_eq_mul` live in
  `Mathlib.Probability.Independence.Basic` — ChainRule only imports
  `Mathlib.Probability.ConditionalProbability`, so add the Independence.Basic import or
  `IndepSet` gets auto-bound as an unknown implicit. `mul_le_mul_left'` is deprecated
  (→ use `gcongr`). `cond_apply (hms) (μ) (t) : μ[t|s] = (μ s)⁻¹ * μ (s ∩ t)` (three
  explicit args). Shared-repo build under 60+ concurrent lean procs: expect frequent
  exit-139 crashes + `invalid header` — retry; two clean `EXIT=0` empty-output passes
  confirm.
