# Knowledge Base: laws-of-large-numbers-oq-01-oq-02-oq-01

**Title:** Marcinkiewicz–Zygmund SLLN in Lean 4
**Chain:** `laws-of-large-numbers` → `-oq-01` (heavy-tailed LLN, 1 axiom) →
`-oq-01-oq-02` (SLLN rate of convergence, 3 axioms) → this leaf.

---

## S1 (researcher-14, 2026-07-02) — OBSERVE/ORIENT survey (text-only)

Goal of this session: pin down the *exact* formal target, map what Mathlib
already provides, decompose the classical proof, and give an honest
tractability verdict. **No Lean file was produced** — this is a survey, and
the honest classification is **SURVEY → multi-session BUILD** (see verdict).

### 1. The formal target

The **Marcinkiewicz–Zygmund strong law of large numbers**. Let
`X, X₀, X₁, …` be i.i.d. real random variables and fix `1 ≤ p < 2`.

- If `1 ≤ p < 2`: `𝔼|X|^p < ∞`  ⟹
  `(∑_{i<n} (Xᵢ − 𝔼X)) / n^{1/p} → 0`  almost surely.
- (`0 < p < 1` variant: `𝔼|X|^p < ∞` ⟹ `(∑_{i<n} Xᵢ)/n^{1/p} → 0` a.s.,
  *no centering*. Out of scope for this leaf, which sits under the "rate of
  convergence" parent and so is the `1 ≤ p < 2` centered regime.)

At `p = 1` this is exactly Kolmogorov/Etemadi SLLN (normalisation `n^{1} = n`).
The content of MZ is the **faster normalisation `n^{1/p}` for `p > 1`**: a
`p`-th moment buys you convergence of the centred sum divided by `n^{1/p}`,
which is `o(n)` — a genuine *rate* strengthening of the plain SLLN. The
converse also holds (a.s. convergence of `Sₙ/n^{1/p}` ⟹ `𝔼|X|^p < ∞` and,
for `p ≥ 1`, `𝔼X = 0`), but the forward direction is the natural leaf target.

Candidate Lean statement (real-valued; `μ` a probability measure on `Ω`):

```lean
theorem marcinkiewicz_zygmund
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p < 2)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))       -- or iIndepFun
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hmom : MemLp (X 0) (ENNReal.ofReal p) μ) :   -- 𝔼|X₀|^p < ∞
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ ↦ (n : ℝ)^(-(1/p)) * (∑ i ∈ Finset.range n, (X i ω - μ[X 0])))
        atTop (𝓝 0) := by
  sorry
```

(`n^(-(1/p))` is the reciprocal of `n^{1/p}`; keep it as an `rpow` to avoid a
`ℕ`-power/`ℝ`-power mismatch.)

### 2. What Mathlib already provides — exact API map

File `Mathlib/Probability/StrongLaw.lean` (verified at the repo's pinned rev):

| Lemma | Statement | Gives us |
|-------|-----------|----------|
| `strong_law_ae` (L.790) | Etemadi SLLN: `Integrable (X 0)`, pairwise-indep, identically-distributed ⟹ `n⁻¹ • ∑ Xᵢ → 𝔼[X 0]` a.s., **Banach-space valued** | The **`p = 1` base case** exactly. |
| `strong_law_Lp` (L.834) | `MemLp (X 0) p`, `1 ≤ p ≠ ∞`, indep, ident ⟹ `n⁻¹ • ∑ Xᵢ → 𝔼[X 0]` **in `Lᵖ`** | Lᵖ *convergence* of the `n⁻¹` average — **not** the `n^{1/p}` a.s. rate. |
| `strong_law_ae_real` (L.600) | real-valued specialisation used to bootstrap the vector case | Truncation/`aux` scaffolding is real-valued and reusable in spirit. |
| `strong_law_aux1…aux7` (L.380–579) | the truncation + Borel–Cantelli internals of Etemadi's proof | **Directly analogous** to what MZ needs, but hard-coded to `n⁻¹`. |

**Gap:** Mathlib has the `n⁻¹` (i.e. `p = 1`) a.s. law and the `Lᵖ` law, but
**no `n^{1/p}` almost-sure normalisation** and **no MZ statement**. Searched
`Marcinkiewicz` across `Mathlib/Probability/*` → 0 hits.

Supporting pieces that *do* exist and are needed:
- `MeasureTheory.MemLp` / `eLpNorm`, `MemLp.integrable` (`p ≥ 1 ⟹ L¹`).
- `ProbabilityTheory.IdentDistrib`, `IndepFun`, `iIndepFun`.
- Kolmogorov-type tools: `MeasureTheory.ae_tendsto_of_…`, Borel–Cantelli
  (`MeasureTheory.measure_limsup_eq_zero`, `ProbabilityTheory.…`), and
  `Finset.sum` rpow/telescoping utilities. **Kolmogorov's three-series
  theorem is NOT in Mathlib** (checked: no `three_series`/`kolmogorov_…`
  convergence lemma) — this is the single biggest missing dependency.

### 3. Classical proof decomposition (Marcinkiewicz–Zygmund 1937)

The standard forward-direction argument for `1 ≤ p < 2`, WLOG `𝔼X = 0`:

1. **Truncation.** `Yᵢ := Xᵢ · 𝟙{|Xᵢ| ≤ i^{1/p}}`. Show `∑ P(Xᵢ ≠ Yᵢ) < ∞`
   from `𝔼|X|^p < ∞` (⟹ by Borel–Cantelli, `Xᵢ = Yᵢ` eventually a.s., so it
   suffices to prove the law for the `Yᵢ`).
2. **Centering the truncation.** Control `∑ (𝔼Yᵢ)/n^{1/p} → 0` using
   `𝔼X = 0` and a moment/`rpow` estimate on the truncated means.
3. **Variance sum converges.** `∑ Var(Yᵢ)/i^{2/p} < ∞` (uses `p < 2`, so
   `2/p > 1`; this is where the `p < 2` hypothesis is *essential*).
4. **Kolmogorov's convergence criterion / three-series** ⟹
   `∑ (Yᵢ − 𝔼Yᵢ)/i^{1/p}` converges a.s.
5. **Kronecker's lemma** ⟹ `n^{-1/p} ∑_{i<n}(Yᵢ − 𝔼Yᵢ) → 0` a.s.
6. Combine 1+2+5.

**Kronecker's lemma** (`aₙ ↑ ∞`, `∑ xₙ/aₙ` converges ⟹ `a_n^{-1} ∑_{i≤n} xᵢ → 0`)
is a clean analysis lemma and a good **standalone sub-target** — check
Mathlib; if absent it is ~40–60 LOC and independently useful.

### 4. Tractability verdict — **SURVEY → multi-session BUILD (not one-session)**

- The proof needs **Kolmogorov's three-series / convergence theorem** and
  **Kronecker's lemma**, neither confirmed in Mathlib. Building the
  three-series theorem alone is a substantial (>300 LOC) probability
  development (second Borel–Cantelli, Kolmogorov maximal inequality, a.s.
  convergence of `L²`-bounded independent series).
- The Etemadi `strong_law_aux*` scaffolding is `n⁻¹`-specific and does **not**
  transfer verbatim to `n^{1/p}`; the truncation level changes from `i` to
  `i^{1/p}` and the variance-sum step is genuinely different.
- **Do NOT axiomatise casually.** The parent chain is already axiom-heavy
  (`-oq-01`: 1 axiom, `-oq-01-oq-02`: 3 axioms). Per the Axiom Integrity /
  Elimination policy, the right next move is to **build reusable
  infrastructure** (Kronecker + Kolmogorov convergence) rather than add a
  fourth axiomatised leaf. A Kronecker-lemma PR is the highest-value,
  genuinely-tractable increment.

### 5. Recommended next actions (for a future session)

1. **S2 (tractable, ~1 session):** formalise **Kronecker's lemma** for real
   sequences as a standalone gallery-adjacent lemma. Independently useful,
   0-axiom, unblocks step 5.
2. **S3 (multi-session):** build the a.s.-convergence-of-independent-`L²`-series
   criterion (Kolmogorov) — the true bottleneck.
3. **S4:** assemble truncation (steps 1–3) and conclude MZ. Only after S2+S3.

### Race / duplication check

`gh pr list --search "marcinkiewicz"` / branch scan: no open PR or branch on
this slug at survey time. Sibling `-oq-01-oq-02` is `COMPLETE` (axiomatised).
Low duplication risk for a Kronecker-lemma S2.

### Bibliography

- Marcinkiewicz & Zygmund (1937), *Sur les fonctions indépendantes*, Fund. Math.
- Chow & Teicher, *Probability Theory* (3e), §5.2 (MZ SLLN, three-series).
- Durrett, *Probability: Theory and Examples* (5e), Thm 2.5.8 (MZ) + Kronecker.
- Etemadi (1981) — pairwise-independent SLLN, the `p=1` base (Mathlib's
  `strong_law_ae`).

---

## S2 (researcher-16, 2026-07-03) — BUILD: Kronecker's lemma SHIPPED (verified)

Kronecker's lemma (step 5 of the MZ decomposition) and its Toeplitz/Silverman
core were formalised, **0-sorry / 0-axiom**, in
`proofs/Proofs/LawsOfLargeNumbersOQ01OQ02OQ01.lean`:

- `LawsOfLargeNumbers.MZ.tendsto_weighted_average_zero` (L47) — Toeplitz null
  step: nonnegative weights `c i` with partial sums dominated by a normaliser
  `A n → ∞`, applied to a null sequence `e i → 0`, give
  `(∑_{i<n} c i · e i) / A n → 0`. Reusable core (ε/2 head–tail split).
- `LawsOfLargeNumbers.MZ.kronecker_lemma` (L122) — `a` positive, monotone,
  `a n → ∞`, `∑ x i / a i` converges ⟹ `(∑_{i<n} x i) / a n → 0`. Via Abel
  summation (`Finset.sum_range_by_parts`) reduced to the weighted-average step;
  index-shifted to `m+1` to avoid the `n−1` that `sum_range_by_parts` produces.

This closed the **first** of the two blocking Mathlib gaps from S1.

> **Process note (2026-07-03):** the S2 session updated `.json` but left
> `state.md` / `knowledge.md` saying "S2 next", which caused a *duplicate*
> Kronecker re-derivation (an independent `field_simp` + `IsLittleO.sum_range`
> proof — also correct, but redundant). It was discarded before merge. Lesson:
> update `state.md` **and** `knowledge.md` in the same commit that ships Lean.

---

## S3 (researcher-16, 2026-07-03) — ORIENT: Kolmogorov criterion is ASSEMBLY, not a foundation gap

The S1 survey called the second gap — a.s. convergence of an independent
mean-zero `L²` series (Kolmogorov's convergence / three-series criterion) — the
"real bottleneck, >300 LOC". That estimate predates checking Mathlib's
**martingale-convergence** machinery. Re-audit of the pinned Mathlib (v4.26.0):
the a.s.-convergence *engine* and **every** glue lemma already exist. What
remains is assembly, not new foundations.

### Target statement (S3)

`X : ℕ → Ω → ℝ` independent (`iIndepFun`), each `MemLp (X i) 2 μ`,
`μ[X i] = 0`, and `∑ i, Var[X i] < ∞`  ⟹  the partial sums
`S n = ∑ i ∈ range n, X i` converge a.s.:
`∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => S n ω) atTop (𝓝 c)`.

### Concrete reduction path — named Mathlib lemmas (all present)

1. **Natural filtration.** `MeasureTheory.Filtration.natural X hX_meas`
   (`Mathlib/Probability/Process/Filtration.lean:255`) — smallest filtration
   making `X` adapted; then `S` is adapted.
2. **Martingale property.** Show `μ[S (n+1) | ℱ n] = S n` a.e. Reduces to
   `μ[X n | ℱ n] = μ[X n] = 0` a.e. because `X n` is independent of the past
   σ-algebra `ℱ n`. The lemma is
   `MeasureTheory.condExp_indep_eq`
   (`Mathlib/Probability/ConditionalExpectation.lean:42`): independent σ-algebras
   ⟹ `μ[f | m₂] = μ[f]`. **Template already in Mathlib:**
   `Mathlib/Probability/BorelCantelli.lean:54` uses exactly this to build a
   martingale from a sequence — follow its filtration/`condExp_indep_eq` pattern.
3. **Uniform `L¹` bound.** `Var[S n] = ∑ i ∈ range n, Var[X i] ≤ ∑ i, Var[X i]`
   by orthogonality of independent mean-zero increments:
   `ProbabilityTheory.IndepFun.variance_sum`
   (`Mathlib/Probability/Moments/Variance.lean:403`). Then on a probability
   measure `eLpNorm (S n) 1 μ ≤ eLpNorm (S n) 2 μ = sqrt (Var[S n]) ≤
   sqrt (∑ i, Var[X i]) =: R` (Lyapunov / `eLpNorm` monotonicity in `p`;
   `MemLp`/`eLpNorm_le_eLpNorm...` on finite measure). Mean-zero ⟹ the `L²`
   norm equals the standard deviation.
4. **Apply the engine.** A martingale is a submartingale, so
   `MeasureTheory.Submartingale.exists_ae_tendsto_of_bdd`
   (`Mathlib/Probability/Martingale/Convergence.lean:191`), with `hbdd n :
   eLpNorm (S n) 1 μ ≤ R`, yields exactly the a.s. limit
   `∀ᵐ ω, ∃ c, Tendsto (S · ω) (𝓝 c)`.

### Honest revised verdict

- **Not a >300 LOC foundational build.** Every hard theorem (upcrossing
  inequality, a.e. martingale convergence, variance orthogonality, condexp
  under independence) is already in Mathlib. S3 is **glue**: build the
  filtration, discharge the martingale identity via `condExp_indep_eq`, chain
  the `eLpNorm` monotonicity for the `L¹` bound, invoke the engine.
- **Estimate: 1–2 sessions.** The main friction is bookkeeping — measurability
  side-goals, `SigmaFinite (μ.trim …)` instances for `condExp_indep_eq`, and
  the `eLpNorm 1 ≤ eLpNorm 2` step on a probability measure.
- This does **not** need any new axiom; keep the leaf on the 0-axiom track.

### S3 bibliography / API cross-refs

- `Mathlib/Probability/Martingale/Convergence.lean` — `exists_ae_tendsto_of_bdd`,
  `ae_tendsto_limitProcess` (the a.e. martingale convergence theorem).
- `Mathlib/Probability/ConditionalExpectation.lean` — `condExp_indep_eq`.
- `Mathlib/Probability/Moments/Variance.lean` — `IndepFun.variance_add/_sum`.
- `Mathlib/Probability/BorelCantelli.lean` — worked example of building a
  martingale from a sequence via `condExp_indep_eq` (imitate its structure).
- Durrett, *PTE* (5e), Thm 2.5.6 (Kolmogorov's convergence theorem via the
  martingale route) — matches this reduction.

---

## S4 (researcher-14, 2026-07-03) — BUILD: Kolmogorov martingale assembly SHIPPED (verified)

The S3 assembly is done. Two new theorems in
`proofs/Proofs/LawsOfLargeNumbersOQ01OQ02OQ01.lean`, **0-sorry / 0-axiom**
(`#print axioms` = propext/Classical.choice/Quot.sound only — no sorryAx, no
`Lean.ofReduceBool`). Verified via Docker build (7743 jobs, 0 errors).

- `martingale_sum_of_indep_mean_zero` (L338) — for `X : ℕ → Ω → ℝ` independent
  (`iIndepFun X μ`), integrable, mean-zero on a probability space, the shifted
  partial sums `f n = ∑ i ∈ range (n+1), X i` are a `Martingale` wrt
  `Filtration.natural X hmeas`. Proof: adaptedness by
  `Finset.stronglyMeasurable_sum` over `Filtration.adapted_natural` + filtration
  monotonicity; the increment condition `μ[f(n+1) − f n | ℱ n] =ᵐ 0` via
  `martingale_of_condExp_sub_eq_zero_nat`, where the increment reduces to
  `X (n+1)` (`Finset.sum_range_succ`) and
  `iIndepFun.condExp_natural_ae_eq_of_lt hmeas hindep (Nat.lt_succ_self n)` gives
  `μ[X(n+1) | ℱ n] =ᵐ fun _ => μ[X(n+1)] = 0`.
- `ae_tendsto_sum_of_indep_of_eLpNorm_bdd` (L382) — same hyps + a uniform L¹
  bound `hbdd : ∀ n, eLpNorm (∑_{i≤n} X i) 1 μ ≤ (R : ℝ≥0∞)` ⟹
  `∀ᵐ ω, ∃ c, Tendsto (∑_{i<n} X i ω) atTop (𝓝 c)`. Proof: `.submartingale` then
  `Submartingale.exists_ae_tendsto_of_bdd`, then `Finset.sum_apply` +
  `(tendsto_add_atTop_iff_nat 1).mp` to shift `∑_{i≤n} → ∑_{i<n}`.

### Gotchas hit (for the next session)

- **Use the SHIFTED sum** `f n = ∑ i ∈ range (n+1), X i` (i.e. `∑_{i≤n}`), NOT
  `∑_{i<n}`. With `ℱ = natural X` (`ℱ n = σ(X_0..X_n)`), the increment must be
  `X (n+1)`, which is *independent of* `ℱ n`. With `∑_{i<n}` the increment `X n`
  is `ℱ n`-measurable and the martingale identity FAILS.
  `iIndepFun.condExp_natural_ae_eq_of_lt` needs `i < j` (j strictly future).
- Engine's bound variable is `R : ℝ≥0` (NNReal), coerced to `ℝ≥0∞` in the
  hypothesis — state `hbdd` with `(R : ℝ≥0∞)`, not `R : ℝ≥0∞`.
- Notation scopes: need `open scoped ENNReal NNReal` for `ℝ≥0∞` / `ℝ≥0`, and
  `open MeasureTheory ProbabilityTheory` for `Martingale`/`condExp`/`iIndepFun`.

### Remaining (S4a / S4b) — see state.md

- **S4a:** discharge `hbdd` from `∑ Var(X_i) < ∞` (probability space:
  `eLpNorm S_n 1 ≤ eLpNorm S_n 2 = sqrt(Var S_n) = sqrt(∑ Var)`). Named lemmas:
  `IndepFun.variance_sum` (Variance.lean L275), `eLpNorm_le_eLpNorm_of_exponent_le`
  (CompareExp.lean L98, needs `IsProbabilityMeasure`), and the
  `evariance`↔`eLpNorm 2` bridge under mean-zero (`evariance_eq_lintegral_ofReal`).
  Only fiddly part is ENNReal/rpow bookkeeping. Yields standalone Kolmogorov.
- **S4b:** truncation + moment estimates (M–Z-specific), then final assembly with
  `ae_tendsto_kronecker_average_zero`.

## Session 2026-07-03 (researcher-4) — S4a: Kolmogorov convergence from a variance-sum bound (DEEP DIVE, PROGRESS)

**Mode**: REVISIT (S4a, the flagged "single cleanest remaining increment"). **Outcome**:
3 new verified theorems, build ✔ (7743 jobs), 0-axiom (`#print axioms` =
propext/Classical.choice/Quot.sound on both the main theorem and the bridge lemma).

Discharged the deterministic `hbdd` L¹ hypothesis of
`ae_tendsto_sum_of_indep_of_eLpNorm_bdd` from a variance-sum bound. Three theorems added
to `Proofs/LawsOfLargeNumbersOQ01OQ02OQ01.lean` (§ Kolmogorov):

1. **`eLpNorm_two_sq_eq_evariance`** `(h0 : μ[X] = 0) : eLpNorm X 2 μ ^ 2 = evariance X μ`.
   The mean-zero bridge — **Mathlib has NO `eLpNorm`↔`evariance` lemma** (confirmed by
   repo-wide grep), this supplies the centered case. Proof: unfold `eLpNorm` via
   `eLpNorm_eq_lintegral_rpow_enorm` to `(∫⁻‖X‖ₑ²)^{1/2}`; unfold `evariance`, kill the
   centering with `simp [h0, sub_zero]`; reconcile the outer `(·)^{1/2}` squared back to
   the lintegral via `← ENNReal.rpow_natCast _ 2`, `← ENNReal.rpow_mul`, `(1/2)*2=1`,
   `rpow_one`; then `simp_rw [ENNReal.rpow_two]` to align the integrand's `^(2:ℝ)` (rpow)
   with `evariance`'s `^2` (nat pow).
2. **`eLpNorm_two_partialSum_le`** — uniform L² bound `‖Sₙ‖₂ ≤ ofReal(√V)` from
   `∑_{i≤n} Var ≤ V`. `‖Sₙ‖₂² = eVar[Sₙ] = ofReal(Var Sₙ) = ofReal(∑Var) ≤ ofReal V`
   (bridge + `ofReal_variance` + `IndepFun.variance_sum` orthogonality), then √ by the
   monotone ℝ≥0∞-power `ENNReal.rpow_le_rpow · (0≤1/2)`.
3. **`ae_tendsto_sum_of_indep_of_variance_bdd`** — Kolmogorov's a.s.-convergence criterion
   in variance-sum form: `‖·‖₁ ≤ ‖·‖₂` (`eLpNorm_le_eLpNorm_of_exponent_le`, needs
   `IsProbabilityMeasure` + `AEStronglyMeasurable`) chained with (2).

**Reusable Lean gotchas (Mathlib v4.26):**
- `eLpNorm_le_eLpNorm_of_exponent_le (hpq)(hf : AEStronglyMeasurable f μ)` — DOES need the
  measurability arg (not just `IsProbabilityMeasure`).
- Mean of a Finset-sum-of-functions: `μ[∑ i, X i] = ∑ μ[X i]` needs
  `simp_rw [Finset.sum_apply]` BEFORE `integral_finset_sum` (the latter's LHS is
  `∫ ∑ i, f i a`, not `∫ (∑ i, f i) a` — the plain `rw` fails on the unapplied sum).
- `(ENNReal.ofReal V)^{1/2} = ofReal(√V)`: `rw [Real.sqrt_eq_rpow,
  ENNReal.ofReal_rpow_of_nonneg hV0 (by norm_num)]` (forward), NOT a single `← rw` on the
  goal — the `←` direction fails to find the `ofReal(V^_)` pattern.
- `ENNReal.ofReal x = ↑x.toNNReal` by `rfl`, so `R := (√V).toNNReal` coerces to
  `ofReal(√V)` definitionally.
- `V ≥ 0` comes free from `hV 0`: `variance_nonneg (X 0) μ ≤ ∑_{i<1} Var = Var(X 0) ≤ V`.

**Honest status.** S4a is the standalone Kolmogorov convergence theorem — genuine, complete,
verified infrastructure, not scaffolding. It does not yet prove Marcinkiewicz–Zygmund: the
remaining **S4b** truncation/moment layer (Borel–Cantelli on `{X_i≠Y_i}`, `∑ Var(Y_i)/i^{2/p}<∞`
via `p<2`) then feeds S4a into `ae_tendsto_kronecker_average_zero`. Worked in locked
`/private/tmp/wt-r4-lln`, committed before building (worktree-deletion hazard did not recur).

## S4b step-2 (researcher-14, 2026-07-03) — BUILD: discrete layer-cake tail-sum SHIPPED (verified)

The Borel–Cantelli *input* for the MZ truncation is the summable tail
`∑ᵢ P(|Xᵢ| > i^{1/p}) < ∞`. For identically distributed `Xᵢ` this is a deterministic
measure-theoretic fact about `Z = |X₀|ᵖ ≥ 0`: the tail sum `∑ₙ μ{Z ≥ n+1}` is dominated
by the first moment. Mathlib has the *continuous* layer cake
(`lintegral_eq_lintegral_meas_le`) but **no discrete companion** (confirmed by repo-wide
grep). Three theorems added to `Proofs/LawsOfLargeNumbersOQ01OQ02OQ01.lean` (§ TailSum),
**0-sorry / 0-axiom** (`#print axioms` = propext/Classical.choice/Quot.sound on all three
— no sorryAx, no `Lean.ofReduceBool`). Verified via `LAKE_UNSAFE=1 lake env lean` against
the pinned prebuilt Mathlib oleans (v4.26.0): 0 errors.

1. **`tsum_indicator_add_one_le (z : ℝ) (hz : 0 ≤ z)`** — pure ENNReal helper:
   `∑' n, (if (n:ℝ)+1 ≤ z then 1 else 0) ≤ ENNReal.ofReal z`. The tail count equals
   `⌊z⌋₊`: the summand is `1` iff `n < ⌊z⌋₊` (via `Nat.le_floor_iff hz` + `Nat.add_one_le_iff`
   after `(n:ℝ)+1 = ((n+1:ℕ):ℝ)`), then `tsum_eq_sum` over `Finset.range ⌊z⌋₊`; finally
   `⌊z⌋₊ ≤ z` by `Nat.floor_le`.
2. **`tsum_measure_add_one_le_lintegral {Z} (hZmeas : Measurable Z) (hZnn : 0 ≤ Z)`** —
   `∑ₙ μ{x | (n:ℝ)+1 ≤ Z x} ≤ ∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ`. Proof: each `μ Aₙ =
   ∫⁻ 𝟙_{Aₙ}` (`lintegral_indicator_one`, `Aₙ` measurable by `measurableSet_le`), swap
   sum/integral (`lintegral_tsum`), pointwise bound via (1).
3. **`tsum_measure_add_one_ne_top {Z} (… ) (hZint : ∫⁻ ofReal Z ≠ ∞)`** — finiteness
   corollary `∑ₙ μ{Z ≥ n+1} ≠ ∞`, the exact hypothesis of first Borel–Cantelli
   (`measure_limsup_eq_zero`).

### Reusable Lean gotchas (Mathlib v4.26)

- **`rw [lintegral_tsum h]` FAILS to unify** when the integrand is `s.indicator 1` (the
  `1 : Ω → ℝ≥0∞` constant-one function): the higher-order matcher can't recover `f i a`
  from `(s.indicator 1) a`. **Fix:** don't `rw`; use it as a `calc` step
  `_ = ∫⁻ … := (lintegral_tsum h).symm` — the *expected type* of the calc step pins `f`,
  so elaboration succeeds. (General lesson: for HO-unification-hostile lemmas, drive with
  the expected type via `calc`/`exact`, not `rw`.)
- `measurable_const.indicator (hs : MeasurableSet s) : Measurable (s.indicator (fun _ => c))`
  unifies `c := 1` against `s.indicator 1` (Pi `1 = fun _ => 1` defeq). `.aemeasurable`
  gives the `lintegral_tsum` hypothesis.
- `lintegral_indicator_one (hs : MeasurableSet s) : ∫⁻ a, s.indicator 1 a ∂μ = μ s`.
- `tsum_eq_sum (s := Finset.range N) (fun n hn => …) : ∑' = ∑ over range` — supply the
  "zero outside `s`" proof; `simpa using hn` turns `n ∉ range N` into `¬ n < N` for `if_neg`.
- `ENNReal.ofReal_natCast (n) : ENNReal.ofReal ↑n = ↑n` — use `← ` to turn `(⌊z⌋₊:ℝ≥0∞)`
  into `ENNReal.ofReal ↑⌊z⌋₊` before `ENNReal.ofReal_le_ofReal (Nat.floor_le hz)`.
- Avoid shadowing: write the super-level set as `{x | (n:ℝ)+1 ≤ Z x}` (not `{ω | …}`) so
  the set-builder variable doesn't collide with the `∫⁻ ω` integration variable.

### Honest status

S4b step-2 is a genuine, complete, verified brick — the discrete layer-cake tail-sum and
its Borel–Cantelli-feeding corollary — reusable well beyond MZ. It does **not** yet prove
Marcinkiewicz–Zygmund: remaining are S4b step-1 (i.i.d. reduction to apply this to
`Z=|X₀|ᵖ` + `measure_limsup_eq_zero`), step-3 (centered-truncation control), step-4
(`∑ Var(Yᵢ)/i^{2/p}<∞`, uses `p<2`), then assembly with S4a + S2 Kronecker lift. Worked in
a locked `/private/tmp/r14-session-*` worktree off `origin/main`, committed before verifying
(the worktree-deletion hazard recurred at session start — designated `.loom/worktrees/researcher-14`
was gone again; the locked /tmp worktree avoids the clobber trap).

---

## S4b step-1 (researcher-14, 2026-07-03) — BUILD: i.i.d. Borel–Cantelli truncation reduction SHIPPED (verified)

**Mode**: FRESH (RICH knowledge, depth-first) · **Outcome**: progress (0-axiom brick shipped)

### What I did

Completed **S4b step-1**, connecting the step-2 discrete-layer-cake tail bound to the
actual Marcinkiewicz–Zygmund truncation event. Three theorems added to
`proofs/Proofs/LawsOfLargeNumbersOQ01OQ02OQ01.lean` (§ TruncationReduction), all
**0-sorry / 0-axiom** (`#print axioms` = `propext`/`Classical.choice`/`Quot.sound` on
all three — no `sorryAx`, no `Lean.ofReduceBool`). Verified via `LAKE_UNSAFE=1 lake env
lean` against the pinned prebuilt Mathlib v4.26.0 oleans: 0 errors, 0 warnings.

1. **`rpow_inv_lt_iff_lt_rpow {p} (hp:0<p) {a b} (ha:0≤a) (hb:0≤b) : a^(1/p) < b ↔ a < b^p`**
   — the elementary threshold reindex. Proof: `Real.rpow_lt_rpow_iff` (strict mono of
   `·^p` on nonneg, `0<p`) rewritten by `Real.rpow_inv_rpow ha hp.ne'`
   (`(a^p⁻¹)^p = a`); `one_div` bridges `1/p ↔ p⁻¹`.
2. **`tsum_measure_truncation_ne_top_of_identDistrib`** — for i.i.d. `Xᵢ` (each
   `IdentDistrib (Xᵢ) (X₀)`) with `𝔼|X₀|ᵖ < ∞` (finite `∫⁻ ofReal |X₀|ᵖ`), the truncation
   tail `∑ᵢ μ{i^{1/p} < |Xᵢ|} ≠ ∞`. Proof chain: (a) each tail measure `= μ{i < |X₀|ᵖ}` —
   `{ω | i^{1/p}<|Xᵢ ω|}` is `Xᵢ ⁻¹' {y | i^{1/p}<|y|}` (`rfl`), transfer by
   `IdentDistrib.measure_mem_eq` on that measurable set, reindex the `X₀` side pointwise
   by `rpow_inv_lt_iff_lt_rpow`; (b) peel `i=0` (`tsum_eq_zero_add'`, term `≤ 1` by
   `measure_ne_top`); (c) dominate the `i≥1` tail by `tsum_measure_add_one_ne_top`
   (step 2) with `Z=|X₀|ᵖ`, via `{(b+1:ℝ) < Z} ⊆ {(b:ℝ)+1 ≤ Z}` (`ENNReal.tsum_le_tsum` +
   `measure_mono` + `push_cast`/`linarith`).
3. **`ae_eventually_abs_le_rpow_of_identDistrib`** — feeds (2) into
   `MeasureTheory.ae_eventually_notMem` (first Borel–Cantelli) ⟹
   `∀ᵐ ω, ∀ᶠ i, |Xᵢ ω| ≤ i^{1/p}`. This is the truncation reduction: a.s. `Xᵢ = Yᵢ`
   eventually where `Yᵢ = Xᵢ·𝟙{|Xᵢ| ≤ i^{1/p}}`.

### Key finding / reusable gotcha (Mathlib v4.26)

- **`Summable.tsum_eq_zero_add` (dot form) is `whnf`-pathological** and must be avoided
  for the ENNReal tsum peel. `rw [Summable.tsum_eq_zero_add ENNReal.summable]` blows past
  **1 000 000 heartbeats at `whnf`** — and this reproduces *even on a fully abstract
  `g : ℕ → ℝ≥0∞`* (`example (g) : ∑' i, g i = g 0 + ∑' n, g (n+1) := ENNReal.summable.tsum_eq_zero_add`
  times out) and even when the split is stated as a fully-typed `have`. The fix is the
  **primed, non-dot idiom `rw [tsum_eq_zero_add' ENNReal.summable]`** — exactly how
  Mathlib's own `Topology/Instances/ENNReal/Lemmas.lean` peels ENNReal tsums. Compiles
  instantly. Bisected via stubbed-dependency scratch files (`ScratchMZ.lean`).

### Provenance note

Salvaged a prior interrupted researcher-14 draft (the section text was correct but never
compiled — the session died on the worktree-deletion hazard before verification). Its base
was a stale `origin/main` predating S4a/S5, so it was transplanted onto current
`origin/main` in a **locked** `/Users/rwalters/lg-wt/` worktree (the worktree-deletion
hazard recurred twice this session; `--lock` is mandatory).

### Files modified

- `proofs/Proofs/LawsOfLargeNumbersOQ01OQ02OQ01.lean` (+108 lines, § TruncationReduction)
- `research/problems/.../state.md`, `.../knowledge.md`, problem JSON knowledge

### Next steps

S4b step-3 (centered-truncation control `∑ᵢ 𝔼Yᵢ/n^{1/p} → 0`) and step-4
(`∑ᵢ Var(Yᵢ)/i^{2/p} < ∞`, uses `p<2`), then final assembly via S5
`ae_tendsto_average_zero_of_variance_weighted_bdd` on the centered truncations plus this
step's a.s. eventual `Xᵢ = Yᵢ`.

---

## S4b steps 3–4 kernels (written r14 2026-07-03, VERIFIED r8 2026-07-04) — BUILD: pointwise truncation-moment kernels SHIPPED

**Outcome: BUILD (verified).** Wrote the two **pointwise `rpow` inequalities** that are
the analytic hearts of the two remaining S4b estimates (centering and variance). Both are
pure real-analysis (no measure theory), elementary, reusable, 0-sorry / 0-`axiom`.
New section `§ TruncationMomentKernels` in `LawsOfLargeNumbersOQ01OQ02OQ01.lean`.

> **VERIFIED (researcher-8, 2026-07-04).** The disk-full blocker cleared (9.3 Gi free);
> `./proofs/scripts/docker-build.sh Proofs.LawsOfLargeNumbersOQ01OQ02OQ01` → **Built
> (7743 jobs, 54s, exit 0)**. Both kernels use only `Real.rpow` lemmas with no
> `decide`/`native_decide`/`sorry`/`axiom`, so 0-axiom by construction. The r14
> name/signature pre-checks against the pinned `v4.26.0` source all held.

### What shipped

- `abs_le_rpow_mul_rpow_of_tail` — **step-3 kernel (centering).**
  `1 ≤ p`, `0 < t`, `t < |x|` ⟹ `|x| ≤ t^{1-p} · |x|^p`.
  Mechanism: `|x| = |x|^p · |x|^{1-p}` (`Real.rpow_add`, exponent `p+(1-p)=1`), and
  the **sign of `1-p`** does the work — `1-p ≤ 0` with `0 < t ≤ |x|` gives the
  *antitone* rpow bound `|x|^{1-p} ≤ t^{1-p}` via `Real.rpow_le_rpow_of_nonpos`
  `(hx : 0<x) (hxy : x≤y) (hz : z≤0) : y^z ≤ x^z`.
- `sq_le_rpow_mul_rpow_of_trunc` — **step-4 kernel (variance).**
  `p < 2`, `0 < t`, `|x| ≤ t` ⟹ `x² ≤ t^{2-p} · |x|^p`.
  Mechanism: `x=0` case is RHS-nonnegativity; else `x² = |x|^2 = |x|^p · |x|^{2-p}`
  via `Real.rpow_add` + the cast chain `|x|^{(2:ℝ)} = |x|^{((2:ℕ):ℝ)} = |x|^{(2:ℕ)} = x²`
  (`Real.rpow_natCast`, `sq_abs`), then `0 ≤ 2-p` with `0 < |x| ≤ t` gives the
  *monotone* rpow bound `|x|^{2-p} ≤ t^{2-p}` via `Real.rpow_le_rpow`.

### Insights (propagate)

- **The `p`-regime hypotheses enter through one sign each.** `1 ≤ p` ⟺ `1-p ≤ 0`
  (tail factor `t^{1-p}` sub-linear, step-3); `p < 2` ⟺ `0 ≤ 2-p` (truncation factor
  `t^{2-p}` super-linear + `2/p > 1` for the variance-sum convergence, step-4). This is
  the *entire* role of `1 ≤ p < 2` at the pointwise level — everything else is `rpow`
  bookkeeping.
- **`rpow_add` split idiom.** To relate `|x|` (or `x²`) to `|x|^p·(threshold)^{exp}`,
  write the target power as `|x|^p · |x|^{k-p}` (`k=1` tail, `k=2` variance) via
  `← Real.rpow_add hxpos` with the exponent identity closed by `show … = k by ring`,
  then bound the *second* factor by the threshold using the appropriate signed-exponent
  monotonicity lemma. Reused verbatim in both kernels.
- **`x^(2:ℝ) = x^(2:ℕ)` cast chain** (recurs whenever a square meets rpow): 
  `rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]`. `sq_abs` turns
  `|x|^(2:ℕ)` into `x^(2:ℕ)` for free.
- These kernels are **pointwise only** — the surviving work is the *integral lift*:
  `integral_mono`/`abs_integral_le` against the kernel to reach `|𝔼Yᵢ| ≤ i^{(1-p)/p}𝔼|X|^p`
  (step-3) and `𝔼[Yᵢ²] ≤ i^{(2-p)/p}𝔼|X|^p` (step-4), plus the two sums.

### Recommended next: step-4 before step-3

Step-4's integral lift is more self-contained (just `integral_mono` on the indicator
`Yᵢ² = Xᵢ²·𝟙{|Xᵢ|≤i^{1/p}}` + a Mathlib `∑ i^{-2/p}` convergence lemma —
`Real.summable_one_div_nat_rpow` with `2/p > 1`), whereas step-3 additionally needs the
weight partial-sum asymptotic `∑_{i<n} i^{1/p-1} ~ p·n^{1/p} → ∞` for
`tendsto_weighted_average_zero`. Do step-4 first.

### Process / hazard

- **Worktree-deletion hazard recurred (3rd session running).** The unlocked worktree at
  `.loom/worktrees/researcher-14` was deleted mid-session by a concurrent cleanup, then a
  `/private/tmp` replacement was *also* deleted. Only **`--lock`ed** worktrees survive
  (all long-lived worktrees in `git worktree list` show `locked`). Mandatory pattern:
  `git worktree add --lock /Users/rwalters/lg-wt/<name> <branch>`.
- The stale `feature/researcher-14` branch is at an *old* main commit with **no** MZ file;
  the merged MZ work lives on `origin/main`. Always base new MZ work on `origin/main`.

### Files modified

- `proofs/Proofs/LawsOfLargeNumbersOQ01OQ02OQ01.lean` (+~90 lines, § TruncationMomentKernels)
- `research/problems/.../state.md`, `.../knowledge.md`, problem JSON knowledge

## Session 2026-07-03 (researcher-8) — S4b integral lifts: kernels → expectations (DEEP DIVE, PROGRESS)

**Mode**: REVISIT (RICH, score 29). **Outcome**: progress (DEEP DIVE) — new
`§ TruncationIntegralLifts` in `proofs/Proofs/LawsOfLargeNumbersOQ01OQ02OQ01.lean`
(2 theorems, 0 sorry, 0 axiom). **VERIFIED**: `docker-build.sh
Proofs.LawsOfLargeNumbersOQ01OQ02OQ01` → Built (7743 jobs, 42s, exit 0);
`#print axioms` on both = `[propext, Classical.choice, Quot.sound]` only — no
`sorryAx`, no `Lean.ofReduceBool`, no `decide`.

### What this session did
Lifted the two verified pointwise `rpow` kernels (`sq_le_rpow_mul_rpow_of_trunc`,
`abs_le_rpow_mul_rpow_of_tail`) from the previous session to the expectation level —
exactly the top-priority `nextSteps` items ("integral lift ... do first,
self-contained"):

- **`integral_trunc_sq_le`** (step 4, variance, `p < 2`):
  `∫ (𝟙{|X| ≤ t}·X)² ∂μ ≤ t^{2-p} · ∫ |X|^p ∂μ`.
- **`integral_tail_abs_le`** (step 3, centering, `1 ≤ p`):
  `∫ 𝟙{t < |X|}·|X| ∂μ ≤ t^{1-p} · ∫ |X|^p ∂μ`.

### Technique (reusable)
Both go through `MeasureTheory.integral_mono_of_nonneg`, whose key virtue is it
needs integrability **only of the dominating side** (`hint.const_mul _`, i.e.
`t^k · |X|^p` integrable from the `E|X|^p < ∞` hypothesis). The truncated integrand
on the LHS may itself be non-integrable when `μ` is infinite; `integral_mono_of_nonneg`
absorbs that by returning `0` for the undefined integral, still `≤` the finite bound.
Pointwise bound: `Set.indicator_apply` + `split_ifs`; the on-set branch is the kernel
verbatim, the off-set branch is `0 ≤ t^k·|X|^p` (`mul_nonneg (Real.rpow_nonneg …) …`).
Then `integral_const_mul` pulls the `t^k` constant out. **No probability,
independence, or finiteness of `μ` is used** — pure measure theory over arbitrary `μ`.

### Honest status
Genuine progress on the critical path, but NOT the full SLLN. What remains (updated
`nextSteps`): instantiate `t = i^{1/p}` in each lift, do the `rpow` exponent
arithmetic `(i^{1/p})^{2-p} = i^{(2-p)/p}`, and (step 4) sum against `i^{-2/p}` via
`Real.summable_one_div_nat_rpow` (converges iff `2/p > 1`, i.e. `p < 2`) to get the
finite variance sum; (step 3) feed the null sequence to `tendsto_weighted_average_zero`;
then S5 assembly through `ae_tendsto_average_zero_of_variance_weighted_bdd`.

### Files Modified
- proofs/Proofs/LawsOfLargeNumbersOQ01OQ02OQ01.lean (new § TruncationIntegralLifts)
- src/data/research/problems/laws-of-large-numbers-oq-01-oq-02-oq-01.json (leanFiles + knowledge)
- research/problems/laws-of-large-numbers-oq-01-oq-02-oq-01/knowledge.md (this entry)
