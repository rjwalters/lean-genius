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
