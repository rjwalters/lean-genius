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
