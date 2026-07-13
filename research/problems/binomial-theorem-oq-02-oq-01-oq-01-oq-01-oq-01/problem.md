# Problem: Discharge `multinomialPMF_sum_eq_one` via parent + Mathlib API

## Statement

### Plain Language

The parent file
`proofs/Proofs/BinomialTheoremOQ02OQ01OQ01.lean` defines
`multinomialPMF s p n hp : PMF (Composition α s n)` and depends on
the sorry-laden normalization theorem

```lean
theorem multinomialPMF_sum_eq_one
    (s : Finset α) (p : α → ℝ≥0∞) (n : ℕ)
    (hp : ∑ i ∈ s, p i = 1) :
    ∑ k : Composition α s n, multinomialPMFVal s p n k = 1 := by sorry
```

The sibling child file
`proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ01.lean` already proves
the structural bridge

```lean
theorem CompositionFintype.sum_composition_eq_piAntidiag_sum
    {α} [DecidableEq α] {M} [AddCommMonoid M]
    (s : Finset α) (n : ℕ) (f : (α → ℕ) → M) :
    ∑ c : CompositionFintype.Composition α s n, f c.counts =
    ∑ k ∈ s.piAntidiag n, f k
```

and Mathlib v4.26.0 (pin `2df2f015`) provides the multinomial
theorem in any commutative semiring:

```lean
lemma Finset.sum_pow_eq_sum_piAntidiag {α R} [DecidableEq α] [CommSemiring R]
    (s : Finset α) (f : α → R) (n : ℕ) :
    (∑ i ∈ s, f i) ^ n =
      ∑ k ∈ s.piAntidiag n, Nat.multinomial s k * ∏ i ∈ s, f i ^ k i
```

Since `ℝ≥0∞` is a `CommSemiring`, the multinomial theorem instantiates
at `R = ℝ≥0∞`, and the sum-over-`Composition` is rewritable to a
sum-over-`piAntidiag` via the bridge.

**Open question (this slug).** Can `multinomialPMF_sum_eq_one` be
discharged purely by combining those two lemmas plus `hp`-driven
collapse `(∑ p i)^n = 1^n = 1`?

### Formal Statement

$$
\forall \alpha\ [\mathrm{DecidableEq}\,\alpha]\;
\forall (s : \mathrm{Finset}\,\alpha)\;
\forall (p : \alpha \to \mathbb{R}_{\geq 0}^{\infty})\;
\forall (n : \mathbb{N})\;
\bigl(\textstyle\sum_{i \in s} p_i = 1\bigr) \;\Longrightarrow\;
\textstyle\sum_{k : \mathrm{Composition}\,\alpha\,s\,n} \binom{n}{k}\,\textstyle\prod_{i \in s} p_i^{k_i} = 1.
$$

### Lean Target Signature (S2 ACT-A)

A new file
`proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean` should
deliver, with 0 sorries and 0 axioms:

```lean
theorem BinomialTheoremOQ02OQ01OQ01.multinomialPMF_sum_eq_one_proved
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ENNReal) (n : ℕ)
    (hp : ∑ i ∈ s, p i = 1) :
    ∑ k : BinomialTheoremOQ02OQ01OQ01.Composition α s n,
      BinomialTheoremOQ02OQ01OQ01.multinomialPMFVal s p n k = 1
```

The proof composes:

1. `compositionTypeEquiv` — an equivalence
   `BinomialTheoremOQ02OQ01OQ01.Composition α s n ≃
    CompositionFintype.Composition α s n` (structurally identical, but
   in different namespaces; ~10-line trivial bijection).
2. `CompositionFintype.sum_composition_eq_piAntidiag_sum` — already
   proved in `BinomialTheoremOQ02OQ01OQ01OQ01.lean`.
3. `Finset.sum_pow_eq_sum_piAntidiag` — Mathlib, instantiated at
   `R := ENNReal`.
4. `hp` plus `one_pow n : (1 : ENNReal) ^ n = 1`.

The S2 ACT-A file does NOT modify
`BinomialTheoremOQ02OQ01OQ01.lean` (the sorry remains there for
historical reasons; the proven version lives in the new child file
under the `BinomialTheoremOQ02OQ01OQ01` namespace as
`multinomialPMF_sum_eq_one_proved`). A future doc-sync session may
optionally back-port the proof to the parent file once the bridge
equivalence has settled into a stable shape.

### What This OQ Entry Does NOT Claim

* It does not prove the four other sorries in
  `BinomialTheoremOQ02OQ01OQ01.lean` (`multinomialPMF_support`,
  `multinomial_marginal_binomial`, `multinomial_mean`,
  `multinomial_covariance`). Those have separate slugs or remain
  open follow-ons.
* It does not contribute to Mathlib upstream. The Mathlib bridge for
  a full `PMF.multinomial` constructor is a separate project; this
  slug only discharges the gallery-internal sorry.
* It does not generalize beyond `ℝ≥0∞`; the gallery's PMF target type
  is fixed at `ENNReal` by the `PMF` definition in
  `Mathlib.Probability.ProbabilityMassFunction.Basic`.

## Classification

```yaml
tier: B
significance: 5
tractability: 5
tags:
  - combinatorics
  - multinomial
  - fintype
  - piAntidiag
  - composition
  - probability
  - mathlib-bridge
  - seeker-selected
  - gallery-extracted
```

**Significance**: 5/10 — Discharges one named sorry in a
mid-significance gallery entry. The proof itself is short (≤ 60
lines), but it closes a multinomial-PMF normalization gap that
several downstream marginal/mean/variance lemmas depend on.

**Tractability**: 5/10 — The two required lemmas already exist
(parent's structural bridge + Mathlib's multinomial theorem); the
remaining work is the namespace-bridge equivalence plus a 10-line
sequence of `rw`/`simp`/`exact` steps. The S1 audit confirmed the
Mathlib API is in v4.26.0 at the pinned rev. Tractability would be
6-7 except for the cross-namespace `Composition` overhead.

## Why This Matters

1. **Unblocks four downstream sorries.** The four other sorries in
   `BinomialTheoremOQ02OQ01OQ01.lean`
   (`multinomialPMF_support`, `multinomial_marginal_binomial`,
   `multinomial_mean`, `multinomial_covariance`) all depend on the
   `multinomialPMF` being a well-formed PMF, which in turn requires
   `multinomialPMF_sum_eq_one`. Once this slug is closed, those four
   can be attacked independently.

2. **Validates the parent's design philosophy.** The parent file's
   §"Feasibility Analysis" claims `sum_pow_eq_sum_piAntidiag` is the
   exact Mathlib hook needed for normalization. This slug formally
   verifies that claim with a `0 sorries, 0 axioms` Lean file.

3. **Demonstrates the composition-pattern bridge.** The technique of
   pairing a gallery `Composition` type with `piAntidiag` via a
   structural bijection is reusable for any similar combinatorial
   PMF (Dirichlet-multinomial, hypergeometric, etc.). This slug is
   the smallest end-to-end exhibit of the pattern.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `binomial-theorem` | Root entry — gallery's home for the binomial / multinomial expansion. |
| `binomial-theorem-oq-02-oq-01-oq-01-oq-01` | Parent file with the `multinomialPMF_sum_eq_one` sorry being discharged. |
| `binomial-theorem-oq-02-oq-01-oq-01` | Houses the `multinomialPMF` definition and the surrounding PMF infrastructure (5 sorries total, this slug discharges 1). |
| `binomial-theorem-oq-02-oq-01-oq-01-oq-01` (sibling) | The `CompositionFintype` file containing `sum_composition_eq_piAntidiag_sum`, the structural-bridge lemma we will compose with `sum_pow_eq_sum_piAntidiag`. |
| `ehrhart-cube-proven-oq-04` | Uses the same `piAntidiag` API for a different combinatorial identity (Worpitzky / Eulerian); cross-references this slug for the multinomial-theorem invocation pattern. |
