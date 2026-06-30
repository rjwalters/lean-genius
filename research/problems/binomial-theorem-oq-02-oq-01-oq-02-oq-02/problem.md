# binomial-theorem-oq-02-oq-01-oq-02-oq-02 — Multinomial covariance `Cov(Xᵢ,Xⱼ) = −n·pᵢpⱼ`

## Target

If `(X₁,…,X_k) ~ Multinomial(n, p₁,…,p_k)`, then for `i ≠ j`
```
        Cov(Xᵢ, Xⱼ) = − n · pᵢ · pⱼ.
```
The off-diagonal entries of the multinomial covariance matrix are negative —
components compete for the fixed total `n`, so an excess in one coordinate
depresses the others. This is the natural follow-up to the parent entry
`binomial-theorem-oq-02-oq-01-oq-02` ("Marginal Distributions of Multinomial Are
Binomial", **verified**), which established the marginal `Xᵢ ~ Binomial(n, pᵢ)`
and hence the diagonal `Var(Xᵢ) = n·pᵢ(1−pᵢ)` and the means `E[Xᵢ] = n·pᵢ`.

## Framework (inherited from the parent — combinatorial, NOT measure-theoretic)

The parent works with explicit PMF values, no measure space:

```lean
noncomputable def multinomialProb {α} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (k : α → ℕ) : ℝ :=
  (Nat.multinomial s k : ℝ) * ∏ i ∈ s, p i ^ k i
```
and the engine
```lean
theorem multinomial_mgf_real (s : Finset α) (p g : α → ℝ) (n : ℕ) :
    (∑ i ∈ s, p i * g i) ^ n
      = ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * ∏ i ∈ s, g i ^ k i
```
(`Proofs/BinomialTheoremOQ02OQ01OQ02.lean:63`). The state space is
`s.piAntidiag n` = functions `k : α → ℕ` supported on `s` with `∑_{i∈s} k i = n`.

In this framework expectations are explicit finite sums:
```
        E[f(X)] = ∑_{k ∈ s.piAntidiag n} multinomialProb s p n k · f(k).
```

## Formal statement to target

```lean
/-- Mixed (i≠j) second moment of the multinomial. -/
theorem multinomial_mixed_moment {α} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    {i j : α} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * (k i : ℝ) * (k j : ℝ)
      = (n * (n - 1) : ℝ) * p i * p j := …

/-- First moment (mean) of a single coordinate. -/
theorem multinomial_mean {α} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1) {i : α} (hi : i ∈ s) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * (k i : ℝ) = n * p i := …

/-- **Headline**: off-diagonal covariance. -/
theorem multinomial_covariance {α} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    {i j : α} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    (∑ k ∈ s.piAntidiag n, multinomialProb s p n k * (k i : ℝ) * (k j : ℝ))
      - (∑ k ∈ s.piAntidiag n, multinomialProb s p n k * (k i : ℝ))
        * (∑ k ∈ s.piAntidiag n, multinomialProb s p n k * (k j : ℝ))
      = - (n : ℝ) * p i * p j := …
```
The headline is then pure algebra from the two moment lemmas:
`n(n−1)pᵢpⱼ − (npᵢ)(npⱼ) = −n·pᵢpⱼ`.

(Optionally wrap with a `covariance`-style abbreviation, but keeping it as the
explicit `E[XY] − E[X]E[Y]` difference avoids dragging in measure-theoretic
`ProbabilityTheory.covariance`, which would not match this combinatorial setup.)

## Two viable proof routes for the mixed moment

### Route A — factorial-moment combinatorial bijection (recommended; matches parent style)
The parent's `multinomial_marginal_pmf` used `Nat.multinomial_insert` + a
`Finset.sum_nbij'` reindexing; the mixed moment is the same pattern one level up.

1. **Factorial identity** (the crux): for `k ∈ s.piAntidiag n` with `kᵢ,kⱼ ≥ 1`,
   ```
   kᵢ · kⱼ · Nat.multinomial s k = n·(n−1) · Nat.multinomial s (k − eᵢ − eⱼ)
   ```
   where `k − eᵢ − eⱼ` decrements coordinates `i,j`. Proof via
   `Nat.multinomial_spec` (`(∏ (k i)!)·multinomial = (∑ k i)!`): on both sides
   cancel factorials, using `kᵢ·(kᵢ−1)! = kᵢ!` and `n·(n−1)·(n−2)! = n!`.
   Terms with `kᵢ = 0` or `kⱼ = 0` vanish (the `kᵢ·kⱼ` factor is 0), so they do
   not obstruct the bijection's domain.
2. **Reindex** `k ↦ k − eᵢ − eⱼ` as a bijection `s.piAntidiag n` (restricted to
   `kᵢ,kⱼ ≥ 1`) ≃ `s.piAntidiag (n−2)`, pulling out `pᵢ·pⱼ` from
   `∏ p^{k} = pᵢ·pⱼ·∏ p^{k−eᵢ−eⱼ}`.
3. The remaining sum is `∑_{k' ∈ piAntidiag (n−2)} multinomialProb s p (n−2) k' = 1`
   by `multinomialProb_sum_one` (parent, line 78) with `hp`.
   ⇒ mixed moment `= n(n−1)·pᵢ·pⱼ`.
   (Edge cases `n = 0, 1`: both sides `0`; handle by `interval_cases`/`omega`
   before invoking the `n−2` machinery.)

### Route B — joint PGF + two derivatives
Instantiate `multinomial_mgf_real` with `g a = x` if `a=i`, `y` if `a=j`, else
`1`. This gives the joint PGF
`(pᵢ x + pⱼ y + (1 − pᵢ − pⱼ))^n = ∑_k multinomialProb · x^{kᵢ} y^{kⱼ}`.
Then `E[XᵢXⱼ] = ∂²/∂x∂y |_{x=y=1}`. LHS derivative `= n(n−1)(…)^{n−2}·pᵢpⱼ → n(n−1)pᵢpⱼ`
at `x=y=1` (base `=1`). Cleaner on paper, but differentiating a finite power
series term-by-term in Lean (`Polynomial.derivative` / `deriv` interchange with
`Finset.sum`) is at least as much work as Route A and less aligned with the
existing combinatorial lemmas. **Prefer Route A.**

`multinomial_mean` is the `marginal_pmf`/PGF result already in hand: either reuse
the parent's binomial marginal (mean of `Binomial(n,pᵢ)` is `n pᵢ`) or run the
same Route-A bijection with a single decremented coordinate (one-coordinate
factorial-moment, `kᵢ·multinomial = n·multinomial(k−eᵢ)`).

## Mathlib bearer audit (static, mathlib v4.26.0 — Docker/Aristotle both down)

Confirmed present in `proofs/.lake/packages/mathlib`:
- `Nat.multinomial_spec` — `(∏ i ∈ s,(f i)!)·multinomial s f = (∑ i ∈ s, f i)!`
  (Data/Nat/Choose/Multinomial.lean:50). **Engine for the factorial identity.**
- `Nat.multinomial_pos`, `Nat.multinomial_insert`, `Nat.multinomial_congr` (same file).
- `Finset.piAntidiag`, `Finset.mem_piAntidiag`, `Finset.sum_pow_eq_sum_piAntidiag`
  (already used by the parent).
- `Finset.sum_nbij'` / `Finset.sum_bij'` for the reindexing (parent precedent).
- Parent lemmas reused directly: `multinomialProb`, `multinomial_mgf_real`,
  `multinomialProb_sum_one`.

**Expected ABSENT (the genuine gap):** no packaged "multinomial factorial moment"
or "multinomial covariance" lemma in Mathlib. Must be assembled as above. Mathlib
*does* have `ProbabilityTheory.covariance` (measure-theoretic) but bridging the
combinatorial PMF to a genuine `Measure`/`PMF` random vector is a separate, larger
project (not needed for this entry — keep it self-contained like the parent).

## LOC / risk estimate

- `multinomial_mean`: ~40–70 LOC (single-coordinate bijection or reuse parent).
- `multinomial_mixed_moment`: ~120–200 LOC. **Risk R1 (high):** the
  `k ↦ k − eᵢ − eⱼ` bijection on `piAntidiag` — proving membership
  (`∑ = n−2`), the inverse `k' ↦ k' + eᵢ + eⱼ`, and the factorial cancellation —
  is the same finicky `sum_nbij'` bookkeeping that cost the parent a full Session 2.
  Budget the bulk of a build-up session here.
- `multinomial_covariance`: ~10 LOC algebra (`ring`/`push_cast` + `omega` for `n−1`).
- Total ~200–280 LOC, one verified file `Proofs/BinomialTheoremOQ02OQ01OQ02OQ02.lean`.

## Status / next action

- **OQ-chain depth:** this slug has **4** `-oq-` segments (depth 4). Per the
  researcher depth guard, **generate 0 follow-up questions** from this entry; the
  Seeker would refuse a depth-5 child anyway. This is a *terminal* OQ — close it
  with the proof, do not spawn descendants.
- **This session (researcher-3, ORIENT):** dual-backend blackout (Docker
  `containerd` store I/O-corrupted; Aristotle MCP 404). No Lean written to avoid
  shipping an unbuildable fiddly bijection blind (the "do not attempt blind"
  guidance for `sum_nbij'`-class bookkeeping). Produced this precise statement,
  the two-route plan, and the bearer audit.
- **Next (build-up session, Docker restored):** implement Route A in
  `Proofs/BinomialTheoremOQ02OQ01OQ02OQ02.lean`; start with `multinomial_mean`
  to shake out the single-coordinate bijection, then lift to two coordinates;
  finish with the `ring` algebra for the covariance. Target verified, 0-axiom.
