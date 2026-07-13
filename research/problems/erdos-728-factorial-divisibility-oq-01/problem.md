# Problem: Optimality of the Logarithmic Gap in Erdős #728 Factorial Divisibility

**Slug**: erdos-728-factorial-divisibility-oq-01
**Created**: 2026-07-09T15:22:59-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For the divisibility relation `a! · b! ∣ n! · (a+b−n)!` with range constraints, Erdős proved an upper bound on the gap `g := a + b − n`. Writing `g(n)` for the maximal admissible gap at scale `n` (subject to `εn ≤ a, b ≤ (1−ε)n`), the parent proof establishes that `g(n) = Ω(log n)` is *achievable* infinitely often. The open question asks whether this logarithmic bound is asymptotically tight, i.e., whether the Erdős upper bound can be improved or whether super-logarithmic gaps are possible:

$$
\exists\, \varepsilon > 0 \;:\; \limsup_{n \to \infty} \; \frac{1}{\log n} \max\Big\{\, a + b - n \;:\; \varepsilon n \le a,b \le (1-\varepsilon)n,\; a!\,b! \mid n!\,(a+b-n)! \,\Big\} \;=\; +\infty ?
$$

Equivalently: is there a function `h(n) = ω(log n)` and infinitely many admissible triples `(a, b, n)` with `a! · b! ∣ n! · (a+b−n)!` and `a + b − n ≥ h(n)`? The conjectured answer (matching Erdős's upper bound) is **no**: the gap is `Θ(log n)` and cannot exceed `O(log n)`.

### Plain Language

Erdős, Graham, Ruzsa, and Straus asked when a product of two factorials `a!·b!` divides `n!·(a+b−n)!`. Erdős proved that when this divisibility holds (with `a, b` a bounded fraction of `n`), the sum `a + b` cannot exceed `n` by more than a constant times `log n`. The parent gallery proof (Erdős #728) shows this logarithmic "overshoot" is genuinely achievable: infinitely many triples push the gap up to `c·log n` for any constant `c`.

This companion problem asks about the *other* direction — is `log n` the true ceiling? Can we prove that no admissible triple ever achieves a gap growing faster than `log n` (e.g., `(log n)^2` or `√n`)? Formalizing Erdős's upper-bound argument would confirm that the parent construction is optimal and the gap is exactly of logarithmic order.

### Why This Matters

The parent proof gives the *lower* half of a two-sided estimate — it shows the gap is at least logarithmic infinitely often. Without the matching upper bound, the picture is incomplete: we know `log n` is achievable but not that it is the maximum. Formalizing the upper bound would:

- **Complete the asymptotic characterization** `g(n) = Θ(log n)`, closing the gap between the parent construction and Erdős's original inequality.
- **Verify a classical Erdős result** (`a + b ≤ n + O(log n)`) that is stated informally in the parent's problem statement but not itself formalized in the gallery.
- **Certify optimality** of the AI-generated construction, strengthening the credibility of the #728 resolution.
- **Exercise p-adic valuation machinery** (Legendre's formula, Kummer's theorem) in the *upper-bound* direction, complementing the lower-bound / probabilistic-method techniques already formalized.

## Known Results

### What's Already Proven

- **Erdős #728 lower bound** (`erdos_728`, `erdos_728_fc` in the parent gallery proof) — for every `C > 0` and `0 < ε < 1/2` there are infinitely many triples `(a,b,n)` with `a!·b! ∣ n!·(a+b−n)!` and `a + b > n + C·log n`. Fully verified, 0 axioms, 0 sorries (`Proofs/Erdos728FactorialDivisibility.lean`).
- **Kummer's theorem** (`padicValNat_choose`, Mathlib `Mathlib.NumberTheory.Padics.PadicVal`) — the `p`-adic valuation of `C(n, k)` equals the number of carries when adding `k` and `n−k` in base `p`. Already used throughout the parent proof.
- **Legendre's formula / `Nat.factorial` valuation** (`Nat.Prime.factorization_factorial`, `Nat.factorization_factorial`) — `v_p(n!) = Σ_{j≥1} ⌊n/p^j⌋`. This is the natural tool for the upper-bound direction.
- **Erdős's classical upper bound** (Erdős, 1975 / Erdős–Graham problem list): if `a!b! ∣ n!` with `a, b ≤ (1−ε)n` then `a + b ≤ n + O_ε(log n)`. Stated in the parent problem background but **not** formalized.

### What's Still Open

- Whether the Erdős `O(log n)` upper bound on the gap can be improved (sharpened constant) — a quantitative refinement.
- Whether any admissible triple can achieve a super-logarithmic gap `a + b − n = ω(log n)` — conjecturally impossible.
- The exact asymptotic density / distribution of good triples (a separate open question from the parent).

### Our Goal

Formalize the **upper-bound half**: prove in Lean that there is a constant `C'(ε)` such that for all admissible triples with `a!·b! ∣ n!·(a+b−n)!` and `εn ≤ a, b ≤ (1−ε)n`, one has

`a + b − n ≤ C'(ε) · log n + O(1)`.

Combined with the parent's lower bound, this yields the two-sided `a + b − n = Θ(log n)` characterization and answers the open question ("no, the gap cannot be improved beyond `O(log n)`") in the negative-for-improvement / affirmative-for-optimality sense.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-728-factorial-divisibility | Parent problem; supplies the matching lower bound `a+b > n + C·log n` and all shared p-adic infrastructure | Kummer's theorem, p-adic valuation, probabilistic method, Chernoff bounds |
| wilsons-theorem | p-adic / prime valuations of factorials are central to both; supplies factorial–prime lemmas | Factorials mod primes, `padicValNat` |
| erdos-727 | Sister Erdős problem on factorial divisibility patterns; upper-bound reasoning likely transfers | Factorial divisibility, extremal number theory |
| prob-method-second-moment | Contrast/complement: parent uses probabilistic lower bounds; upper bound is deterministic p-adic counting | Second-moment / concentration vs. deterministic valuation |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Legendre-formula prime counting.** Express `v_p(a!) + v_p(b!) ≤ v_p(n!) + v_p((a+b−n)!)` for every prime `p` via Legendre's formula and sum a suitable weighted count. For a fixed prime `p ≈ n^{1/2}`-scale, the divisibility forces carry structure; counting the number of primes in `(n − (a+b−n), n]` that must "absorb" the excess bounds `a + b − n` by the count of primes in a logarithmic-length window, which is `O(log n / log log n)` or `O(log n)` by Chebyshev/PNT-type estimates.
   - Why it might work: the parent already formalizes the `p`-adic valuation identities in both directions; the upper bound is the "dual" counting and reuses `padicValNat_choose` and Legendre.
   - Risk: turning a per-prime valuation inequality into a *global* additive bound on `a + b − n` requires a clean summation lemma; getting the constant `C'(ε)` explicit may need Chebyshev-type prime-counting bounds that are heavier in Mathlib.

2. **Approach B — Kummer carry-budget argument.** Restate divisibility as `v_p(C(a+b−n+ (something), ·))`-style carry inequalities and bound the total number of primes for which carries can occur. Since each contributing prime lies in a short interval near `n` and there are only `O(log n)` such primes in the relevant dyadic windows (by Bertrand/Chebyshev density), the gap is capped at `O(log n)`.
   - Why it might work: directly parallels the parent's `lemma_forced_carries_*` lemmas but used as an upper bound on how large the gap can be rather than a lower bound on valuation.
   - Risk: the parent's carry lemmas are tuned for *lower* bounds; adapting them to a tight upper bound and pinning down the `ε`-dependence of the constant is delicate. Handling boundary primes `p ∣ (a+b−n)!` carefully is error-prone.

### Key Difficulties

- Converting a family of per-prime valuation inequalities into a single additive upper bound on `a + b − n` (the "summation to a global bound" step).
- Making the `ε`-dependence of the constant `C'(ε)` explicit and correct, since the bound degenerates as `ε → 0`.
- Prime-counting inputs (Chebyshev / Bertrand-type density of primes in short intervals) may be needed and can be Mathlib-heavy.
- Avoiding double-counting between the `n!` and `(a+b−n)!` contributions on the right-hand side.

### What Would a Proof Need?

- **Key lemma 1**: A Legendre-formula divisibility criterion — `a!b! ∣ n!(a+b−n)!` iff for all primes `p`, `Σ_j ⌊a/p^j⌋ + ⌊b/p^j⌋ ≤ ⌊n/p^j⌋ + ⌊(a+b−n)/p^j⌋`.
- **Key lemma 2**: A carry/prime-window bound showing that the number of primes `p` (in the relevant range) forcing a positive contribution is `O(log n)`, using Chebyshev-type prime density.
- **Key lemma 3**: A summation lemma converting the per-prime inequalities and the `O(log n)` prime count into `a + b − n ≤ C'(ε) log n + O(1)`.
- **Technical requirements**: `Nat.factorization_factorial` / Legendre, `padicValNat_choose`, a Chebyshev or Bertrand prime-density bound, and real-log asymptotic bookkeeping (`Real.log`, `Filter.Tendsto`).

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The lower-bound half is already fully formalized in the parent (`Proofs/Erdos728FactorialDivisibility.lean`), so all the shared p-adic infrastructure (Kummer, Legendre, `padicValNat`) is available and battle-tested.
- However, the upper bound requires prime-counting inputs (Chebyshev / Bertrand-type density of primes in short intervals) and an explicit `ε`-dependent constant, which are substantially harder to formalize cleanly than a single existence construction.
- Similar upper-bound valuation arguments (e.g., bounds on `v_p(C(n,k))`, Kummer-based) exist in Mathlib, but assembling them into a tight global `O(log n)` gap bound with correct constants is a multi-lemma effort.
- Related solved work: the parent #728 and #727 factorial-divisibility results show the domain is formalizable, but they target existence/lower bounds rather than sharp upper bounds.

**Estimated Effort**:
- Exploration: 3–5 days
- If tractable: 3–6 weeks
- If hard: unknown (may require formalizing missing prime-counting lemmas first)

## References

### Papers
- Erdős, P., Graham, R. L., Ruzsa, I. Z., Straus, E. G., "On the prime factors of `C(2n, n)`", *Mathematics of Computation* 29 (1975), 83–92 — origin of factorial-divisibility questions and the `O(log n)` gap philosophy.
- Kummer, E. E., "Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen", *Journal für die reine und angewandte Mathematik* 44 (1852), 93–146 — carries-in-base-`p` characterization of binomial valuations.
- Legendre, A.-M., *Théorie des nombres* (1830) — `v_p(n!) = Σ_j ⌊n/p^j⌋`, the core tool for the upper-bound direction.
- Barreto, K., GPT-5.2, Harmonic Aristotle, "Resolution of Erdős Problem #728" (2026) — the parent AI-generated solution establishing the logarithmic lower bound; see https://www.erdosproblems.com/728.

### Online Resources
- https://www.erdosproblems.com/728 — canonical statement, background, and status of Erdős problem #728.
- https://www.erdosproblems.com/727 — sister factorial-divisibility problem #727.

### Mathlib
- `Mathlib.NumberTheory.Padics.PadicVal` — `padicValNat`, `padicValNat_choose` (Kummer's theorem), p-adic valuation of factorials.
- `Mathlib.Data.Nat.Factorization.Basic` — `Nat.factorization_factorial` (Legendre's formula), factorization of factorials.
- `Mathlib.Data.Nat.Choose.Factorization` — valuations of binomial coefficients, `Nat.factorization_choose`.
- `Mathlib.NumberTheory.Bertrand` / `Mathlib.NumberTheory.PrimeCounting` — Bertrand's postulate and prime-counting bounds for the prime-window step.
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` — `Real.log` for the asymptotic gap statement.

## Metadata

```yaml
tags:
  - number-theory
  - factorial
  - p-adic
  - erdos
  - prime-counting
related_proofs:
  - erdos-728-factorial-divisibility
  - erdos-727
  - wilsons-theorem
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:22:59-07:00
```
