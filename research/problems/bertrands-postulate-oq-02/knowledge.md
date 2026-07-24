# Knowledge Base: Legendre's Conjecture (`bertrands-postulate-oq-02`)

## Progress Summary

**Date**: 2026-05-30
**Researcher**: researcher-1 (Session 1)
**Phase**: SURVEY (initial)
**Result**: Survey of unconditional and conditional partial results,
identification of three candidate tractable sub-milestones for follow-up
iterations.

## Phase: SURVEY

### What Legendre's Conjecture Says

For every $n \geq 1$, there is a prime $p$ with $n^2 < p < (n+1)^2$.

The interval has length $(n+1)^2 - n^2 = 2n + 1$. Substituting $x = n^2$, the
length is $\approx 2\sqrt{x}$. So Legendre is essentially the statement:

> there is a prime in $[x, x + 2\sqrt{x} + 1]$ for every $x = n^2$, $n \geq 1$.

The conjecture is *equivalent* to the prime-gap bound

$$
g(p_k) := p_{k+1} - p_k < 2\sqrt{p_k} + 1
$$

for every $k$, in a quantitative form. (See Granville, "Harald Cramér and the
distribution of prime numbers," *Scand. Actuar. J.* 1995.)

### What Is Known Unconditionally

The state of the art on **prime gaps in short intervals** $[x, x + h]$:

| Year | Authors | Result | Source |
|------|---------|--------|--------|
| 1930 | Hoheisel | $h = x^{1 - 1/33000}$ | First non-trivial $\theta < 1$ |
| 1972 | Huxley | $h = x^{7/12 + \varepsilon}$ | Density of $\zeta$ zeros |
| 2001 | Baker–Harman–Pintz | $h = x^{0.525}$ | Best unconditional |

Legendre's conjecture requires $h = O(\sqrt{x}) = x^{1/2}$, i.e. $\theta = 1/2$.
The Baker–Harman–Pintz gap of $0.525$ is the closest unconditional approach but
**still does not reach Legendre**. The gap $\theta = 1/2$ itself appears to
require either RH (which gives $\theta = 1/2 + \varepsilon$ for *almost all*
intervals, not all) or a substantial new idea.

### What Is Known Conditionally

| Hypothesis | Best gap result | Implies Legendre? |
|------------|------------------|-------------------|
| Riemann Hypothesis | $g(p_k) = O(\sqrt{p_k} \log p_k)$ (Cramér 1936) | **No** — has an extra $\log$ |
| RH + Lindelöf | Same | No |
| Cramér's conjecture | $g(p_k) = O((\log p_k)^2)$ | Yes (overwhelmingly) |
| Heath-Brown / Goldston density hypothesis | $h = x^{1/2 + \varepsilon}$ for *most* intervals | Not for every $n$ |

**Key observation**: Even under RH, Legendre's conjecture is **not known**.
Cramér's 1936 bound under RH gives $g(p_k) \ll \sqrt{p_k} \log p_k$, which is
*one logarithmic factor too weak*: at $p_k \approx n^2$, this guarantees a gap
$\ll n \log(n^2) = 2n \log n$, but Legendre needs the gap $\leq 2n$.

This is widely cited (e.g. Tao, "Structure and randomness in the prime
numbers," 2007) as the reason Legendre is *harder* than RH.

### Variants and Partial Results Worth Knowing

1. **Iwaniec–Pintz (1984)**: there is a prime in $[x - x^{1/2 + \varepsilon},
   x]$ for almost all $x$ (with explicit "exceptional set" bound).
2. **Heath-Brown (1988)**: $\theta = 7/12$ for the *Brun–Titchmarsh*-style
   prime-counting in short intervals.
3. **Ingham (1937)** showed under unproved hypotheses on $\zeta$ zeros, prime
   gaps satisfy $g \ll p^{1/2}$.
4. **Computational verification** (Nicely, Oliveira e Silva, et al.): Legendre
   verified for all $n \leq 1.5 \times 10^{18}$ as of 2024.

### What Is in Mathlib

| Component | Available | Form |
|-----------|-----------|------|
| `Nat.bertrand` | **Yes** | `∀ n ≥ 1, ∃ p, p.Prime ∧ n < p ∧ p ≤ 2 * n` |
| `Nat.exists_infinite_primes` | **Yes** | Euclid |
| Prime counting $\pi(x)$ | **Yes** | `Nat.Primes.card` + `Nat.primesBelow` |
| Riemann zeta zeros | **Partial** | `ZetaFunctional`, `riemannZeta` defined |
| Prime gap function | **No** | Not formalized as a definition |
| Cramér's conjecture | **No** | Not stated in Mathlib |
| RH | **Defined, axiomatized** | `RiemannHypothesis` Prop |

### Why Bertrand Doesn't Help (Recap)

Bertrand: $\exists p$ prime, $n < p \leq 2n$.

Setting $n = n_0^2$: there exists $p$ prime with $n_0^2 < p \leq 2 n_0^2$. But
Legendre requires $p < (n_0 + 1)^2 = n_0^2 + 2 n_0 + 1$, and for $n_0 \geq 2$
the upper bound $2 n_0^2$ is much larger than $n_0^2 + 2 n_0 + 1$. So Bertrand
is too weak by a factor of $\sim n_0$.

The "right" Bertrand-like statement implying Legendre would be

> $\exists p$ prime, $n < p < n + 2\sqrt{n} + 1$,

which is exactly Legendre after a substitution. No such Bertrand-strength
elementary proof is known.

## Three Candidate Sub-Milestones for Follow-up Iterations

In order of increasing difficulty:

### Sub-Milestone A (tractability ~8): Formalize "Legendre under Cramér"

Statement: If `Cramer's conjecture` holds — i.e., `∃ C, ∀ k, p_(k+1) - p_k ≤
C * (log p_k)^2` — then Legendre's conjecture holds for all sufficiently large
$n$.

Proof idea: For $n$ large enough that $C (\log n^2)^2 < 2n + 1$, any prime gap
hitting an interval of length $\geq 2n + 1$ contains a prime. Combine with the
`legendre-partial` computational base case for small $n$.

**Mathlib readiness**: Cramér's conjecture is not stated. Would define it as
an `axiom` or `def` (Prop), then state and prove the implication.

### Sub-Milestone B (tractability ~6): Formalize equivalence with gap bound

Statement: `LegendreConjecture ↔ ∀ k, p_(k+1) - p_k ≤ 2 * √p_k`.

Proof idea: Forward direction — for every $n$, choose $p_k$ to be the largest
prime $\leq n^2$, then $p_{k+1} \leq (n+1)^2 = p_k + \text{gap}$, and apply
the gap bound. Reverse direction — analogous.

**Mathlib readiness**: Needs prime-gap function definition (not in Mathlib).
Could define it locally.

### Sub-Milestone C (tractability ~9): Extend computational verification

Statement: `LegendreAt n` for $n = 21, \dots, 50$ (or some new range).

Proof idea: Same `native_decide` + explicit witness pattern as
`legendre-partial`, just extended.

**Risk**: Pure padding of existing work; minimal mathematical content. Only
valuable if presented as part of a structural infrastructure (e.g. a
`LegendreWitness` tactic that auto-finds witnesses).

## Recommended Next Step (Iteration 2)

Pursue **Sub-Milestone B** (equivalence with gap bound) — it is purely
formal-mathematical (no number-theoretic hypotheses), creates a reusable
prime-gap definition for the gallery, and yields a publishable Lean lemma.

A. Define `primeGap : ℕ → ℕ` (gap to next prime), prove basic properties.

B. State `legendreConjecture ↔ ∀ n, primeGap (nth_prime n) ≤ 2 * ⌈√(nth_prime n)⌉`.

C. Prove both directions (no open math content; pure unwinding).

## References

- Granville, A. "Harald Cramér and the distribution of prime numbers,"
  *Scand. Actuar. J.* (1995). https://dms.umontreal.ca/~andrew/PDF/cramer.pdf
- Baker, R. C.; Harman, G.; Pintz, J. "The difference between consecutive
  primes, II," *Proc. London Math. Soc.* 83 (2001), 532–562.
- Heath-Brown, D. R. "The number of primes in a short interval,"
  *J. Reine Angew. Math.* 389 (1988), 22–63.
- Tao, T. "Structure and randomness in the prime numbers" (2007),
  https://terrytao.wordpress.com/2007/05/22/
- Wikipedia: https://en.wikipedia.org/wiki/Legendre%27s_conjecture
- OEIS A014085: Number of primes between $n^2$ and $(n+1)^2$.

## Files

**Iteration 1 (SURVEY)**: No Lean source produced.

**Iteration 2 (DEEP DIVE — Sub-Milestone B, 2026-05-30)**: Created
`proofs/Proofs/LegendreGapEquivalence.lean` (212 lines, 15 theorems, 6 defs,
0 axioms, 0 sorries, build verified).

## Iteration 2 Log: Sub-Milestone B Complete

**Date**: 2026-05-30
**Researcher**: researcher-1 (Session 2)
**Phase**: ACT — DEEP DIVE
**Result**: Equivalence-form lemmas for Legendre's Conjecture, 0 new axioms.

### Deliverable

`proofs/Proofs/LegendreGapEquivalence.lean` proves that Legendre's Conjecture
is equivalent to three structural reformulations:

| Form | Statement (for each $n \geq 1$) |
|------|-------------------------------|
| Original | $\exists p$ prime, $n^2 < p < (n+1)^2$ |
| Gap | $\exists p$ prime, $n^2 < p \leq n^2 + 2n$ |
| Distance | $\exists p$ prime, $p > n^2 \land p - n^2 \leq 2n$ |
| Half-open | $\exists p$ prime, $n^2 + 1 \leq p \leq n^2 + 2n$ |

All three equivalences are proved via the identity $(n+1)^2 = n^2 + 2n + 1$
combined with `omega`. The proofs are structural, not arithmetic-deep, and
they bridge from the original formulation to the form used in the prime-gap
literature.

### Key Theorems

- `legendreAt_iff_gap (n : ℕ) : LegendreAt n ↔ LegendreGapAt n`
- `legendreAt_iff_distance (n : ℕ) : LegendreAt n ↔ LegendreDistanceAt n`
- `legendreAt_iff_halfOpen (n : ℕ) : LegendreAt n ↔ LegendreHalfOpenAt n`
- `legendre_iff_gap_form : LegendreConjecture ↔ LegendreGapForm`
- `legendre_iff_distance_form : LegendreConjecture ↔ LegendreDistanceForm`
- `legendre_iff_halfOpen_form : LegendreConjecture ↔ LegendreHalfOpenForm`

Plus five sample transferrals (`legendre_gap_1`, `legendre_gap_5`,
`legendre_gap_20`, `legendre_distance_10`, `legendre_halfOpen_15`) confirming
that `LegendrePartial`'s computational base cases hold in each equivalent form
via one `.mp` step.

### Why This Matters

1. The gap form aligns with short-interval prime theory: at $x = n^2$, Legendre
   asserts a prime in $[x, x + 2\sqrt{x}]$. This is exactly the
   $\theta = 1/2$ short-interval problem, allowing direct comparison with
   Hoheisel ($\theta = 1 - 1/33000$), Huxley ($7/12$), and BHP ($0.525$).
2. The distance form is the form used to compare with Cramér's gap conjecture
   $g(p_k) = O((\log p_k)^2)$.
3. The half-open form makes `Finset.Ico` reasoning immediate for any future
   computational verification work.

### Honest Status

This iteration produced equivalence lemmas, **not** any progress on the open
conjecture itself. The mathematical content is purely structural; the value
lies in providing the gallery with a clean Lean record of "Legendre
equivalently says: gap above $n^2$ is at most $2n$" — a fact often stated
informally in the literature but not previously formalized in this gallery.

### Axiom Delta

| Before iteration 2 | After iteration 2 |
|--------------------|-------------------|
| 1 axiom (`legendre_conjecture` in `LegendrePartial.lean`) | 1 axiom (unchanged) |

The new file adds **0 new axioms** and **0 new sorries**.

### Next Steps

**Sub-Milestone B+ (Iteration 3)**: Prove the equivalence with the prime-gap
function:

  $\mathrm{LegendreConjecture} \iff \forall k,\ p_{k+1} - p_k \leq 2\sqrt{p_k} + 1$

This requires reasoning about consecutive primes (the `nth Nat.Prime`
function) and is strictly harder. Build on the
`nth_prime_succ_le_of_prime_gt` lemma already in `Proofs.PrimeGapBounds`.

**Sub-Milestone A (Iteration 4+)**: State and prove "Cramér's conjecture
implies Legendre's conjecture for sufficiently large $n$." Requires first
stating Cramér's conjecture (not in Mathlib).

## Iteration 5 Log: S4-ACT-α DONE — sqrt prime-gap bound suffices

**Date**: 2026-06-06
**Researcher**: researcher-1 (Session 5)
**Phase**: ACT — implementation of the corrected one-way implication
**Result**: New file `proofs/Proofs/LegendrePrimeGapSqrtBoundSuffices.lean`
(227 LOC, 0 axioms, 0 sorries) formalizes the salvageable direction
identified by iter-4 PREP-1.

### Deliverable

`LegendrePrimeGapSqrtBoundSuffices.lean` proves:

  `(∀ k, p_{k+1} - p_k ≤ 2 · √p_k + 1) ⟹ LegendreConjecture`

where `p_k := Nat.nth Nat.Prime k`. Plus three free corollaries (gap form,
distance form, half-open form) via composition with iteration-2's
`legendre_iff_*_form` equivalences.

### Why this iteration, not the original iff

Iteration 4 PREP-1 (memo `2026-06-05-iter4-prep-1-gap-bound-asymmetry.md`)
established that the forward direction `LegendreConjecture ⟹ gap bound` is
NOT provable from `LegendreConjecture` alone — the best derivable bound is
`≤ 4·√p_k + 2`, not `≤ 2·√p_k + 1`. This iteration formalizes the
salvageable reverse direction and documents the asymmetry from the Lean
source via the module docstring.

### Proof technique (in Lean)

For each `n ≥ 1`, the file constructs a prime in `(n², (n+1)²)`:

1. **Case `n = 1`**: prime `2` directly witnesses `LegendreAt 1` (a `refine`
   with `Nat.prime_two` plus `norm_num`).
2. **Case `n ≥ 2`**: Let `k := Nat.findGreatest (fun k => p_k ≤ n²) n²`,
   the index of the largest prime ≤ n². Key facts:
   - `Nat.findGreatest_spec` (with witness `k = 0`, since `p_0 = 2 ≤ n²`)
     yields `p_k ≤ n²`.
   - `not_prime_sq_of_ge_two` shows `n²` is composite for `n ≥ 2`, so
     `p_k ≠ n²` and hence `p_k < n²` strictly.
   - `nth_prime_ge` (k + 2 ≤ p_k) combined with `p_k < n²` gives the bound
     `k + 1 ≤ n²` needed for `Nat.findGreatest_is_greatest`.
   - `Nat.findGreatest_is_greatest` then yields `¬ (p_{k+1} ≤ n²)`, i.e.
     `p_{k+1} > n²`.
   - The gap-bound hypothesis at `k`: `p_{k+1} - p_k ≤ 2 · √p_k + 1`.
   - Strict monotonicity (`Nat.nth_strictMono Nat.infinite_setOf_prime`)
     converts the ℕ-subtraction into a clean addition for omega.
   - Sqrt monotonicity + `Nat.sqrt_lt'` (sqrt n < m ↔ n < m²) gives the
     bound `√p_k ≤ √(n² - 1) ≤ n - 1`.
   - omega assembles the linear arithmetic
     `p_{k+1} ≤ (n² - 1) + 2(n - 1) + 1 = n² + 2n - 2 < n² + 2n + 1 = (n+1)²`.

3. **Corollaries**: `legendre_iff_*_form.mp` lifts the main theorem through
   the iter-2 equivalences for gap/distance/half-open formulations.

### Axiom delta

| Before iteration 5 | After iteration 5 |
|--------------------|-------------------|
| 1 axiom (`legendre_conjecture` in `LegendrePartial.lean`) | 1 axiom (unchanged) |

0 new axioms, 0 new sorries. Docker build verified end-to-end.

### Honest status

This iteration produces a **conditional implication**, not progress on the
open conjecture itself. The hypothesis `PrimeGapSqrtBound` is essentially
equivalent in strength to Legendre (and is open: it would imply Legendre by
exactly this theorem). The value:

1. Closing the salvageable half of the broken iff (iter-4 PREP-1).
2. Three free corollaries via iter-2 equivalences.
3. A clean Lean statement of the gap-bound-suffices structure, ready to
   compose with future Cramér-style or BHP-style refinements.

### Next Steps

**Iteration 6 recommendation — Sub-Milestone A (Cramér ⇒ Legendre)**:
Now that `prime_gap_sqrt_bound_implies_legendre` is in place, the route to
Cramér ⇒ Legendre cleanly factors:

```
Cramér's conjecture
  ⟹ (for sufficiently large k) p_{k+1} - p_k ≤ C·(log p_k)² ≤ 2·√p_k + 1
  ⟹ LegendreConjecture (via prime_gap_sqrt_bound_implies_legendre,
                          modulo finite tail handled by legendre-partial)
```

Target file: `proofs/Proofs/CramerImpliesLegendre.lean`. Estimated +200-250
LOC. 0 new axioms expected (only Cramér as a hypothesis, not an axiom).
Hard parts: stating Cramér; the asymptotic `C·(log p_k)² ≤ 2·√p_k + 1`
for sufficiently large k; bridging the finite tail.

---

## Iteration 6 Log — S5-PREP-2 Cramér⇒Legendre bridging gap (researcher-9, 2026-06-10)

**Phase**: PREP / doc-only (no Lean edits)

### Audit motivation

Iter 5 (researcher-1, 2026-06-06) asserted the route Cramér ⇒ Legendre
"cleanly factors" through `prime_gap_sqrt_bound_implies_legendre`. This
pre-flight audit checks whether the type signatures actually compose
before committing the +200-250 LOC `CramerImpliesLegendre.lean` ACT.

### The structural quantifier mismatch

`prime_gap_sqrt_bound_implies_legendre` takes
`PrimeGapSqrtBound : Prop := ∀ k, p_{k+1} - p_k ≤ 2·√p_k + 1` — quantified
over **all** prime indices `k`.

Cramér's conjecture in *every* form is only `∀ k ≥ k₀` (an asymptotic /
"eventually" statement). The bound fails at small k: with the optimistic
C = 1, `C · (log p₀)² = (log 2)² ≈ 0.48 < 1 = p₁ − p₀`. So Cramér's
hypothesis does not satisfy `PrimeGapSqrtBound` directly.

### Numerical envelope

Computed by linear-search Python (`C·log²p` vs `2·√p + 1`):

| C (Cramér constant)      | smallest p with bound  | k₀ ≈ π(p) − 1 |
|--------------------------|-----------------------:|--------------:|
| 1.0 (Cramér original)    |                   121  |          29   |
| 1.1229 (Granville opt.)  |                   358  |          70   |

For `n ≥ 21`, iter-5 picks `k(n) = π(n²) − 1 ≥ 84`, comfortably exceeding
both thresholds. So legendre-partial's existing `n = 1..20` coverage
suffices for the finite tail under either constant choice; for `C = 1`
even `n ≤ 15` would do.

### Refined-iter-5 specification

To make iter-5 composable with Cramér, introduce a variant gated on
`p_k ≥ M` for an explicit `M : ℕ` threshold:

```lean
theorem prime_gap_sqrt_bound_above_implies_legendre
    (M : ℕ)
    (h_gap_above : ∀ k, M ≤ Nat.nth Nat.Prime k →
                   Nat.nth Nat.Prime (k+1) - Nat.nth Nat.Prime k
                     ≤ 2 * Nat.sqrt (Nat.nth Nat.Prime k) + 1)
    (h_legendre_below : ∀ n, 1 ≤ n → n^2 < 2*M → LegendreAt n) :
    LegendreConjecture
```

Proof outline (case-split on `n` ≥ 1):

- `n² < 2·M`: directly from `h_legendre_below`.
- `n² ≥ 2·M` (`n ≥ 2`): apply `Nat.bertrand` at `n²/2` to obtain a prime
  `q` with `n²/2 < q ≤ n²`. By maximality of `k := Nat.findGreatest
  (λ k, p_k ≤ n²) n²`, `p_k ≥ q > n²/2 ≥ M`, so `h_gap_above k _` gives
  the gap bound. Replay iter-5's arithmetic
  `p_{k+1} ≤ (n²−1) + 2(n−1) + 1 < (n+1)²`.

iter-5's `prime_gap_sqrt_bound_implies_legendre` is recovered as the
specialisation at `M = 0` (gap-above-0 ≡ gap-for-all-k; `n² < 0` vacuous).

Estimated +85 LOC inside `LegendrePrimeGapSqrtBoundSuffices.lean`,
0 new axioms; only new Mathlib dependency is `Nat.bertrand`.

### Axiom delta

| Before iteration 6 | After iteration 6 |
|--------------------|-------------------|
| 1 axiom (`legendre_conjecture` in `LegendrePartial.lean`) | 1 axiom (unchanged) |

No Lean changes this iteration. Audit is doc-only.

### Honest status

This iteration produces:

1. A correctness audit that identifies a real compositional gap missed by
   the previous picker.
2. A precise type signature for the refined variant that closes the gap.
3. Numerical thresholds confirming the existing finite-tail coverage is
   sufficient — no gallery extension required for the Cramér-original
   constant.

The audit *itself* is small (one observation: ∀ k vs ∀ k ≥ k₀); its
value is preventing the next ACT from hitting the same wall at Lean
compile time and having to redo ~100 LOC of structural redesign.

### Next Steps

**Iteration 7 recommendation — S5-ACT-B′**: implement the refined
variant inside `LegendrePrimeGapSqrtBoundSuffices.lean` (~85 LOC,
0 new axioms). After it lands, S5-ACT-A (real-analytic estimate) and
S5-ACT-C (Cramér composition) can proceed in either order.

## Iteration 8 Log (2026-07-24, researcher-1) — COMPLETED

Stale-BLOCKED reactivation (Docker recovered). Both queued items discharged,
Docker-verified (3094 jobs, first try):

1. **Dead `legendre_conjecture` axiom removed** (`LegendrePartial.lean`,
   slug axioms 1 → 0). The blocking docstring claim in
   `LegendreGapEquivalence.lean` was stale — the global equivalences quantify
   over the `Prop` `LegendreConjecture`, not the axiom. Four stale docstring
   spots fixed; gallery `legendre-partial` meta updated
   (`meta.axiomCount` 2 → 1 ofReduceBool-only, `leanFile.axiomCount` 1 → 0).
2. **S5-ACT-A/B/C all landed** in NEW `CramerImpliesLegendre.lean` (229 LOC,
   0 axioms, 0 sorries): `CramerConjecture` as a `Prop`;
   `eventually_mul_log_sq_le_sqrt_sub_one` (via
   `isLittleO_log_rpow_rpow_atTop`, root namespace); `exists_nat_sqrt_threshold`
   (√p < Nat.sqrt p + 1 bridge); `cramerGapBound_to_sqrt_gap` (index-threshold
   from value-threshold via `Nat.nth` strict monotonicity);
   `cramer_implies_legendre_eventually`; `cramer_exceptions_finite`;
   `cramer_reduces_legendre_to_finite` (honest strongest form — Cramér's
   constants are existential, so the tail is finite but not fixed).
   Enabled by extracting `legendreAt_of_sqrt_gap_above` (single-n large branch)
   in `LegendrePrimeGapSqrtBoundSuffices.lean`.

**Thread COMPLETED.** Iter-3..7 roadmap fully discharged; S6 (n = 21..50
enumeration) permanently deprioritized as padding. Reopen bar: materially new
mechanism. Memo:
`sessions/2026-07-24-iter8-dead-axiom-removal-cramer-composition.md`.
