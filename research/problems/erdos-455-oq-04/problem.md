# Problem: Prime sequences with AP-gaps (generalization of Erdős #455)

**Slug**: `erdos-455-oq-04`
**Parent**: `erdos-455` (verified entry: "Erdős Problem #455: Monotone Prime Gap Sequences")
**Source**: seeker-extracted from `src/data/proofs/erdos-455/meta.json`, `conclusion.openQuestions[3]`.
**Created**: 2026-05-12 (S1 OBSERVE by researcher-10)

## Statement

### Parent open question (verbatim)

> Can the problem be generalized to other arithmetic conditions on gaps (e.g., gaps forming an arithmetic progression)?

### Plain language

The parent `erdos-455` studies sequences of primes $q_1 < q_2 < \ldots$ whose consecutive gaps $g_n := q_{n+1} - q_n$ are **non-decreasing** ($g_n \ge g_{n-1}$). Richter 1976 proves $\liminf q_n / n^2 > 0.352$; Erdős conjectured $\lim q_n / n^2 = \infty$.

This sub-OQ asks the natural generalization: **what if the gaps $g_n$ themselves form an arithmetic progression?** I.e., the *second-order gaps* $g_{n+1} - g_n$ are constant.

Two natural specializations:

1. **Constant-gap** ($g_n = g_{n+1}$): the primes themselves are in arithmetic progression. This is the **Green–Tao theorem** territory (Ben Green & Terence Tao, *Annals of Math* 2008): the primes contain arbitrarily long arithmetic progressions.

2. **AP-gap** ($g_{n+1} - g_n = d$ constant for some $d \in \mathbb{Z}$): the gaps form an AP with common difference $d$. If $d = 0$, this reduces to case (1). If $d > 0$, this is the parent's *strictly increasing* gap condition. If $d < 0$, this would require eventually negative gaps, contradicting $q_{n+1} > q_n$; so only finitely many terms possible.

The interesting *new* case is therefore $d > 0$ (strictly increasing gap differences), which is a **strict refinement of the parent's monotone-gap condition**:

$$ \mathrm{ConstantGap} \subsetneq \mathrm{APGap}_{d > 0} \subsetneq \mathrm{MonotoneGap} \subsetneq \mathrm{AllStrictlyIncreasingPrimes}. $$

### Formal Lean target signatures

```lean
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Proofs.Erdos455Problem  -- parent

namespace Erdos455OQ04

/-- A sequence has **AP-gaps with common difference d** if consecutive gap differences are d. -/
def HasAPGaps (q : ℕ → ℕ) (d : ℤ) : Prop :=
  ∀ n, (q (n + 2) : ℤ) - 2 * (q (n + 1) : ℤ) + (q n : ℤ) = d

/-- An AP-gap prime sequence: strictly increasing primes whose gaps form an AP. -/
structure APGapPrimeSeq (d : ℤ) where
  seq : ℕ → ℕ
  strictMono : StrictMono seq
  allPrime : ∀ n, (seq n).Prime
  apGaps : HasAPGaps seq d

/-- **Constant gap = primes in AP**: an APGapPrimeSeq with d = 0 means consecutive
gaps are equal, i.e., the primes are in arithmetic progression. -/
theorem apGap_zero_iff_prime_AP (q : ℕ → ℕ) :
    HasAPGaps q 0 ↔ ∀ n, q (n + 2) - q (n + 1) = q (n + 1) - q n := by
  unfold HasAPGaps
  constructor <;> intro h n <;> have := h n <;> omega

/-- **Green-Tao (axiom)**: the primes contain arbitrarily long arithmetic progressions.
Equivalently: for every k, there exists q : Fin k → ℕ that is an APGapPrimeSeq 0 prefix. -/
axiom green_tao : ∀ k : ℕ, ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n < k, (q n).Prime) ∧
  ∀ n < k - 1, q (n + 1) - q n = q 1 - q 0

/-- **AP-gap subsumes monotone-gap (in the positive direction)**: if d ≥ 0 and the
sequence has AP-gaps with common difference d, then gaps are non-decreasing. -/
theorem apGap_subsumes_monotone {q : ℕ → ℕ} {d : ℤ} (hd : d ≥ 0) (h : HasAPGaps q d) :
    ∀ n, (q (n + 1) : ℤ) - q n ≥ (q n : ℤ) - q (n - 1) := by
  sorry  -- direct from definition + induction (S2 deliverable)

/-- **Growth lower bound for AP-gap prime sequences (conjectural)**:
for any AP-gap prime sequence with d ≥ 0, q_n grows at least cubically: q_n = Ω(n^3).
Reasoning: gaps grow linearly (g_n = g_0 + n·d, so g_n ≍ n for d > 0), so q_n ≍ n^2 by
telescoping, but with prime-density constraints (Vinogradov/Heath-Brown) the bound
likely strengthens to n^3. -/
axiom apGap_growth_lower_bound :
    ∀ d : ℤ, d > 0 →
    ∀ q : APGapPrimeSeq d, ∃ c : ℝ, c > 0 ∧
    Filter.Tendsto (fun n => (q.seq n : ℝ) / (n : ℝ) ^ 3) Filter.atTop (Filter.atTop)
    -- or stronger
end Erdos455OQ04
```

## Classification

```yaml
tier: B
significance: 6
tractability: 4
tags:
  - seeker-selected
  - erdos-problem
  - number-theory
  - prime-gaps
  - arithmetic-progression
  - green-tao
  - sequences
  - mathlib-gap
```

**Significance**: 6/10 — Erdős-numbered; direct extension of parent. The constant-gap case is **Green–Tao**, a major modern theorem. The AP-gap case ($d > 0$) is genuinely novel and to the author's knowledge has not been published.

**Tractability**: 4/10 — Mixed:

- **S2 definitions and structure** are trivial (~30 Lean lines).
- **S3 subsumption proofs** (monotone-gap ⊂ AP-gap with $d \ge 0$): elementary, ~15 lines.
- **Green–Tao axiom** (S5): well-defined statement, axiomatised.
- **Growth lower bound for AP-gap** (S4): research-grade, axiomatised. The exponent (cubic? quartic?) is not in the literature.
- **Concrete examples** (S6): construct $\{q_n\}$ with AP-gaps and verify primality.

## Decomposition

### S2 — Define `APGapPrimeSeq` structure (constant-gap and general-d)

**Deliverable**: `proofs/Proofs/Erdos455OQ04.lean` with the `APGapPrimeSeq d` structure and basic facts:

```lean
def HasAPGaps (q : ℕ → ℕ) (d : ℤ) : Prop := ...
structure APGapPrimeSeq (d : ℤ) where ...
theorem apGap_zero_iff_prime_AP : ...
theorem apGap_subsumes_monotone : d ≥ 0 → HasAPGaps q d → HasNonDecreasingGaps q
```

Expected ~50 Lean lines, no sorries.

### S3 — Constant-gap (d = 0) ⇔ primes in AP

Direct equivalence proof. ~10 lines.

### S4 — AP-gap growth bound (axiomatised)

```lean
axiom apGap_growth_lower_bound : ∀ d > 0, ∀ q : APGapPrimeSeq d,
  ∃ c > 0, ∀ᶠ n in atTop, q.seq n ≥ c * (n : ℝ) ^ 3
```

The cubic exponent is the author's conjecture; rigorous derivation would require prime-density estimates beyond Mathlib.

### S5 — Green–Tao axiom + connection

Axiomatize the Green–Tao theorem (long APs in the primes) and derive that APGapPrimeSeq 0 sequences of any length exist (parametrically).

### S6 — Concrete witnesses

Construct small examples:

- $\{5, 11, 17, 23\}$: 4 primes in AP with gap 6 ($d = 0$).
- $\{3, 5, 11, 23\}$: gaps $2, 6, 12$ — these are NOT in AP (differences 4, 6).
- $\{3, 11, 23\}$: gaps $8, 12$ — second-difference 4 (AP with $d = 4$). Verify primality.
- Search the first 1000 primes for APGap-3 sequences with $d \in \{2, 4, 6\}$.

### S7 — Gallery integration

`src/data/proofs/erdos-455-oq-04/` with `status: "axiomatized"`, `axiomCount: 2-3` (Green-Tao + growth bound + possibly Richter).

## Mathlib Infrastructure Map

| Need | Mathlib | Module |
|------|---------|--------|
| `Nat.Prime` | ✅ | `Mathlib.Data.Nat.Prime.Basic` |
| `StrictMono` | ✅ | `Mathlib.Order.Monotone.Basic` |
| `Filter.Tendsto`, `Filter.atTop` | ✅ | `Mathlib.Order.Filter.AtTopBot.Basic` |
| Green–Tao theorem | ❌ | n/a |
| Richter 1976 | ❌ (parent axiomatises) | n/a |
| Heath-Brown bound on prime AP-density | ❌ | n/a |
| 3-APs in primes (van der Corput) | ⚠️ partial via `Mathlib.NumberTheory.LSeries.Dirichlet` | not directly applicable |

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `erdos-455` (direct parent) | Monotone-gap framework + Richter axiom |
| `green-tao` | Long APs in primes (if it exists in gallery) |
| `dirichlets-theorem` | Primes in AP (infinitude) |
| `bounded-prime-gaps-oq-03-oq-02` | Adjacent prime-gap research |
| `infinitude-primes-4k1` / `4k3` | Density of primes mod 4 (subcase) |

## Risk Notes

- **Green–Tao is a major theorem** — Mathlib does not have it. The S5 axiomatic statement must cite Green & Tao, *Annals of Math.* 167 (2008).
- **AP-gap growth bound** (S4) is the author's conjecture; no published result. The cubic exponent comes from a heuristic: $g_n = g_0 + n d \asymp n$, so $q_n \asymp \sum_k k = n^2$; tightening to $n^3$ requires careful primality constraints (the author's intuition; needs verification).
- **`status: "axiomatized"` is mandatory** — Green–Tao alone forces this.
- **Sibling sub-OQs**: `erdos-455-oq-01, oq-02, oq-03` ask different questions (whether $\lim q_n/n^2 = \infty$, the exact Richter constant, counting monotone-gap sequences from a fixed start). None overlap with this AP-gap generalization.

## References

- Erdős, *Some remarks on prime numbers and prime gaps*, J. Indian Math. Soc. 5 (1941).
- Richter, *Über die Monotonie von Differenzenfolgen*, Acta Arith. 28 (1975/76), 117–122.
- Green & Tao, *The primes contain arbitrarily long arithmetic progressions*, Annals of Math. 167 (2008), 481–547.
- van der Corput, *Über Summen von Primzahlen und Primzahlquadraten*, Math. Ann. 116 (1939) — 3-APs in primes (precursor to Green–Tao).
- Heath-Brown, *Three primes and an almost-prime in arithmetic progression*, J. London Math. Soc. (1981).
- OEIS [A005115](https://oeis.org/A005115) — primes in AP with common difference 6 (constant-gap subcase).
- erdosproblems.com/455 — parent problem source.

## Honesty

This S1 OBSERVE is a **survey + decomposition**. It produces:

- 0 new Lean theorems
- 0 sorry/axiom deltas
- 3 markdown files
- 1 gallery JSON

The constant-gap subcase ($d = 0$) is **Green–Tao**, a deep theorem absent from Mathlib. The general AP-gap case ($d > 0$) is a *new* mathematical question to the author's knowledge — the cubic growth bound is conjectural.

Future Lean entry: `status: "axiomatized"` (Green-Tao is non-negotiable).
