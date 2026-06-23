# Knowledge Base: Euler's Converse for Even Perfect Numbers

## Status: S1 OBSERVE (survey + plan, no Lean changes yet)

## Mathlib API Inventory

### Core definitions
- `Nat.Perfect n` — `(∑ i ∈ n.divisors, i) = 2 * n` (proper-divisor form: `σ(n) - n = n`).
- `ArithmeticFunction.sigma k n` — `∑ d ∈ n.divisors, d^k`; we use `σ 1 = σ`.
- `Nat.mersenne p` — `2^p - 1`; Mersenne prime when `(mersenne p).Prime`.

### Key Mathlib lemmas (already available)
| Lemma | Statement (informal) |
|---|---|
| `Nat.perfect_iff_sum_divisors_eq_two_mul` | `0 < n → (n.Perfect ↔ ∑_{d ∣ n} d = 2n)` |
| `ArithmeticFunction.IsMultiplicative.sigma_one` | `σ 1` is multiplicative (over coprime args) |
| `Nat.sigma_one_apply` | `σ 1 n = ∑ d ∈ n.divisors, d` |
| `Theorems100.Nat.sigma_two_pow_eq_mersenne_succ` | `σ 1 (2^k) = mersenne (k+1)` (proven in Archive) |
| `Theorems100.Nat.perfect_two_pow_mul_mersenne_of_prime` | **Euclid direction** (in Archive) |
| `Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect` | **Euler direction** (bundled proof in Archive) |
| `Theorems100.Nat.even_and_perfect_iff` | **Complete equivalence** (in Archive) |

### Coprime + prime-power infrastructure
- `Nat.Coprime.pow_right`, `Nat.Coprime.pow_left` — coprimality of powers.
- `Nat.Coprime` — Mathlib `Nat.Coprime a b ↔ Nat.gcd a b = 1`.
- `Nat.Odd.coprime_two_pow` (or equivalent) — odd numbers are coprime to powers of 2.
- `Nat.sigma_one_prime` — `σ 1 p = p + 1` when `p.Prime`.

## Proof Skeleton (Euler ⇒ direction)

Let `n > 0` be even and perfect. Write `n = 2^k · m` with `m` odd and `k ≥ 1`.

### Step 1 — Coprime decomposition
**Goal**: `σ(2^k · m) = σ(2^k) · σ(m)`.
- Apply `IsMultiplicative.sigma_one` with hypothesis `Coprime (2^k) m` (from `m` odd).
- Mathlib helper: `Nat.Coprime.pow_left` or `Odd.coprime_two_pow`.

### Step 2 — Power identity
**Goal**: `σ(2^k) = 2^(k+1) - 1 = M_{k+1}`.
- Directly from `Theorems100.Nat.sigma_two_pow_eq_mersenne_succ k`.

### Step 3 — Perfect-equation expansion
**Goal**: `M_{k+1} · σ(m) = 2^(k+1) · m`.
- From `n.Perfect` and Step 1: `σ(2^k) · σ(m) = 2 · (2^k · m) = 2^(k+1) · m`.
- Substitute Step 2.

### Step 4 — Divisibility extraction
**Goal**: `M_{k+1} ∣ m` (since `gcd(M_{k+1}, 2^(k+1)) = 1` as `M_{k+1}` is odd).
- `M_{k+1} = 2^(k+1) - 1` is odd, so coprime to `2^(k+1)`.
- From Step 3: `M_{k+1} · σ(m) = 2^(k+1) · m` and `Coprime M_{k+1} (2^(k+1))` gives `M_{k+1} ∣ m`.
- Write `m = M_{k+1} · c` for some `c ≥ 1`.

### Step 5 — Substitution + bound
**Goal**: `σ(m) = 2^(k+1) · c` and `c < m`.
- From Step 3 with `m = M_{k+1} · c`: `M_{k+1} · σ(m) = 2^(k+1) · M_{k+1} · c`, so `σ(m) = 2^(k+1) · c`.
- Note `2^(k+1) · c = (M_{k+1} + 1) · c = m + c`. So `σ(m) = m + c`.

### Step 6 — Two-divisor lemma forces primality + `c = 1`
**Goal**: `c = 1` and `m` prime (hence `m = M_{k+1}` is a Mersenne prime).
- `σ(m) = m + c` and `c ∣ m` (since `m = M_{k+1} · c`).
- For `m > 1`, the divisors of `m` always include at least `1` and `m`; their sum is at least `1 + m`.
- So `m + c ≥ 1 + m`, i.e., `c ≥ 1`. Equality forces divisor set `= {c, m}` and `c = 1` (since `1` must appear).
- Thus `c = 1`, `m = M_{k+1}`, and `m` has exactly two divisors → `m.Prime`.

### Step 7 — Conclusion
- `n = 2^k · m = 2^k · M_{k+1}` with `M_{k+1}.Prime`. ∎

## Comparison to Mathlib Archive

The Archive proof `eq_two_pow_mul_prime_mersenne_of_even_perfect` performs essentially
the same steps in a single ~80-line block. The pedagogical refactor would:
1. Introduce named lemmas for Steps 1, 2, 4, 5, 6 (Step 3 is a direct rewrite, Step 7 a conjunction).
2. Add docstrings explaining the algebraic intuition.
3. Verify in our build (`docker-build.sh Proofs.SumOfDivisorsOQ02`).

## Mathlib Gaps Identified

None that block S2 ACT. All lemmas needed for Steps 1–7 are either in Mathlib core
(`Coprime`, `IsMultiplicative`, `Nat.divisors`) or in the Archive (`sigma_two_pow_eq_mersenne_succ`).

The Archive import (`import Archive.Wiedijk100Theorems.PerfectNumbers`) is already
working in `PerfectNumbers.lean` and would be reused here.

## Risks and Open Decisions

- **Risk**: The pedagogical refactor may end up structurally identical to the Archive
  proof, providing limited gallery value. Mitigation: prioritize naming + docstrings
  over algebraic novelty; treat as documentation contribution.
- **Decision deferred to S2 ACT**: Whether to write `Proofs/SumOfDivisorsOQ02.lean` from
  scratch, or extend `PerfectNumbers.lean` with named intermediate lemmas. Default plan:
  separate file to keep the bundled `euler_even_perfect` wrapper intact.

## References

- Euler, L. (1747). "De numeris amicabilibus" (posthumous, 1849). Opera Postuma 1, 85–100.
- Euclid (~300 BCE). *Elements*, Book IX, Proposition 36.
- Hardy, G.H. & Wright, E.M. (1979). *An Introduction to the Theory of Numbers*, §16.8.
- Mathlib Archive: `Archive.Wiedijk100Theorems.PerfectNumbers` (Wiedijk #70).
- Keith Conrad. "Perfect Numbers and Mersenne Primes." UConn expository notes.

## Scouting Log

### S1 OBSERVE (2026-05-12, researcher-12)

**Mode**: Survey + plan; no Lean changes.

**Findings**:
- Parent slug `sum-of-divisors` is marked COMPLETED (skipped in favor of `PerfectNumbers.lean`).
- `PerfectNumbers.lean` already wraps the Archive's bundled Euler converse via `euler_even_perfect`.
- The OQ-02 framing (per seeker note: "sigma_mul_coprime + prime-power structure") proposes a
  *self-contained* pedagogical proof with named intermediate steps, not a re-wrapping.

**S2 plan**: Scaffold `Proofs/SumOfDivisorsOQ02.lean` with:
- Section per step (Steps 1–6 above) — each step as a named lemma with `sorry`.
- Top-level theorem `euler_converse_self_contained` combining the steps.
- Gallery entry `src/data/proofs/sum-of-divisors-oq-02/` with annotations.

**Honesty note**: If S2 build reveals the named decomposition is nearly identical to the
Archive proof's internal structure, the contribution is *documentation-only* (rename + docstrings)
and the slug should be closed as "covered-by-parent / pedagogical-only" after one or two
iterations, not pursued as multi-session research.
