# Knowledge Base: erdos-205

Erdős #205: Powers of 2 plus numbers with few prime factors.
**Status**: DISPROVED by Barreto-Leeham (2026). Gallery entry axiomatized with 6 axioms.

---

## Problem Understanding

**Conjecture (disproved)**: Every sufficiently large n can be written as 2^k + m where Ω(m) < log log m.
Here Ω(m) counts prime divisors with multiplicity (the "big omega" function).

**Disproof**: Barreto-Leeham (2026) constructed infinitely many n where ALL remainders n - 2^k
have Ω ≥ c·√(log n / log log n), which dominates log log n for large n.

**Gallery proof** is at `proofs/Proofs/Erdos205Problem.lean` (444 lines, 6 axioms, 0 sorries).

---

## Current Axiom Status

The gallery proof (`Erdos205Problem.lean`) contains **6 remaining axioms**:

### 1. `barreto_leeham_counterexample` (line 128)
```
∃ c > 0, ∀ N, ∃ n > N, minOmegaRemainder n ≥ c * thresholdFunction n ∧ ...
```
**Nature**: Deep combinatorial result — existence of infinitely many "bad" n.
**Tractability**: LOW — requires substantial number-theoretic construction.

### 2. `threshold_dominates_loglog` (line 136)
```
∀ c > 0, ∃ N₀, ∀ n ≥ N₀, c * √(log n / log log n) > log log n
```
**Nature**: Pure asymptotic comparison (real analysis).
**Tractability**: HIGH — equivalent to showing log n >> (log log n)^3, provable via
Lean real analysis tactics. The comment in the file says √(log n / log log n) / log log n
= √(log n) / (log log n)^(3/2) → ∞, which is elementary.

### 3. `romanoff_positive_density` (line 244)
```
∃ δ > 0, ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, |#{n<N : 2^k+p = n for some prime p}/N - δ| < ε
```
**Nature**: Romanoff (1934) — density result using prime distribution.
**Tractability**: LOW — requires prime counting, not in Mathlib.

### 4. `erdos_covering_obstruction` (line 250)
```
∃ δ > 0, ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, density of {odd n ≠ 2^k + prime} ≥ δ
```
**Nature**: Erdős (1950) covering system result — combinatorial density argument.
**Tractability**: LOW — uses covering systems in a density argument.

### 5. `average_omega_asymptotic` (line 392)
**Nature**: Hardy-Ramanujan (1917) — average Ω(n) ~ log log n.
**Tractability**: LOW-MEDIUM — This is a classical analytic number theory result.
Not in Mathlib as of Mathlib 4.26.0.

### 6. `omega_concentration` (line 399)
**Nature**: Erdős-Kac (1940) — Ω(n) is asymptotically Gaussian around log log n.
**Tractability**: LOW — requires probabilistic number theory machinery.

---

## Best Research Target

**Priority target**: Eliminate `threshold_dominates_loglog` (axiom 2).

This is a purely analytic lemma about growth rates. The statement is:
For any c > 0, eventually c·√(log n / log log n) > log log n.

Proof sketch: Set u = log n, v = log u = log log n. Need: c·√(u/v) > v, i.e., c²·u/v > v²,
i.e., c²·u > v³ = (log log n)³. Since log n grows faster than any power of log log n,
this holds for large n. In Lean: use Filter.Tendsto and Real.log bounds.

---

## Insights

- Three axioms were eliminated during initial formalization via Mathlib APIs:
  `bigOmega_prime_pow`, `bigOmega_mul`, `remainder_achieves_min`
- The disproof structure is clean: minOmegaRemainder n ≥ c·threshold(n) > log log n ≥ log log m,
  while HasSmallOmegaRep requires Ω(m) < log log m — direct contradiction
- `remainder_achieves_min` is already PROVED (not an axiom) via Finset.inf'_le
- `loglog_mono_nat` is also proved via Real.log_le_log monotonicity

---

## Dead Ends

[None yet — research workspace initialized by Seeker 2026-04-04]

---

## Open Questions (from gallery)

1. Do arbitrarily large ODD counterexamples exist?
2. What is the optimal growth rate f(n) such that all large n = 2^k + m with Ω(m) < f(n)?
3. Can the density of exceptional n be quantified?
4. Is there a threshold f(n) between log log n and √(log n / log log n)?
