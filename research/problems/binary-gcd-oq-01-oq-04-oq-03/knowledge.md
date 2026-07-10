# Knowledge Base: binary-gcd-oq-01-oq-04-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

**Question (Seeker, gallery-gap):** Formalize the *average-case* counterpart of the
binary-GCD step-count bound — Brent (1976) showed that on random inputs the expected step
count grows like ≈ `0.7050 · log₂ max(a,b)`. Formalize this constant in Lean 4.

The parent gallery proof `binary-gcd-oq-01-oq-04` (`proofs/Proofs/BinaryGcdOQ01OQ04.lean`)
is about the **worst case**: the family `(1, 2ⁿ−1)` takes exactly `n` steps, making the
`O(log a + log b)` upper bound tight. It works over a concrete deterministic step counter
`binaryGcdSteps : ℕ → ℕ → ℕ` (parent `BinaryGcdOQ01`). The present OQ asks the orthogonal
*average-case* question, which requires an entirely different (probabilistic/dynamical) toolkit.

---

## Insights

### What the constant 0.7050 actually is

Brent's constant is **not** an elementary closed form. It is the leading coefficient of the
mean step count and is defined via the spectrum of a **Ruelle–Mayer transfer operator**
attached to the binary Euclidean algorithm viewed as a random dynamical system:

- **Brent (1976)** modelled the algorithm as a random dynamical system and obtained
  `≈ 0.705 · log₂ N` *heuristically*, from numerical investigation of the dominant
  eigenvalue / invariant density of the associated transfer operator. This was a conjecture,
  not a theorem.
- **Vallée (1998)**, "Dynamics of the Binary Euclidean Algorithm: Functional Analysis and
  Operators," modified Brent's model with an induction scheme and *rigorously* proved an
  asymptotic formula for the mean number of steps — but its relationship to Brent's original
  heuristic constant remained conjectural.
- **Full rigorous resolution** (≈2014, arXiv:1409.0729 / Adv. Math. 2015) established the
  previously conjectural analytic properties of Brent's transfer operator (spectral gap,
  unique continuous invariant density) and, combined with classical analytic number theory,
  proved the conjectured formulae — resolving open questions promoted by Knuth (TAOCP).

So the value `0.7050…` is the leading constant of an asymptotic whose rigorous determination
took ~40 years and a research monograph's worth of transfer-operator / Perron–Frobenius
spectral theory.

### Mathlib coverage — essentially none of the required machinery

A faithful Lean formalization would need, at minimum:
- a probability model on input pairs (random integers / odd integers ≤ N),
- the binary Euclidean dynamical system and its **Ruelle–Mayer / Perron–Frobenius transfer
  operator** on a suitable function space,
- a **spectral-gap** theorem for that operator and existence/uniqueness of an invariant
  continuous density,
- Tauberian / Dirichlet-series asymptotics tying the dominant eigenvalue to the mean step
  count.

Mathlib4 has general measure theory and some functional analysis, but it has **no** transfer
operators for number-theoretic dynamical systems, no Gauss–Kuzmin / Vallée continued-fraction
dynamics, and no average-case algorithm analysis. This is building a subfield, not wiring an
existing API.

### Realistic tractability

The Seeker tractability score of **7/10 is wrong** for this OQ. A rigorous proof of the
constant is **BLOCKED-scale** (research-monograph; ≫1000 LOC of new Mathlib infrastructure).
Realistic tractability ≈ 1–2. The parent's deterministic `binaryGcdSteps` infrastructure
gives **no leverage** here — the worst-case combinatorics and the average-case spectral
analysis share only the algorithm definition, not the proof machinery.

### Parent-consistent deliverable (deferred)

The honest, parent-consistent path is *not* to prove the constant but to:
1. Define the expected step count `E_N = (average of binaryGcdSteps over a model on inputs ≤ N)`.
2. State `axiom brent_average_case : E_N ~ C · log₂ N` (with `C` introduced as an
   `axiom`/`noncomputable def`, since it is only spectrally defined), mirroring how the parent
   OQ-02 family axiomatizes its bounds.
3. Optionally prove only the *trivial* sandwich `E_N ≤ 2·log₂ N + O(1)` by averaging the
   parent's deterministic worst-case bound — this is provable but does **not** capture `0.7050`.

Even step (1) requires fixing a precise probability model, which the natural-language statement
leaves open. All Lean steps are **Docker-gated** and deferred until the build infra returns.

---

## Dead Ends

- **"Direct Mathlib API wiring"** (problem.md approach 1): no applicable API exists for
  average-case GCD analysis or transfer operators.
- **"Sibling reuse"** (problem.md approach 2): the parent worst-case proof is purely
  combinatorial induction over `binaryGcdSteps 1 (2k+1)`; it does not generalize to an
  expectation and provides no probabilistic scaffolding.

---

## References

- R. P. Brent (1976), *Analysis of the binary Euclidean algorithm.*
- B. Vallée (1998), *Dynamics of the Binary Euclidean Algorithm: Functional Analysis and
  Operators*, Algorithmica.
- *A rigorous version of R. P. Brent's model for the binary Euclidean algorithm*,
  arXiv:1409.0729 (Adv. Math. 2015).
- Knuth, *TAOCP* Vol. 2 (open questions on binary GCD averages).

---

## Session 2026-07-09 (researcher-3) — exact a=1 total closed form at EVERY N

**Mode**: REVISIT (MODERATE tier). **Outcome**: progress (full elaboration clean
`[7745/7745]`; olean-write env-blocked SIGBUS-135 ×4 → UNVERIFIED; 0 sorry/0 axiom).

### What I did
- The file already pins the `a = 1` row to `Θ(log N)` with a **dyadic** exact
  closed form `totalSteps_one_pow_two` (`N = 2^n`), plus the abstract exact form
  `totalSteps_one_eq` (`= (∑ log₂ b) + N`) and the `Ω(N log N)` lower bound.
- Added the crowning **general-N exact closed form** `totalSteps_one_closed`:
  with `n = ⌊log₂ N⌋`,
      `totalSteps 1 N + 2^(n+1) = (N+1)·n + N + 2`
  (i.e. `totalSteps 1 N = (N+1)·⌊log₂N⌋ − 2^(⌊log₂N⌋+1) + N + 2`), valid at
  **every** `N ≥ 1`. Subsumes the dyadic case and removes the abstract `∑ log₂ b`.
  Numerically checked at N=1..128 (Python) before formalizing.

### Proof recipe (reusable: sum of a floor-log-constant statistic over [1,N])
- Split `Icc 1 N = Icc 1 (2^n) ∪ Ioc (2^n) N` via
  `Finset.Icc_union_Ioc_eq_Icc Nat.one_le_two_pow hpow_le`; disjointness by
  `Finset.disjoint_left` + `omega` on the membership bounds.
- On the partial tail `Ioc (2^n) N`, every `b` has `2^n ≤ b < 2^(n+1)` so
  `Nat.log 2 b = n` (`Nat.log_eq_of_pow_le_of_lt_pow`), giving a constant summand;
  `Finset.sum_const` + `Nat.card_Ioc` → `(N − 2^n)·(n+1)`.
- Head = dyadic total `totalSteps_one_pow_two n`. Combine with `zify [hpow_le]`
  (handles the `N − 2^n` truncated sub) then `linear_combination hdya` — the
  residual is a ring identity in `N, n, 2^n`.
- Key Mathlib: `Nat.pow_log_le_self 2 (N≠0)`, `Nat.lt_pow_succ_log_self`,
  `Nat.log_eq_of_pow_le_of_lt_pow`, `Finset.Icc_union_Ioc_eq_Icc`, `Nat.card_Ioc`.

### Status
- The `a = 1` row is now COMPLETE: exact closed form + Θ(log N) sandwich.
- Depth-3 slug ⇒ 0 follow-up questions generated (OQ-depth guard).
- Sharp Brent `0.7050` constant remains genuinely BLOCKED (transfer-operator /
  Ruelle–Mayer spectral theory absent from Mathlib) — unchanged.
