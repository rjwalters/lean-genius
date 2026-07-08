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

## Increment (researcher-2, 2026-07-08 session 2)

Added the missing **ℚ average lower bound** so the a=1 Θ(log N) is now stated in a
single normalised quantity (previously the ceiling `avgSteps_le` was in ℚ but the
matching lower bound `totalSteps_one_ge` was in ℕ). New (VERIFIED, 0 sorry/0 axiom,
no native_decide; build 7745 jobs, exit 0 on retry after one environmental exit-135):

- `avgSteps_one_ge (hN : 0 < N) : (log₂ N − 1)/2 ≤ (totalSteps 1 N)/N`
  — divide `totalSteps_one_ge` by N, using `N − ⌊N/2⌋ = ⌈N/2⌉ ≥ N/2` (i.e.
  `2·⌊N/2⌋ ≤ N`). Two cases: `log₂N = 0` (LHS = −1/2 ≤ 0 ≤ RHS), else clear
  denominators via `div_le_iff₀`/`le_div_iff₀` and close with `nlinarith` given the
  product hint `0 ≤ (log₂N−1)·(N−2⌊N/2⌋)`.
- `avgSteps_one_theta (hN : 0 < N) : (log₂ N − 1)/2 ≤ avg ∧ avg ≤ 2·log₂ N + 2`
  — packages both ℚ bounds; upper half = `avgSteps_le 1 N` with `Nat.log 2 1 = 0`.

This is the honest capstone of the ORDER result; the sharp 0.7050 constant stays
BLOCKED-scale (transfer-operator spectral theory absent from Mathlib). At OQ depth 3
→ no follow-up questions generated (depth guard).

Gotchas confirmed: `Nat.cast_sub` needs the `≤` side proof for each truncated ℕ
subtraction (`N/2 ≤ N`, `1 ≤ log₂N`); the current-name divide-lemmas are the `₀`
variants (`div_le_iff₀`, `le_div_iff₀`), not the deprecated non-`₀` forms.
