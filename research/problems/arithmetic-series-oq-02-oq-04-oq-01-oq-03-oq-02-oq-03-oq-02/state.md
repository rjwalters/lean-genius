# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12 (S1)
**Iteration**: 1

## Current Focus

S1 (researcher-10): OBSERVE survey for `arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02` — the seeker-extracted child of the verified gallery entry `arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03` ("q-Multichoose: The Gaussian Binomial as q-Analog of Multiset Coefficients"). The sub-OQ asks:

> Can `qMultichoose` be generalized to a $(q,t)$-deformation (Macdonald-type) where `qMultichoose(q,t,n,k)` recovers `qMultichoose` at $t = 1$ and classical `multichoose` at $q = t = 1$? This would connect to the theory of Macdonald polynomials and Hall–Littlewood functions.

This iteration produces:

- `problem.md` — formal problem statement with full Lean target signatures (`qtBinom`, `qtMultichoose`, the three specialization theorems, and the conjectural $(q,t)$-Pascal); S2–S7 decomposition; Mathlib gap analysis.
- `knowledge.md` — historical timeline (Macdonald 1973 → 1988 → 1995, Haiman 2001); detailed specialization analysis showing $\mathrm{qtMultichoose}(q, t, 2, 2)$ is independent of $t$; risk-and-uncertainty table for S2–S6.
- `state.md` (this file) — phase NEW → OBSERVE.
- `src/data/research/problems/arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02.json` — gallery JSON.

No Lean changes in S1.

## Active Approach

**Candidate $(q,t)$-deformation** (from Macdonald 1995, §VI.6):
$$ \mathrm{qtBinom}(q, t, n, k) := \prod_{i=1}^{k} \frac{1 - q^{n+1-i} t^{i-1}}{1 - q^i t^{i-1}}, \qquad \mathrm{qtMultichoose}(q, t, n, k) := \mathrm{qtBinom}(q, t, n + k - 1, k). $$

**Key technical observation (from S1 small-case calculation)**: For $(n, k) = (2, 2)$:
$$ \mathrm{qtMultichoose}(q, t, 2, 2) = \frac{1 - q^3}{1 - q} \cdot \frac{1 - q^2 t}{1 - q^2 t} = \frac{1 - q^3}{1 - q} = 1 + q + q^2, $$
**independent of $t$**. This suggests the $(q,t)$-multichoose has more cancellation than a generic $(q,t)$-binomial; the full $t$-dependence emerges only at larger $(n, k)$.

**$(q,t)$-Pascal recurrence (S4 conjecture)**:

The form in Macdonald §VI.6 (6.4) is
$$ \binom{n+1}{k+1}_{q,t} = \binom{n}{k+1}_{q,t} + q^{n-k} \frac{1 - t^{k+1}}{1 - q^{n-k} t^k} \binom{n}{k}_{q,t} $$
which has a *rational $t$-coefficient*. At $t = 1$, the $t$-factor becomes $0/(\ldots) = 0$, so this Pascal **does not interpolate the parent's q-Pascal**.

S4's open task: find the **interpolating** $(q,t)$-Pascal, of the form
$$ \mathrm{qtMultichoose}(q, t, n+1, k+1) = \mathrm{qtMultichoose}(q, t, n+1, k) + q^{k+1} t^{a(n,k)} \cdot \mathrm{qtMultichoose}(q, t, n, k+1) $$
with the exponent $a(n, k)$ determined so that at $t = 1$ the parent's q-Pascal is recovered.

**S5 specialisation at $q = t = 1$**: the cleanest path is via the interpolating Pascal (S4 deliverable). Both numerator and denominator of each factor in the product vanish at $(1, 1)$, but the Pascal recurrence at $q = t = 1$ becomes the ordinary Pascal $\binom{n+k}{k+1} = \binom{n+k}{k} + \binom{n+k-1}{k+1}$, allowing induction.

## Blockers

None mathematical for S1 (OBSERVE iteration). Practical infrastructure:

- **`Field R` requirement**: the rational expression in `qtBinom` requires `Field R` (or a localised ring). This restricts gallery integration; the parent works over `CommRing R`.
- **Macdonald polynomial infrastructure absent from Mathlib**: any S6+ connection to $P_\lambda(x; q, t)$ must be axiomatised.
- **Interpolating $(q,t)$-Pascal exponent $a(n, k)$ is genuinely unknown**: needs S4 derivation from small cases (see `knowledge.md` for the calculation pattern).

## Next Action

**S2 (any researcher)**: Define `qtBinom` and `qtMultichoose` in `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean` with the candidate Macdonald product formula. Prove the four boundary cases (`zero_right`, `zero_left`, `one_left`, `one_right`).

Concrete plan:

```lean
import Mathlib
import Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03  -- qMultichoose

namespace QtMultichooseCoefficients

variable {R : Type*} [Field R]

noncomputable def qtBinom (q t : R) (n k : ℕ) : R :=
  ∏ i ∈ Finset.range k, (1 - q ^ (n - i) * t ^ i) / (1 - q ^ (i + 1) * t ^ i)

noncomputable def qtMultichoose (q t : R) (n k : ℕ) : R :=
  qtBinom q t (n + k - 1) k

@[simp] theorem qtMultichoose_zero_right (q t : R) (n : ℕ) :
    qtMultichoose q t n 0 = 1 := by simp [qtMultichoose, qtBinom]

@[simp] theorem qtMultichoose_one_left (q t : R) (k : ℕ) :
    qtMultichoose q t 1 k = 1 := by sorry  -- product telescopes
-- additional boundary cases
end QtMultichooseCoefficients
```

Expected ~40 Lean lines, ~3-5 sorries (boundary cases that need real proof, not heuristic).

**S3** (after S2): `qtMultichoose_at_t_eq_one : qtMultichoose q 1 n k = qMultichoose q n k` (~25 lines, 0 sorries expected).

**S4** (after S3): determine and prove the interpolating $(q,t)$-Pascal recurrence. **This is the deepest technical step** and may take 2–3 sessions.

**S5** (after S4): `qtMultichoose_at_one_one` via induction with Pascal (~30 lines).

**S6** (optional): axiomatise Macdonald polynomial principal-specialization identity.

**S7**: gallery JSON `meta.json` integration with `status: "verified"` if S5 ships clean, else `"axiomatized"`.

## Honesty

This S1 OBSERVE iteration is a **pure survey**. It produces:

- 0 new Lean theorems
- 0 sorry deltas
- 0 axiom deltas
- 3 markdown files (`problem.md`, `knowledge.md`, this `state.md`)
- 1 gallery JSON entry

The candidate $(q,t)$-deformation is from Macdonald's textbook (well-established mathematics). The Lean formalisation is genuinely new — this would be the **first Lean entry to mention Macdonald theory at any depth**. The deepest technical step (S4 — interpolating $(q,t)$-Pascal) is research-grade: the conventional Macdonald Pascal does NOT specialise to the parent's q-Pascal at $t = 1$, so a new normalisation must be derived.

The future Lean entry will be `status: "verified"` if S5 ships without axioms; `"axiomatized"` if a real-analytic limit axiom or Macdonald-polynomial axiom is required.
