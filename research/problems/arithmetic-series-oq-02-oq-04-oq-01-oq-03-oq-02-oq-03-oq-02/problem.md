# Problem: (q,t)-deformation of qMultichoose (Macdonald-style)

**Slug**: `arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02`
**Parent**: `arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03` (verified entry: "q-Multichoose: The Gaussian Binomial as q-Analog of Multiset Coefficients")
**Source**: seeker-extracted from `src/data/proofs/.../meta.json`, `conclusion.openQuestions[1]`.
**Created**: 2026-05-12 (S1 OBSERVE by researcher-10)

## Statement

### Parent open question (verbatim)

> Can qMultichoose be generalized to a (q,t)-deformation (Macdonald-type) where qMultichoose(q,t,n,k) recovers qMultichoose at t=1 and classical multichoose at q=t=1? This would connect to the theory of Macdonald polynomials and Hall-Littlewood functions.

### Plain language

The parent proves $\mathrm{qMultichoose}(q, n, k) := \binom{n+k-1}{k}_q$ is the natural $q$-analog of the ordinary multichoose coefficient $\binom{n+k-1}{k}$, satisfies a $q$-Pascal recurrence, and recovers the integer multichoose at $q = 1$.

This sub-OQ asks: **does the natural Macdonald-style $(q,t)$-deformation $\mathrm{qtMultichoose}(q, t, n, k)$ exist, and does it satisfy:**

1. $\mathrm{qtMultichoose}(q, 1, n, k) = \mathrm{qMultichoose}(q, n, k)$ (Hall–Littlewood-type specialization),
2. $\mathrm{qtMultichoose}(1, 1, n, k) = \mathrm{multichoose}(n, k)$ (classical specialization),
3. a $(q,t)$-Pascal recurrence generalizing the parent's $q$-Pascal,
4. connection to Macdonald polynomial principal specializations?

### Candidate definition (S1 proposal)

The **Macdonald $(q,t)$-binomial coefficient** (Macdonald 1995, *Symmetric Functions and Hall Polynomials*, ch. VI §6) is
$$ \binom{n}{k}_{q,t} := \prod_{i=1}^{k} \frac{1 - q^{n+1-i} t^{i-1}}{1 - q^i t^{i-1}}, $$
defined as a rational function in $q, t$. At $t = 1$, this reduces to the Gaussian binomial $\binom{n}{k}_q = \prod_{i=1}^k \frac{1 - q^{n+1-i}}{1 - q^i}$. At $q = t = 1$, both numerator and denominator have simple zeros; the limit is the integer binomial coefficient $\binom{n}{k}$ (computable via L'Hôpital / repeated cancellation).

The candidate $(q,t)$-deformation is therefore
$$ \mathrm{qtMultichoose}(q, t, n, k) := \binom{n+k-1}{k}_{q,t} = \prod_{i=1}^{k} \frac{1 - q^{n+k-i} t^{i-1}}{1 - q^i t^{i-1}}. $$

### Formal target signatures (Lean 4)

```lean
import Mathlib
import Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03  -- qMultichoose

namespace QtMultichooseCoefficients

variable {R : Type*} [Field R]  -- field for division

/-- The Macdonald (q,t)-binomial coefficient.

    `qtBinom q t n k := ∏ i ∈ Finset.range k, (1 - q^(n+1-i) * t^i) / (1 - q^(i+1) * t^i)`

    Defined as a rational expression. At t=1 reduces to qBinom q n k. -/
noncomputable def qtBinom (q t : R) (n k : ℕ) : R :=
  ∏ i ∈ Finset.range k, (1 - q ^ (n - i) * t ^ i) / (1 - q ^ (i + 1) * t ^ i)
  -- careful with index shift; the standard Macdonald convention uses
  -- (n+1-i) in numerator and (i) in denominator (1-indexed).

/-- The (q,t)-multichoose coefficient. -/
noncomputable def qtMultichoose (q t : R) (n k : ℕ) : R :=
  qtBinom q t (n + k - 1) k

/-- **Specialization to t = 1**: recovers qMultichoose. -/
theorem qtMultichoose_at_t_eq_one (q : R) (n k : ℕ) :
    qtMultichoose q 1 n k = qMultichoose q n k := by
  sorry  -- requires simplification of (1 - q^_ · 1^_) / (1 - q^_ · 1^_) = (1 - q^_) / (1 - q^_)

/-- **Specialization to q = t = 1**: recovers multichoose (as a real). -/
theorem qtMultichoose_at_one_one (n k : ℕ) :
    qtMultichoose (1 : R) (1 : R) n k = (Nat.multichoose n k : R) := by
  sorry  -- requires limit computation (q,t) → (1,1) of 0/0 form; use cancellation

/-- **(q,t)-Pascal recurrence (conjectural form)**:

    qtMultichoose q t (n+1) (k+1) =
      qtMultichoose q t (n+1) k
    + q^(k+1) · t^? · qtMultichoose q t n (k+1)

    The exact t-weight is not immediate from the parent's q-Pascal; this
    is the principal CONJECTURE for S2 to verify. -/
theorem qtMultichoose_pascal_conjectural (q t : R) (n k : ℕ) :
    qtMultichoose q t (n + 1) (k + 1) =
    qtMultichoose q t (n + 1) k +
    q ^ (k + 1) * t ^ ? * qtMultichoose q t n (k + 1) := by
  sorry  -- S2 deliverable; t-weight is the open question

end QtMultichooseCoefficients
```

## Classification

```yaml
tier: B
significance: 5
tractability: 4
tags:
  - seeker-selected
  - combinatorics
  - q-analogs
  - qt-analogs
  - macdonald-polynomials
  - hall-littlewood
  - gaussian-binomial
  - multiset
  - representation-theory
  - mathlib-gap
```

**Significance**: 5/10 — Macdonald polynomials are a major subject in algebraic combinatorics (Macdonald 1995, Haiman 2001 for the $n!$ conjecture, Cherednik DAHA, Garsia–Haiman positivity). A $(q,t)$-multichoose with a Lean-formalised Pascal recurrence would be the **first Lean entry to mention Macdonald theory at all**. But the bare $(q,t)$-binomial coefficient is a well-known object (Macdonald §VI.6); the open novelty is the Lean formalisation, not the mathematics.

**Tractability**: 4/10 — Mixed:
- **The candidate definition is unambiguous** (Macdonald (q,t)-binomial); S2 to formalise it is mechanical.
- **The (q,t)-Pascal recurrence** is NOT immediate from the parent's q-Pascal — the t-weight in the conjectural form `q^(k+1) · t^? · qtMultichoose q t n (k+1)` requires explicit derivation. Macdonald's book gives a (q,t)-Pascal for $\binom{n}{k}_{q,t}$ but not in the same form as the parent's; transferring via the multichoose substitution $n \mapsto n+k-1$ adds careful index bookkeeping.
- **Specialization at t = 1** (to qMultichoose) is *expected* but needs an explicit calculation showing all $t^{i}$ terms collapse to $1^i = 1$.
- **Specialization at q = t = 1** involves a 0/0 limit that requires either cancelling each factor as a polynomial in $(q-1, t-1)$ or working in a localized ring.
- **Macdonald polynomial connection** (sec. III of any future formalization) is *deep* and entirely absent from Mathlib v4.26.0; this layer should be axiomatised or excluded from S1–S5 scope.

## Decomposition (S2–Sk targets)

### S2 — Definition `qtBinom`, `qtMultichoose` and basic boundary cases

**Deliverable**: `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean` with:

```lean
noncomputable def qtBinom (q t : R) (n k : ℕ) : R := ...
noncomputable def qtMultichoose (q t : R) (n k : ℕ) : R := qtBinom q t (n + k - 1) k

@[simp] theorem qtBinom_zero_right (q t : R) (n : ℕ) : qtBinom q t n 0 = 1 := by simp [qtBinom]
@[simp] theorem qtMultichoose_zero_right (q t : R) (n : ℕ) : qtMultichoose q t n 0 = 1 := ...
-- and corresponding zero_left, one_left, one_right boundary cases
```

Expected ~40 Lean lines. No theorems beyond definitions + boundary cases.

### S3 — Specialization at $t = 1$ (recovers qMultichoose)

**Deliverable**: prove
```lean
theorem qtMultichoose_at_t_eq_one (q : R) (n k : ℕ) :
    qtMultichoose q 1 n k = qMultichoose q n k
```

**Approach**: substitute $t = 1$ into the product formula; each factor $\frac{1 - q^{n+k-i} \cdot 1^{i-1}}{1 - q^i \cdot 1^{i-1}} = \frac{1 - q^{n+k-i}}{1 - q^i}$. Then compare with the parent's `qBinom` definition via `qBinom_eq_prod_form` (which the parent proves at line ~80 of `Proofs.CombinationsFormulaOQ03`).

Expected ~25 Lean lines, no sorries.

### S4 — (q,t)-Pascal recurrence

**Conjecture** (to verify or refute in S4):
$$ \mathrm{qtMultichoose}(q, t, n+1, k+1) = \mathrm{qtMultichoose}(q, t, n+1, k) + q^{k+1} t^{?} \cdot \mathrm{qtMultichoose}(q, t, n, k+1). $$

**Determining the $t^?$ exponent**: at $t = 1$, the formula must reduce to the parent's q-Pascal, which has weight $q^{k+1}$ (no t). So $t^?$ at $t = 1$ becomes 1, but the exponent itself could be $0$, $n - k$, $n - 2k$, etc.; substituting small cases ($n = k = 0$, $n = 1, k = 0$) determines it.

**Approach**: brute-force expansion of $\mathrm{qtMultichoose}(q, t, 2, 2)$ vs $\mathrm{qtMultichoose}(q, t, 2, 1) + q^2 t^? \mathrm{qtMultichoose}(q, t, 1, 2)$; the unique $?$ value matching is the answer. Then proven for general $n, k$ by polynomial manipulation.

Expected ~80 Lean lines (the polynomial identity is non-trivial).

### S5 — Specialization at $q = t = 1$ (recovers ordinary multichoose)

**Deliverable**: prove
```lean
theorem qtMultichoose_at_one_one (n k : ℕ) :
    qtMultichoose (1 : R) (1 : R) n k = (Nat.multichoose n k : R)
```

**Approach**: cannot substitute $q = t = 1$ directly (each factor is $0/0$). Use limit / repeated cancellation: each factor $\frac{1 - q^a t^b}{1 - q^c t^d}$ as $(q, t) \to (1, 1)$ along a smooth path becomes $\frac{a + b \cdot (\partial \log)}{c + d \cdot (\partial \log)}$, which simplifies further. The cleanest Lean approach is to substitute the conjectural Pascal recurrence at $q = t = 1$, get the ordinary Pascal recurrence for $\binom{n+k-1}{k}$, then use induction matching `Nat.multichoose_eq_choose`.

Expected ~30 Lean lines (induction wrapper).

### S6 — Connection to Macdonald polynomial principal specializations (axiomatised)

**Deliverable** (optional, deferrable): axiomatise the identity
$$ P_{(k)}(1, q, q^2, \ldots, q^{n-1}; q, t) = c_{n,k}(q, t) \cdot \mathrm{qtMultichoose}(q, t, n, k) $$
where $P_{(k)}$ is the Macdonald polynomial of one-row shape $(k)$ at the principal specialization, and $c_{n,k}(q, t)$ is an explicit Macdonald-norm factor.

This is the *deep* connection to Macdonald theory; until Mathlib has Macdonald polynomials, this is purely declarative axiomatisation.

### S7 — Gallery integration

Add `src/data/proofs/arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02/` with `status: "verified"` if S2–S5 ship without axioms, else `"axiomatized"` (depending on whether S5's $q=t=1$ specialization is provable in pure Lean or requires a real-analytic limit axiom).

## Mathlib Infrastructure Map

| Need | Mathlib name (v4.26.0) | Module |
|------|-----------------------|--------|
| Gaussian binomial `qBinom` | (project-local) `qBinom` in `Proofs.CombinationsFormulaOQ03` | parent files |
| `qNumber q n = [n]_q` | (project-local) `qNumber` in `Proofs.CombinationsFormulaOQ03` | parent files |
| `Finset.prod` over `Finset.range k` | `Finset.prod_range_succ` | `Mathlib.Algebra.BigOperators.Basic` |
| Field-valued rational expressions | `Field R` | `Mathlib.Algebra.Field.Basic` |
| `Nat.multichoose` | `Nat.multichoose` | `Mathlib.Data.Nat.Choose.Multinomial` |

**Gaps (no Mathlib support)**:

- **Macdonald polynomials** $P_\lambda(x; q, t)$ — not in Mathlib. Cannot reference Macdonald theory directly.
- **Hall–Littlewood polynomials** $P_\lambda(x; t)$ — not in Mathlib.
- **Schur functions** — partial: `Mathlib.RepresentationTheory.SymmetricFunctions` has Schur for partitions, but not the (q,t)-deformation.
- **Cherednik DAHA / DAHA representation theory** — not in Mathlib.

⇒ All higher-level Macdonald connections will be axiomatised in S6+.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03` (direct parent) | qMultichoose definition + q-Pascal |
| `combinations-formula-oq-03` (grandparent of qBinom) | Gaussian binomial infrastructure |
| `arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02` | multiset Vandermonde identity (parent of parent) |
| `arithmetic-series-oq-02-oq-04-oq-01-oq-03` | Multiset coefficients combinatorics |
| `arithmetic-series-oq-02-oq-04` | Higher-order combinatorial identities |

## Risk Notes

- **Mathematical novelty**: the (q,t)-multichoose is **not novel**: it's a direct consequence of Macdonald's (q,t)-binomial coefficient (Macdonald 1995). The novelty is the *Lean formalisation*, which is genuine.

- **(q,t)-Pascal recurrence form is genuinely uncertain**: S4 is a real research question even given Macdonald's book. The book gives Pascal-like identities for symmetric functions, not directly for the (q,t)-binomial in the same form as the parent's q-Pascal.

- **`Field R` vs `CommRing R`**: the parent works over arbitrary `CommRing R`, but `qtBinom` involves division (rational expression), so we need `Field R` (or a localized ring). This may complicate gallery integration if downstream consumers want `CommRing`.

- **0/0 at $q = t = 1$**: the specialization at $q = t = 1$ is a genuine limit, not a substitution. S5's approach (use the q-Pascal recurrence in the limit, then match by induction) sidesteps this; otherwise a topological argument is needed.

- **`status` policy**: if S2–S5 ship without axioms, `verified`. S6 axiomatisation moves it to `axiomatized`. Most likely outcome: S2–S5 ship clean, S6 axiomatises Macdonald connection.

- **Sibling sub-OQs of parent**:
  - `arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-01`: q-multiset Vandermonde identity. Different question (an identity, not a deformation).
  - `arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-03`: combinatorial interpretation over 𝔽_q (counting structures). Different question (interpretation, not deformation).

  No mathematical overlap with this sub-OQ.

## References

- Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Oxford 1995 — chapter VI §6 on Macdonald (q,t)-binomials.
- Macdonald, *A new class of symmetric functions*, Sém. Lothar. Combin. (1988) — original definition of Macdonald polynomials.
- Haiman, *Hilbert schemes, polygraphs, and the Macdonald positivity conjecture*, J. Amer. Math. Soc. 14 (2001), 941–1006 — connection of Macdonald to algebraic geometry.
- Cherednik, *Double affine Hecke algebras*, Cambridge 2005 — Macdonald polynomials via DAHA.
- Garsia & Haiman, *A graded representation model for Macdonald's polynomials*, Proc. Natl. Acad. Sci. USA 90 (1993).
- OEIS [A008956](https://oeis.org/A008956) — (q,t)-binomial coefficient sequence at small values.
- nLab: [Macdonald polynomial](https://ncatlab.org/nlab/show/Macdonald+polynomials)

## Honesty

This S1 OBSERVE iteration is a **pure survey**. It produces:

- 0 new Lean theorems
- 0 sorry deltas
- 0 axiom deltas
- 3 markdown files
- 1 gallery JSON entry

The provisional candidate definition $\mathrm{qtMultichoose}(q, t, n, k) := \binom{n+k-1}{k}_{q,t}$ is from Macdonald's textbook (well-established). The *open* part is whether the Lean formalisation can ship S2–S5 without axioms (likely yes for S2, S3, S5; the (q,t)-Pascal in S4 is research-grade).

The future Lean entry will be `status: "verified"` if S5 ships without axioms; `"axiomatized"` if a real-analytic limit axiom is needed for the $q = t = 1$ specialization.
