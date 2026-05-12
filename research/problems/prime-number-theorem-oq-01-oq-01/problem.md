# Problem: Is the Riemann Hypothesis true

## Source / Status

This slug was seeker-extracted from the parent
`prime-number-theorem-oq-01` ("From PNT to optimal prime distribution"),
whose Lean file `proofs/Proofs/PrimeNumberTheoremOQ01.lean` already states
RH and assumes it via several axioms. **It overlaps almost entirely** with
the existing gallery slug `riemann-hypothesis`
(`proofs/Proofs/RiemannHypothesis.lean`, 41 axioms, status COMPLETED in
the research-problem-pool).

RH itself is a **Millennium Prize Problem (2000)**; no formal proof is
plausible from a research session. Any meaningful S(N) work on this slug
must therefore target a *related tractable result*, not the open
conjecture itself.

## Statement

### Plain language

Let
$\zeta(s) = \sum_{n=1}^{\infty} n^{-s} \quad \text{for } \Re s > 1$
(extended to all $s \in \mathbb{C} \setminus \{1\}$ by analytic
continuation). The trivial zeros of $\zeta$ are $-2, -4, -6, \ldots$.
The **Riemann Hypothesis** asserts that every non-trivial zero satisfies
$\Re s = \tfrac{1}{2}$.

### Formal statement (using `Mathlib.NumberTheory.LSeries.RiemannZeta`)

$$
\mathrm{RH} \;\Leftrightarrow\;
\forall s \in \mathbb{C},\; \zeta(s) = 0 \,\wedge\, 0 < \Re s < 1 \;\Rightarrow\; \Re s = \tfrac{1}{2}.
$$

This is the form already formalised in
`proofs/Proofs/RiemannHypothesis.lean` (def `RiemannHypothesis`) and in
`proofs/Proofs/PrimeNumberTheoremOQ01.lean` (def `RiemannHypothesis`).
The two definitions are propositionally identical up to unfolding
`isNonTrivialZero`.

### Three equivalent reformulations (all axiomatised in the gallery)

The classical literature lists a long menu of equivalents. Three already
appear in `Proofs/RiemannHypothesis.lean` as axioms:

1. **Robin (1984)** —
   $\sigma(n) < e^{\gamma}\, n \log\log n \quad\text{for all } n > 5040.$
   (`RH_iff_Robin`, file line 284.)
2. **Mertens-Littlewood (1912)** — for all $\varepsilon > 0$,
   $M(x) := \sum_{n \le x} \mu(n) = O\!\left(x^{1/2 + \varepsilon}\right).$
   (`RH_iff_Mertens`, file line 325.)
3. **Von Koch (1901) / Prime-counting** —
   $|\pi(x) - \mathrm{Li}(x)| = O\!\left(\sqrt{x}\, \log x\right)$
   for all sufficiently large $x$.
   (`RH_iff_PrimeCounting`, file line 383.)

Each equivalence is genuinely a Mathlib milestone (deep number theory);
no full Lean proof is feasible without major new infrastructure.

## Classification

```yaml
tier: B
significance: 6
tractability: 4
tags:
  - seeker-selected
  - riemann-hypothesis
  - duplicate-of-riemann-hypothesis-slug
```

**Significance**: 6/10 — Millennium Prize, but this slug duplicates the
parent `riemann-hypothesis` slug and offers no fresh angle.

**Tractability**: 4/10 — the open conjecture is intractable; only narrow
adjacent results (bridge theorems, axiom discharge, partial direction of
one equivalent) are realistic.

## Why this matters

1. **Cleaning the gallery** — the slug presently has no formal statement
   and a NEW-phase state. Either (a) close it as a duplicate, or (b)
   reorient it onto a small tractable RH-related sub-target. This S1
   makes that decision explicit.
2. **Bridge value** — `RiemannHypothesis.lean` and
   `PrimeNumberTheoremOQ01.lean` use independent (definitionally
   equivalent) `RiemannHypothesis : Prop` declarations. A short bridge
   theorem `PrimeNumberTheoremOQ01.RiemannHypothesis ↔ Proofs.RiemannHypothesis.RiemannHypothesis`
   would let downstream files cite either form. This is a candidate S2
   target with ~10 LOC.
3. **Axiom-discharge candidates** — the parent file's 41 axioms include
   a few that may now be discharge-able with current Mathlib (e.g.
   `zeta_zero`, `trivial_zeros`, and possibly `zeta_conj`); a focused
   audit pass against Mathlib v4.26.0 is independently useful even if
   RH itself is untouched.

## Related gallery proofs

| Proof | Relevance |
|-------|-----------|
| `riemann-hypothesis` | **Direct duplicate** — parent slug, COMPLETED status, 41 axioms, all RH formalisation already lives there. |
| `rh-consequences` | Sibling — collects results that depend on RH. |
| `prime-number-theorem` | PNT (Hadamard / de la Vallée-Poussin 1896); proven unconditionally; uses `riemannZeta` non-vanishing on $\Re s = 1$. |
| `prime-number-theorem-oq-01` | The immediate parent OQ — states RH and several conditional sharpenings of PNT. |
