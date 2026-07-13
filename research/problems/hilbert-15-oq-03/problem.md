# Problem: Quantum Schubert Calculus Corrections to Classical Intersection Numbers

**Slug**: hilbert-15-oq-03
**Created**: 2026-07-03
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\sigma_\lambda \star \sigma_\mu\ =\ \sum_{\nu,\, d \ge 0} q^{d}\, c_{\lambda\mu}^{\nu, d}\, \sigma_\nu \quad\text{in}\quad QH^*(\mathrm{Gr}(k,n)),
$$

with $c_{\lambda\mu}^{\nu,0}$ the classical Littlewood–Richardson coefficients. Determine how the quantum corrections $c_{\lambda\mu}^{\nu,d}$ ($d \ge 1$, the 3-point genus-0 Gromov–Witten invariants) modify the classical intersection numbers.

### Plain Language

Hilbert's 15th sought rigorous foundations for Schubert calculus — the classical count of geometric incidences on Grassmannians, governed by the Littlewood–Richardson rule. Quantum cohomology deforms the cup product by "quantum corrections" counting rational curves (Gromov–Witten invariants). This question asks how those corrections modify the classical intersection numbers: what is the structure of the quantum product $\sigma_\lambda \star \sigma_\mu$ relative to the classical one?

### Why This Matters

Quantum Schubert calculus connects enumerative geometry, representation theory, and mathematical physics (via the Verlinde algebra and the $\mathfrak{sl}_n$ WZW model). Understanding the corrections rigorously extends the classical, formalized story of Hilbert's 15th into the modern quantum setting.

## Known Results

### What's Already Proven

- Classical intersection theory on Grassmannians: Schubert classes as a $\mathbb{Z}$-basis, Littlewood–Richardson rule for structure constants — parent entry `hilbert-15`.
- Verified classical intersection numbers via the formalized framework — parent entry.

### What's Still Open

- A formal treatment of the quantum product $\star$ and the Gromov–Witten corrections $c_{\lambda\mu}^{\nu,d}$.
- Rigorous statement of Bertram's quantum Littlewood–Richardson rule in this framework.

### Our Goal

Formalize the *statement* of quantum Schubert calculus on $\mathrm{Gr}(k,n)$ — the deformed product, the grading by degree $d$, and the recovery of classical numbers at $q = 0$ — and verify the smallest quantum-corrected products (e.g. on $\mathrm{Gr}(2,4)$).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| hilbert-15 | Direct parent; supplies Schubert classes and the classical LR rule | Intersection theory, Littlewood–Richardson |

## Initial Thoughts

### Potential Approaches

1. **Algebraic/axiomatic model**: define $QH^*(\mathrm{Gr}(k,n))$ as a $\mathbb{Z}[q]$-algebra with structure constants supplied by (axiomatized) Gromov–Witten invariants, and prove $q \to 0$ recovers the classical ring.
   - Why it might work: mirrors the parent entry's axiomatized-intersection-theory style.
   - Risk: the invariants are assumed, not derived from moduli of curves.

2. **Small explicit case**: compute $QH^*(\mathrm{Gr}(2,4))$ by hand and verify the quantum corrections against Bertram's rule.
   - Why it might work: fully finite, checkable structure constants.
   - Risk: limited generality; establishes the pattern, not the theorem.

### Key Difficulties

- Genuine Gromov–Witten invariants require moduli of stable maps, far beyond current Mathlib.
- Separating what is *axiomatized* from what is *proven* (per the Axiom Integrity Policy).

### What Would a Proof Need?

- Key lemma 1: a $\mathbb{Z}[q]$-algebra structure with a classical-limit homomorphism at $q = 0$.
- Key lemma 2: quantum structure constants for a small Grassmannian matching Bertram's rule.
- Technical requirements: commutative-algebra and free-module infrastructure in Mathlib.

## Tractability Assessment

**Difficulty**: Moonshot

**Justification**:
- Full quantum cohomology needs Gromov–Witten theory absent from Mathlib.
- Any near-term result must be an axiomatized model or a single explicit Grassmannian.
- The parent entry's axiomatized approach gives a viable, honestly-scoped template.

**Estimated Effort**:
- Exploration: days
- If tractable: weeks (for an axiomatized small case)
- If hard: unknown

## References

### Papers
- A. Bertram, "Quantum Schubert calculus", Adv. Math. (1997) — quantum Littlewood–Richardson rule.
- W. Fulton, "Young Tableaux" — classical Schubert calculus background.

### Online Resources
- Hilbert's 15th problem overview — https://en.wikipedia.org/wiki/Hilbert%27s_fifteenth_problem

### Mathlib
- `Polynomial` / `MvPolynomial` over $\mathbb{Z}$ — the $\mathbb{Z}[q]$ coefficient ring.
- Free-module and algebra structures — for the Schubert-class basis.

## Metadata

```yaml
tags:
  - algebraic-geometry
  - intersection-theory
  - quantum-cohomology
  - hilbert-problems
related_proofs:
  - hilbert-15
difficulty: moonshot
source: proof-suggestion
created: 2026-07-03
```

**Significance**: 6/10
**Tractability**: 3/10
