# Problem: CRT for 3 Non-Coprime Moduli in PIDs via IsBezout

**Slug**: chinese-remainder-non-coprime-oq-02-oq-01
**Created**: 2026-04-21T22:19:23+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Extend the gallery proof `chinese-remainder-non-coprime-oq-02` (CRT for 2 non-coprime moduli in Euclidean domains) to **3 non-coprime moduli** in PIDs:

Given a PID $R$ and ideals $I_1, I_2, I_3 \trianglelefteq R$, the system
$$x \equiv a_i \pmod{I_i}, \quad i = 1, 2, 3$$
is solvable iff for all $i \neq j$: $a_i - a_j \in I_i + I_j$.

The solution is unique modulo $I_1 \cap I_2 \cap I_3$.

### Plain Language

The Chinese Remainder Theorem for coprime moduli is classical. The gallery entry `chinese-remainder-non-coprime-oq-02` generalizes to 2 non-coprime moduli. This problem extends to 3 moduli: the solvability condition is pairwise compatibility ($a_i \equiv a_j \pmod{I_i + I_j}$ for all pairs), and the solution space is unique mod the intersection $I_1 \cap I_2 \cap I_3$.

### Why This Matters

- The 2-moduli non-coprime CRT was the main result of `chinese-remainder-non-coprime-oq-02`
- Extending to 3 moduli shows the pattern generalizes (by induction, to $n$ moduli)
- Ideal-theoretic CRT in PIDs unifies integer and polynomial CRT in one theorem
- The `IsBezout` typeclass in Mathlib provides the key infrastructure

## Known Results

### What's Already Proven

- 2-moduli non-coprime CRT: in gallery `chinese-remainder-non-coprime-oq-02`
- Mathlib: `IsBezout.isCoprime_of_dvd` and related PID lemmas
- For ideals: `Ideal.add_eq_top_iff` (coprime ideals ↔ $I + J = R$)
- `Ideal.quotient.chinese_remainder` for coprime case in Mathlib

### What's Still Open

- Explicit Lean 4 formalization of 3-moduli solvability criterion
- The inductive step from 2 to 3 moduli in a PID

### Our Goal

Formalize: in a PID `R`, the system `x ≡ a_i [I_i]` for `i = 1, 2, 3` is solvable iff `a_i - a_j ∈ I_i + I_j` for all pairs. Reference: `ChineseRemainderNonCoprimeOQ03.lean` in the gallery.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| chinese-remainder-non-coprime-oq-02 | Direct parent — 2-moduli non-coprime CRT | IsBezout, ideal arithmetic |
| chinese-remainder-constructive-oq-04 | Minimal non-negative CRT solution | constructive CRT |
| chinese-remainder-non-coprime-oq-03 | 3-moduli integer case | integer-specific |

## Initial Thoughts

### Potential Approaches

1. **Inductive from 2-moduli**: Apply 2-moduli CRT twice: first solve $x \equiv a_1 \pmod{I_1}$, $x \equiv a_2 \pmod{I_2}$ to get $x_{12}$ mod $I_1 \cap I_2$, then solve with $I_1 \cap I_2$ and $I_3$.
   - Why it might work: Reduces to 2 applications of the proven result
   - Risk: Need $I_1 \cap I_2$ in the right form; intersection of ideals in PIDs

2. **Direct ideal arithmetic**: Express solvability via the ideal $I_1 \cdot I_2 \cdot I_3$ and use the `Submodule.add_eq_sup` API.
   - Why it might work: More algebraically clean
   - Risk: May require more Mathlib ideal lemmas

### Key Difficulties

- `Ideal.iInf_comap_quotient_pow` or similar for 3-way intersection
- Establishing that the pairwise conditions are sufficient (not just necessary)
- The `IsBezout` typeclass might not directly extend beyond 2 ideals

### What Would a Proof Need?

- `Ideal.add_eq_top_iff` applied to pairs
- `Ideal.quotient.liftₛ` or `Ideal.chineseRemainder` multi-ring version
- Induction lemma: if solvable for $(I_1, I_2)$ and $(I_1 \cap I_2, I_3)$, then solvable for $(I_1, I_2, I_3)$

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The 2-moduli case is already proven in the gallery
- The 3-moduli case follows by induction: combine $I_1 \cap I_2$ with $I_3$
- Mathlib's ideal API is mature; `Ideal.iInf` handles finite intersections

## References

### Papers
- Lang, "Algebra", Chapter II — ideal CRT in Dedekind domains

### Mathlib
- `Mathlib.RingTheory.Ideal.Quotient` — ideal quotient and CRT
- `Mathlib.RingTheory.PrincipalIdealDomain` — PID characterization
- `Mathlib.RingTheory.Bezout` — `IsBezout` typeclass

## Metadata

```yaml
tags:
  - number-theory
  - chinese-remainder-theorem
  - ring-theory
  - pid
  - euclidean-domain
  - ideal-theory
related_proofs:
  - chinese-remainder-non-coprime-oq-02
  - chinese-remainder-constructive-oq-04
difficulty: medium
source: gallery-gap
created: 2026-04-21T22:19:23+02:00
```

**Significance**: 7/10
**Tractability**: 6/10
