# Problem: Which Powers of ω Are Primitive n-th Roots of Unity, and the Totient Count

**Slug**: de-moivre-oq-04-oq-01
**Created**: 2026-07-09T16:43:19-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{For } \omega = \cos(2\pi/n) + i\sin(2\pi/n) \text{ and } 0 \le k < n:\quad
\omega^k \text{ is a primitive } n\text{-th root of unity} \iff \gcd(k,n) = 1,
$$
$$
\text{and consequently } \#\{\, k \in \{0,\dots,n-1\} : \omega^k \text{ is primitive} \,\} = \varphi(n),
$$

where $\varphi$ is Euler's totient function.

### Plain Language

The gallery proof De Moivre OQ-04 shows that $\omega = \cos(2\pi/n) + i\sin(2\pi/n)$ is a *primitive* $n$-th root of unity, meaning its powers $\omega^0, \omega^1, \dots, \omega^{n-1}$ march once around the unit circle and cover **all** $n$ solutions of $z^n = 1$. But not every one of those powers is itself a *generator*: $\omega^k$ regenerates all $n$ roots exactly when $k$ shares no common factor with $n$. This problem asks us to prove that clean criterion — $\omega^k$ is primitive if and only if $\gcd(k,n) = 1$ — and to derive the immediate corollary that the number of primitive $n$-th roots of unity is precisely $\varphi(n)$, Euler's totient. Geometrically, the primitive roots are exactly the vertices of the regular $n$-gon whose "step" $k$ still visits every vertex before returning home.

### Why This Matters

This is the bridge from "$\omega$ generates the roots of unity" to the full arithmetic structure of the cyclic group $\mu_n$. The totient count $\varphi(n)$ is the degree of the $n$-th cyclotomic polynomial $\Phi_n$, so this result is the combinatorial backbone underneath cyclotomy, Gauss's constructibility criterion for regular polygons, and the theory of primitive roots modulo $n$. It also gives a self-contained, geometric proof of a totient identity purely from De Moivre's formula, tightening the connection between complex analysis and number theory that the parent entry opens.

## Known Results

### What's Already Proven

- `IsPrimitiveRoot (omega n) n` — the gallery proof De Moivre OQ-04 establishes that $\omega$ itself is a primitive $n$-th root of unity (transported from `Complex.isPrimitiveRoot_exp`).
- `IsPrimitiveRoot.pow_iff_coprime` — Mathlib: for a primitive $n$-th root $\zeta$, $\zeta^k$ is primitive iff $\gcd(k,n) = 1$ (module `Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots`).
- `Nat.totient` and `Nat.totient_eq_card_coprime` — Mathlib: $\varphi(n)$ counts the integers in $\{0,\dots,n-1\}$ coprime to $n$.

### What's Still Open

- Packaging the "iff coprime" criterion specifically for the *trigonometric generator* $\omega = \cos(2\pi/n) + i\sin(2\pi/n)$ as a standalone verified statement in the gallery, rather than only for the exponential form.
- Deriving the totient count $\#\{k < n : \omega^k \text{ primitive}\} = \varphi(n)$ as a formalized corollary tied to $\omega$.

### Our Goal

Formalize, on top of the existing De Moivre OQ-04 development, the two statements: (1) $\omega^k$ is primitive iff $\gcd(k,n) = 1$ for $0 \le k < n$, and (2) the primitive $n$-th roots number exactly $\varphi(n)$. Reuse `omega_isPrimitiveRoot` from the parent proof so the new lemmas speak about the concrete trigonometric $\omega$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| de-moivre-oq-04 | Parent: proves $\omega$ is a primitive $n$-th root and its powers enumerate all roots of unity; supplies `omega`, `omega_isPrimitiveRoot`, `omega_pow_inj` | De Moivre collapse $n\cdot(2\pi/n)=2\pi$, Euler bridge, `IsPrimitiveRoot` API, injectivity of $k \mapsto \omega^k$ |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Transport Mathlib's coprimality criterion**: Apply `IsPrimitiveRoot.pow_iff_coprime` directly to `omega_isPrimitiveRoot`, instantiating $\zeta = \omega$. This yields $\omega^k$ primitive $\iff \gcd(k,n) = 1$ almost immediately.
   - Why it might work: Mathlib already has the general theorem for any primitive root in an integral domain; the hard analytic content (that $\omega$ *is* primitive) is done in the parent proof.
   - Risk: Mismatched hypotheses (e.g. `n.Coprime k` vs `k.Coprime n`, or side conditions like $n \neq 0$ and $k < n$) may require careful bookkeeping and `omega`/`Nat.gcd_comm` rewrites.

2. **Approach B — Count via a coprimality bijection**: Establish a bijection between $\{k < n : \gcd(k,n) = 1\}$ and the set of primitive $n$-th roots (image of $k \mapsto \omega^k$), then compose with `Nat.totient_eq_card_coprime` to get the cardinality $\varphi(n)$.
   - Why it might work: `omega_pow_inj` from the parent proof already gives injectivity of $k \mapsto \omega^k$ on $\{0,\dots,n-1\}$, so the bijection reduces to matching the coprime index set against the primitive-root set.
   - Risk: Working with `Finset.card` of an image and the exact definitional form of `Nat.totient` in Mathlib; ensuring the counting statement is phrased with `primitiveRoots n ℂ` or an explicit filtered finset.

### Key Difficulties

- Reconciling the exact Mathlib naming and hypothesis order of the coprimality/primitivity API (`IsPrimitiveRoot.pow_iff_coprime` and neighbours) with the concrete $\omega$ from the parent file.
- Choosing the canonical target for the count — `Nat.totient n`, `(primitiveRoots n ℂ).card`, or a filtered `Finset.range n` — and threading `Nat.totient_eq_card_coprime` to bind them.

### What Would a Proof Need?

- Key lemma 1: `omega_pow_isPrimitiveRoot_iff : IsPrimitiveRoot ((omega n)^k) n ↔ Nat.Coprime k n` (for $n \neq 0$), obtained from `omega_isPrimitiveRoot` and `IsPrimitiveRoot.pow_iff_coprime`.
- Key lemma 2: A cardinality statement identifying the number of primitive $n$-th roots (equivalently the coprime residues below $n$) with `Nat.totient n`.
- Technical requirements: `Nat.Coprime`/`Nat.gcd` API, `Nat.totient_eq_card_coprime`, `Finset.card` of an injective image (leveraging `omega_pow_inj`), and the parent file's exported `omega` and `omega_isPrimitiveRoot`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The core analytic fact (that $\omega$ is a primitive $n$-th root) is already fully verified in the parent gallery proof, so this is a targeted extension rather than a fresh formalization.
- Mathlib provides the essential ingredients: `IsPrimitiveRoot.pow_iff_coprime` for the criterion and `Nat.totient_eq_card_coprime` for the count.
- The residual work is API plumbing — matching hypothesis conventions and phrasing the cardinality statement — which is fiddly but not deep.

**Estimated Effort**:
- Exploration: 1–2 hours
- If tractable: 1–3 days
- If hard: up to 1–2 weeks (if the counting corollary needs a custom bijection)

## References

### Papers
- Carl Friedrich Gauss, *Disquisitiones Arithmeticae*, 1801 — cyclotomy, primitive roots, and the totient degree of $\Phi_n$.
- Leonhard Euler, *Introductio in analysin infinitorum*, 1748 — the totient function and the exponential form $e^{2\pi i/n}$.

### Online Resources
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.html — Mathlib primitive-root API, including the coprimality criterion for powers of a primitive root.

### Mathlib
- `Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots` — `IsPrimitiveRoot.pow_iff_coprime`, `IsPrimitiveRoot.pow_inj`, and the `primitiveRoots` finset.
- `Mathlib.NumberTheory.Divisors` / `Mathlib.Data.Nat.Totient` — `Nat.totient` and `Nat.totient_eq_card_coprime`.
- `Mathlib.RingTheory.RootsOfUnity.Complex` — `Complex.isPrimitiveRoot_exp`, the source of $\omega$'s primitivity in the parent proof.

## Metadata

```yaml
tags:
  - complex-analysis
  - trigonometry
  - de-moivre
  - roots-of-unity
  - primitive-roots
  - wiedijk-100
related_proofs:
  - de-moivre-oq-04
difficulty: medium
source: gallery-gap
created: 2026-07-09T16:43:19-07:00
```
