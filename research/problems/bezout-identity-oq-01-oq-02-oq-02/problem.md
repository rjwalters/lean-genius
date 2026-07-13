# Problem: Transitivity of SLₙ(ℤ) on Primitive Vectors

**Slug**: bezout-identity-oq-01-oq-02-oq-02
**Created**: 2026-07-09T16:43:19-07:00
**Status**: Active
**Source**: user-request

## Problem Statement

### Formal Statement

$$
\forall\, v \in \mathbb{Z}^n \text{ with } \gcd(v_1,\dots,v_n)=1,\ \ \exists\, U \in \mathrm{SL}_n(\mathbb{Z}) \text{ such that } U \cdot v = e_1 = (1,0,\dots,0)^{\top}.
$$

Equivalently, $\mathrm{SL}_n(\mathbb{Z})$ acts transitively on the set of primitive integer vectors, and the construction of $U$ should be effective (built from Bézout data).

### Plain Language

The parent gallery entry shows that for two integers $a,b$ with $\gcd(a,b)=1$ there is a $2\times 2$ integer matrix $U$ of determinant $1$ that sends the column vector $(a,b)$ to $(1,0)$. This problem asks for the $n$-dimensional analogue: given any integer vector $v=(v_1,\dots,v_n)$ whose coordinates have greatest common divisor $1$ (a *primitive* vector), construct an $n\times n$ integer matrix $U$ with determinant $1$ — an element of the special linear group $\mathrm{SL}_n(\mathbb{Z})$ — that carries $v$ to the first standard basis vector $e_1=(1,0,\dots,0)$. Because every such $U$ is invertible over $\mathbb{Z}$, this says that any primitive vector can be extended to a $\mathbb{Z}$-basis of $\mathbb{Z}^n$, and that all primitive vectors look alike from the point of view of $\mathrm{SL}_n(\mathbb{Z})$ — the group acts transitively on them.

### Why This Matters

Transitivity of $\mathrm{SL}_n(\mathbb{Z})$ on primitive vectors is a foundational fact in the arithmetic of lattices: it is the statement that a primitive vector can always be completed to a unimodular basis of $\mathbb{Z}^n$. It underlies Smith normal form, the structure theory of finitely generated abelian groups, the reduction theory of quadratic forms in $n$ variables, and computations with modular / arithmetic groups. The $n=2$ case (the parent proof) is the seed of the modular group $\mathrm{SL}_2(\mathbb{Z})$; the general case is the natural next rung and connects Bézout's identity directly to lattice geometry. Formalizing an *effective* construction (as opposed to a pure existence argument) gives a reusable, computable reduction tool inside Mathlib.

## Known Results

### What's Already Proven

- **n = 2 case** — the parent proof `bezout-identity-oq-01-oq-02` builds the explicit $2\times2$ matrix $U=\big[\begin{smallmatrix}\mathrm{gcdA}&\mathrm{gcdB}\\ -b/g&a/g\end{smallmatrix}\big]$, proves $U\cdot(a,b)=(g,0)$ for all $a,b$, and $\det U = 1$ when $g\ne 0$, packaging coprime pairs as elements of `Matrix.SpecialLinearGroup (Fin 2) ℤ`.
- **Bézout's identity** — Mathlib's `Int.gcd_eq_gcd_ab` / `Int.gcdA` / `Int.gcdB` give the two-variable coefficients that drive the $n=2$ reduction.
- **Existence over general PIDs** — the classical statement that a primitive vector over a PID extends to a basis is standard textbook material (Newman, *Integral Matrices*; Dummit–Foote via Smith normal form), though not packaged in the effective `SpecialLinearGroup` form this problem targets.

### What's Still Open

- An **effective** Lean construction of $U \in \mathrm{SL}_n(\mathbb{Z})$ (not merely an existence proof) carrying an arbitrary primitive $v$ to $e_1$, generalizing `bezoutMatrix` to $n$ coordinates.
- A clean induction (or recursion on $n$) that keeps the determinant exactly $1$ (not $\pm 1$) at every step, matching the sign convention used in the parent proof.
- Packaging the result as transitivity of the `Matrix.SpecialLinearGroup (Fin n) ℤ` action on primitive vectors in Mathlib-idiomatic form.

### Our Goal

Formalize, in Lean 4 over Mathlib, that for every primitive $v \in \mathbb{Z}^n$ there exists $U \in \mathrm{SL}_n(\mathbb{Z})$ with $U \cdot v = e_1$, via an explicit recursive construction that reduces the $n$-coordinate case to the $2$-coordinate `bezoutMatrix` of the parent proof, so the whole statement is machine-verified with no new axioms.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| bezout-identity-oq-01-oq-02 | The direct $n=2$ base case: builds the unimodular $2\times2$ reduction matrix and its `SL₂(ℤ)` packaging that the induction glues together | Bézout coefficients `Int.gcdA`/`Int.gcdB`, `Matrix.det_fin_two_of`, `mulVec`, `Matrix.SpecialLinearGroup` |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Recursion on the number of coordinates.**
   Reduce the last two coordinates $(v_{n-1}, v_n)$ using the parent's $2\times2$ `bezoutMatrix`, embedded as a block-diagonal $\mathrm{SL}_n(\mathbb{Z})$ matrix acting on those two slots. This replaces $(v_{n-1}, v_n)$ by $(\gcd(v_{n-1},v_n), 0)$, killing one coordinate while preserving determinant $1$. Iterating collapses $v$ to $(\gcd(v_1,\dots,v_n), 0,\dots,0) = (1,0,\dots,0)$ since $v$ is primitive.
   - Why it might work: each step is a known, already-formalized $\mathrm{SL}_2$ move; the product of $\mathrm{SL}_n(\mathbb{Z})$ matrices stays in $\mathrm{SL}_n(\mathbb{Z})$; primitivity guarantees the final gcd is $1$.
   - Risk: bookkeeping for the block embedding and re-indexing (`Fin n` vs `Fin 2` blocks) is heavy in Lean; tracking that the gcd of the surviving prefix behaves as expected requires `Int.gcd_assoc`-style lemmas.

2. **Approach B — Smith normal form / Bézout matrix over a PID.**
   Invoke a general "primitive vector extends to a unimodular basis" argument: form any integer matrix whose first column is $v$, and use column operations (each an elementary $\mathrm{SL}_n(\mathbb{Z})$ transvection driven by Bézout) to reach $e_1$. This mirrors the Smith normal form reduction restricted to a single vector.
   - Why it might work: elementary transvections are determinant-$1$ and Mathlib has growing support for matrix reduction; the argument is uniform in $n$.
   - Risk: Mathlib's Smith-normal-form / PID matrix machinery may not expose exactly the primitive-vector-to-$e_1$ statement, forcing a from-scratch build of the transvection sequence and a termination argument.

### Key Difficulties

- Managing the inductive/recursive index shuffling in `Fin n` while keeping determinants exactly $1$ (sign discipline as in the parent proof).
- Proving primitivity is preserved (or correctly consumed): after each $2$-coordinate collapse, the gcd of the remaining coordinates must equal the gcd of the original block, ultimately reaching $1$.
- Assembling block-diagonal / embedded matrices as genuine `Matrix.SpecialLinearGroup (Fin n) ℤ` elements and reasoning about their `mulVec` action coordinatewise.

### What Would a Proof Need?

- Key lemma 1: a block-embedding lemma placing a `SpecialLinearGroup (Fin 2) ℤ` element into `SpecialLinearGroup (Fin n) ℤ` acting on two chosen coordinates, with the correct `mulVec` action and preserved determinant $1$.
- Key lemma 2: a gcd-collapse invariant — applying the parent's `bezoutMatrix` block turns $(x,y)$ into $(\gcd x\,y, 0)$ so that after all steps the surviving coordinate is $\gcd(v_1,\dots,v_n)$.
- Technical requirements: `Int.gcd`, `IsCoprime` / primitivity phrased as `gcd = 1`, `Matrix.mulVec`, `Matrix.SpecialLinearGroup`, and a termination/induction schema on `n`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The base case ($n=2$) is already fully formalized and axiom-free in the parent gallery proof, giving a concrete, reusable building block.
- The generalization is a standard, well-understood mathematical fact (primitive vector extends to a unimodular basis), so the risk is engineering, not mathematical uncertainty.
- Mathlib supplies the needed gcd, `IsCoprime`, `Matrix.mulVec`, determinant, and `SpecialLinearGroup` infrastructure; the main cost is `Fin n` block bookkeeping and the induction.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 1–2 weeks
- If hard: unknown (if Mathlib's block-matrix / PID reduction support proves insufficient)

## References

### Papers
- M. Newman, *Integral Matrices*, Academic Press, 1972 — unimodular reduction and the matrix form of the Euclidean algorithm; classical source for primitive-vector-to-basis.
- D. S. Dummit, R. M. Foote, *Abstract Algebra*, Wiley, 2004 — Smith normal form and modules over PIDs, the algebraic backbone of the general case.

### Online Resources
- Mathlib documentation for `Matrix.SpecialLinearGroup` and `Int.gcd` — the target namespaces for the formalization.

### Mathlib
- `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup` — the `SpecialLinearGroup (Fin n) ℤ` group and its `mulVec` action.
- `Mathlib.RingTheory.Int.Basic` / `Int.gcdA`, `Int.gcdB`, `Int.gcd_eq_gcd_ab` — Bézout coefficients driving each reduction step.
- `Mathlib.Data.Matrix.Basic` / `Matrix.mulVec`, `Matrix.det_fin_two_of` — matrix-vector action and $2\times2$ determinant used in the base case.
- `Mathlib.RingTheory.Coprime.Basic` — `IsCoprime` and the primitivity/`gcd = 1` bridge.

## Metadata

```yaml
tags:
  - number-theory
  - bezout-identity
  - euclidean-algorithm
  - linear-algebra
  - special-linear-group
  - unimodular-matrix
  - gcd
  - research
related_proofs:
  - bezout-identity-oq-01-oq-02
difficulty: medium
source: generalization
created: 2026-07-09T16:43:19-07:00
```
