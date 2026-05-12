# Problem: Dehn Invariant Technique for Higher-Dimensional Polytope Dihedral Angles

**Slug**: dissection-of-cubes-oq-04-oq-02
**Created**: 2026-05-12T14:45:46-07:00
**Status**: Active (S1 OBSERVE, researcher-8)
**Source**: gallery-gap (parent `dissection-of-cubes-oq-04`)

## Problem Statement

### Formal Statement

Let $\theta$ be the dihedral angle of a regular convex polytope in dimension $d \ge 4$. The proof of `DissectionOfCubesOQ04.lean` proved $\theta/\pi \notin \mathbb{Q}$ for every Platonic solid (3D) except the cube, using Chebyshev-style integer recurrences. Question: does the same technique extend to higher dimensions?

Specifically, prove:

$$
\forall d \ge 3 : \quad \theta_d^{\text{simplex}} / \pi \notin \mathbb{Q}, \qquad \text{where } \cos\theta_d^{\text{simplex}} = \tfrac{1}{d}.
$$

$$
\forall d \ge 5 : \quad \theta_d^{\text{cross}} / \pi \notin \mathbb{Q}, \qquad \text{where } \cos\theta_d^{\text{cross}} = -\tfrac{d-2}{d}.
$$

$$
\theta_{600\text{-cell}} / \pi \notin \mathbb{Q}, \qquad \text{where } \cos\theta_{600\text{-cell}} = -\tfrac{1+\sqrt5}{4}.
$$

### Plain Language

The cube is the unique Platonic solid with dihedral angle $\pi/2$ — every other Platonic solid has an irrational-multiple-of-$\pi$ dihedral, which gives a nonzero Dehn invariant and obstructs scissors-congruence to a cube. We want to know whether the same Chebyshev-integer-sequence trick used in dimension 3 can prove irrationality for the analogous dihedral angles in dimensions 4 and higher, where each dimension introduces a new family of regular polytopes.

### Why This Matters

In dimension 4, six regular convex polytopes exist (5-cell, tesseract, 16-cell, 24-cell, 120-cell, 600-cell); in dimensions $d \ge 5$ exactly three exist (the $d$-simplex, $d$-cube, $d$-cross-polytope). Extending the dimension-3 cube-isolation theorem to $d \ge 4$ would:

1. Generalize Hilbert's 3rd problem analog: which regular $d$-polytopes are scissors-congruent to the $d$-cube?
2. Stress-test the Chebyshev-sequence method against (a) rational-cosine families parametrized by $d$ (existing technique applies), (b) algebraic-irrational cosines like $-(1+\sqrt5)/4$ for the 600-cell (the technique does NOT directly apply — needs Conway–Jones).
3. Provide a Lean-verified library of dihedral-angle irrationality facts indexed by polytope type.

## Known Results

### What's Already Proven (in this repository)

- `DissectionOfCubesOQ04.lean` proves: arccos($1/3$), arccos($3/5$), arccos($1/9$), arccos($-1/\sqrt5$), arccos($-\sqrt5/3$) are all irrational multiples of $\pi$.
- `DissectionOfCubesOQ02OQ02.lean` proves: `tmul_infinite_order_ne_zero` (the flatness step that turns "infinite-order angle class" into "nonzero Dehn invariant").
- Result: among the 5 Platonic solids, only the cube has Dehn invariant zero (Theorem `cube_isolated_dehn_invariant`).
- The general blueprint is: **(rational cosine + Chebyshev recurrence + mod-prime divisibility) ⇒ irrational angle / π ⇒ infinite order in $\mathbb{R}/\pi\mathbb{Z}$ ⇒ nonzero $D$**.

### What's Still Open (this slug)

1. **General Niven**: For any coprime integers $p,q$ with $q \ge 3$ odd (or more generally $q$ having an odd prime factor) and $|p| < q$, prove `arccos(p/q)/π ∉ ℚ` via a uniform Chebyshev recurrence $d_{n+2} = 2p\,d_{n+1} - q^2 d_n$ with $d_0 = 2,\ d_1 = 2p$.
2. **$d$-simplex family**: Apply Niven with $p=1, q=d$ to obtain $\arccos(1/d)/\pi \notin \mathbb{Q}$ for every $d \ge 3$ (instantiating $d=3$ recovers `arccos(1/3)`).
3. **$d$-cross-polytope family**: Apply Niven with $p = -(d-2), q = d$ (after handling the trivial $d=2,4$ rational cases) for every $d \ge 5$ and $d = 3$. Note: the cross-polytope dihedral $\arccos((2-d)/d)$ becomes a rational multiple of $\pi$ exactly when $d=2$ ($\pi/2$) or $d=4$ ($2\pi/3$); these cases need separate "rational angle ⇒ Dehn-invariant zero on this generator" arguments.
4. **600-cell**: $\cos = -(1+\sqrt5)/4$ is an algebraic irrational. The Chebyshev mod-prime approach in $\mathbb{Z}$ does not extend; instead, one needs either (a) the Conway–Jones theorem (1976) classifying rational linear combinations $\sum a_i \cos(\pi r_i) = 0$ with $r_i \in \mathbb{Q}$, or (b) a direct argument in $\mathbb{Z}[\sqrt5]$ (the integer ring of $\mathbb{Q}(\sqrt5)$).

### Our Goal

S1 OBSERVE deliverable (this session): catalogue the dihedral-angle landscape in dimensions $\ge 4$, classify each case by whether the existing Chebyshev technique applies, and propose 2–3 narrow S2 targets that are clearly within reach of the existing infrastructure.

S2+ goal: build a small "Niven" library in `proofs/Proofs/NivenRationalCosine.lean` that proves the rational-cosine case once and instantiates it for every $d \ge 3$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `dissection-of-cubes-oq-04` | Direct parent; Chebyshev technique invented here | Chebyshev integer recurrence + mod-3 / mod-5 divisibility |
| `dissection-of-cubes-oq-02-oq-02` | Dehn-invariant infrastructure (`tmul_infinite_order_ne_zero`) | $\mathbb{R}$-flatness of $\mathbb{Z}$-modules |
| `dissection-of-cubes-oq-02` | Dehn invariant for tetrahedron | arccos(1/3) Chebyshev sequence |
| `angle-trisection-cos-20-gal-oq-01-oq-03` | arccos(1/2)/π = 1/3 (rational case, opposite end of spectrum) | Galois theory + cyclotomic polynomials |
| `nth-root-irrational-oq-03` (PR #18275) | Hermite-Lindemann/Lindemann-Weierstrass survey — different irrationality flavor | Transcendence vs algebraic |

## Initial Thoughts

### Potential Approaches

1. **Approach A (Uniform Niven via Chebyshev)**:
   For any coprime $p, q$ with $q$ having an odd prime factor $\ell \nmid p$, define $d_n = q^n \cdot 2\cos(n\theta)$ where $\theta = \arccos(p/q)$. Then $d_n \in \mathbb{Z}$, $d_{n+2} = 2p \cdot d_{n+1} - q^2 \cdot d_n$, and reducing modulo $\ell$ gives $d_{n+2} \equiv 2p \cdot d_{n+1} \pmod \ell$. If $\ell \nmid 2p$ and $\ell \nmid d_0 = 2$ (i.e. $\ell \ne 2$, which is automatic), then $\ell \nmid d_n$ for all $n$. But if $\theta/\pi = a/b$ with $\gcd(a,b)=1$, then $b\theta \in a\pi\mathbb{Z}$, so $\cos(b\theta) = \pm 1$, and $d_b = \pm 2 q^b$ is divisible by $\ell$ — contradiction.
   - Why it might work: this is the literal generalization of the three concrete sequences (`cosThreeFifthsSeq`, `tetSeq`, `icoSeq`) already proven; the structural pattern factors out cleanly.
   - Risk: the special case $q = 2^k$ (no odd prime factor) is not covered. For $q=4$ (4-simplex dihedral) we need a different argument — either a $2$-adic refinement, or invoke the cyclotomic / algebraic-integer route directly.

2. **Approach B (Lehmer / Niven via Algebraic Integers)**:
   $2\cos(\pi p/q)$ is an algebraic integer (root of the $2q$-th Chebyshev / cyclotomic polynomial). If it equals a rational $r = m/n$ in lowest terms, then $n=1$, so $2\cos(\pi p/q) \in \mathbb{Z} \cap [-2, 2] = \{-2,-1,0,1,2\}$. This is Niven's theorem in one line.
   - Why it might work: Mathlib has `IsAlgebraic` and cyclotomic-polynomial infrastructure; the statement is short.
   - Risk: extracting "is an algebraic integer" cleanly from `Real.cos` and a rational $\theta/\pi$ may require detouring through complex `Polynomial.IsRoot (cyclotomic ...)`. Verifying the bound $|2\cos| \le 2$ is trivial; verifying integrality may take more API.

3. **Approach C (Cross-polytope rational cases as direct Dehn = 0)**:
   For $d = 4$ cross-polytope (16-cell), dihedral is $2\pi/3$; angle class $[2\pi/3] \in \mathbb{R}/\pi\mathbb{Z}$ has order $3$ (since $3 \cdot 2\pi/3 = 2\pi \equiv 0$). So the Dehn invariant for the 16-cell is a length-times-finite-order element; need to check whether `tmul` lands in $\mathbb{R} \otimes_{\mathbb{Z}} (\mathbb{R}/\pi\mathbb{Z})$ at zero or not. (Length on 16-cell edges times finite-order angle = potentially zero in the tensor.)
   - Why it might work: makes the cross-polytope family decompose cleanly into (rational-angle, finite-order, possibly-zero-Dehn) vs (irrational-angle, infinite-order, nonzero-Dehn) cases.
   - Risk: the 16-cell case may actually be Dehn-zero (need to check); literature on 4D Dehn invariants is sparser.

### Key Difficulties

- **$q$ a pure power of 2**: $d$-simplex with $d=4$ gives $\cos = 1/4$; the mod-prime method needs an odd prime divisor of $q$. Either reformulate via $2$-adic valuation, or invoke Niven via algebraic-integer route (Approach B).
- **Algebraic-irrational cosines (600-cell)**: $\cos = -(1+\sqrt5)/4$ lives in $\mathbb{Z}[\sqrt5]/2$; the recurrence has $\mathbb{Z}[\sqrt5]$-integer coefficients, not $\mathbb{Z}$. Either work over $\mathbb{Z}[\sqrt5]$ throughout (requires `IsNumberField` infrastructure), or use Conway–Jones directly.
- **Cross-polytope rational-angle cases ($d=2,4$)**: dihedral angle is a rational multiple of $\pi$, so the angle class has finite order — these are NOT counterexamples to cube-isolation in higher dimensions; they need to be handled separately to determine whether the cross-polytope has zero Dehn invariant in those specific dimensions.

### What Would a Proof Need?

For the cleanest S2 win, we focus on Approach A's $d$-simplex specialization:

- **Key lemma A.1**: `niven_chebyshev : ∀ (p : ℤ) (q : ℕ) (ℓ : ℕ) [Fact ℓ.Prime], Odd ℓ → ℓ ∣ q → ¬(ℓ : ℤ) ∣ p → ¬∃ r : ℚ, Real.arccos ((p : ℝ) / q) = r * Real.pi`. Proof structure mirrors `arccos_three_fifths_irrational` from `DissectionOfCubesOQ04.lean` but is parametrized.
- **Key lemma A.2**: `simplex_dihedral_irrational : ∀ d : ℕ, 3 ≤ d → ¬∃ r : ℚ, Real.arccos (1 / (d : ℝ)) = r * Real.pi`. Apply Niven with $p=1, q=d$: any odd prime divisor of $d$ works; if $d$ is a power of 2 (i.e. $d=4, 8, 16, \ldots$), need Approach B.
- **Key lemma A.3**: `simplex_dehn_ne_zero : ∀ d ≥ 3, D(d_simplex) ≠ 0`. Apply A.2 + `tmul_infinite_order_ne_zero` exactly as in the parent proof.

For the 600-cell, a single proof in $\mathbb{Z}[\sqrt5]$ would suffice; this is the "algebraic-irrational cosine" S3+ target after Approach A is in place.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The three Lean-proved sequences in `DissectionOfCubesOQ04.lean` follow a single template; abstracting it should be ~150–250 LOC.
- The $d$-simplex case with $d$ having an odd prime factor falls out immediately; $d \in \{4, 8, 16, \ldots\}$ remains.
- The 600-cell ($\sqrt5$-cosine) is genuinely harder and should be deferred to a separate iteration.
- The cross-polytope family decomposes into a clean rational-vs-irrational dichotomy.

**Estimated Effort**:
- S2 (Niven abstraction lemma + $d$-simplex instantiation for odd-$d \ge 3$): 1 session, ~200 LOC.
- S3 ($d$-simplex for $d \in \{4, 8, 16, \ldots\}$ via Approach B or 2-adic): 1–2 sessions, ~150–300 LOC.
- S4 (cross-polytope full classification): 1 session, ~150 LOC.
- S5 (600-cell via $\mathbb{Z}[\sqrt5]$): 2–3 sessions, ~400 LOC.

## References

### Papers

- Niven, I. (1956), *Irrational Numbers*, Carus Mathematical Monographs No. 11, MAA — Theorem 3.9 on rational cosines.
- Conway, J. H. & Jones, A. J. (1976), "Trigonometric Diophantine Equations (On Vanishing Sums of Roots of Unity)", *Acta Arith.* 30, 229–240 — algebraic-irrational cosines $\Leftrightarrow$ specific finite list including $(1+\sqrt5)/4$.
- Lehmer, D. H. (1933), "A note on trigonometric algebraic numbers", *Amer. Math. Monthly* 40, 165–166 — $2\cos(\pi r)$ is an algebraic integer.
- Dehn, M. (1900), "Über raumgleiche Polyeder", *Nachr. Akad. Wiss. Göttingen* 1900, 345–354 — original Dehn-invariant paper.
- Coxeter, H. S. M. (1973), *Regular Polytopes*, Dover — dihedral angle table (§7.6).

### Online Resources

- https://en.wikipedia.org/wiki/Regular_polytope#Regular_convex_polytopes — dihedral-angle table.
- https://en.wikipedia.org/wiki/600-cell — explicit $\cos = -(1+\sqrt5)/4$.
- https://en.wikipedia.org/wiki/Niven%27s_theorem — Niven's rational-cosine theorem statement.

### Mathlib

- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse` — `Real.arccos`, `cos_arccos`, `arccos_cos`.
- `Mathlib.RingTheory.Polynomial.Cyclotomic.Basic` — cyclotomic polynomials, `IsRoot`.
- `Mathlib.NumberTheory.NumberField.Basic` — for $\mathbb{Z}[\sqrt5]$ in the 600-cell case.
- `Mathlib.RingTheory.RootsOfUnity.Minpoly` — minimal polynomial of $2\cos(\pi r)$.

## Metadata

```yaml
tags:
  - geometry
  - dissection
  - dehn-invariant
  - hilbert-3
  - irrationality
  - chebyshev-recurrence
  - regular-polytopes
  - higher-dimensional
related_proofs:
  - dissection-of-cubes
  - dissection-of-cubes-oq-04
  - dissection-of-cubes-oq-02-oq-02
  - angle-trisection-cos-20-gal-oq-01-oq-03
difficulty: medium
source: gallery-gap
created: 2026-05-12T14:45:46-07:00
phase: S1-OBSERVE
researcher: researcher-8
```
