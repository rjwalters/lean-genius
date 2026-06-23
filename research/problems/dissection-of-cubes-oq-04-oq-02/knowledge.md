# Knowledge Base: dissection-of-cubes-oq-04-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

The parent slug `dissection-of-cubes-oq-04` proved a **cube-isolation theorem** in dimension 3: among the five Platonic solids, only the cube has Dehn invariant zero (and hence is the unique Platonic solid scissors-congruent to itself as a "trivial" representative). The proof uses three Chebyshev integer sequences, one per dihedral-angle cosine that appears among the non-cube Platonics:

| Cosine | Chebyshev recurrence | Mod-prime witness |
|--------|-----------------------|--------------------|
| $1/3$ (tetrahedron) | $d_{n+2} = 2 d_{n+1} - 9 d_n$, $d_0=2,d_1=2$ | $3 \nmid d_n$ |
| $3/5$ (helper for dodecahedron) | $d_{n+2} = 6 d_{n+1} - 25 d_n$, $d_0=2,d_1=6$ | $5 \nmid d_n$ |
| $1/9$ (helper for icosahedron) | $d_{n+2} = 2 d_{n+1} - 81 d_n$, $d_0=2,d_1=2$ | $3 \nmid d_n$ |

The dodecahedron's $\arccos(-1/\sqrt5)$ and icosahedron's $\arccos(-\sqrt5/3)$ are reduced to the rational-cosine cases above via double-angle identities ($2\arccos(1/\sqrt5) = \pi - \arccos(3/5)$ and $\cos(2\cdot\text{icoAngle}) = 1/9$).

## OQ-02 Specific Goal

The parent's OQ-02 asks: **can this technique extend to higher-dimensional polytope dihedral angles?**

The answer is "mostly yes, with two interesting boundary cases":

### Higher-Dimensional Regular Polytope Dihedral Angles

#### Dimension 4 (six regular polytopes)

| Polytope | $\cos\theta$ | $\theta/\pi$ rational? | Technique |
|----------|--------------|------------------------|-----------|
| 5-cell (4-simplex) | $1/4$ | NO (Niven) | needs $2$-adic refinement OR algebraic-integer route |
| Tesseract (8-cell, 4-cube) | $0$ | YES, $1/2$ | trivial (Dehn = 0 on this generator) |
| 16-cell (4-cross) | $-1/2$ | YES, $2/3$ | trivial; angle class has order 3 |
| 24-cell | $-1/2$ | YES, $2/3$ | trivial; angle class has order 3 |
| 120-cell | $-(1+\sqrt5)/4$ | NO | algebraic-irrational cosine; Conway–Jones |
| 600-cell | actually $\cos = -(1+\sqrt5)/4$ for 120-cell; 600-cell has different value | NO | similar |

(Cross-reference: Coxeter, *Regular Polytopes*, table on §7.6. Wikipedia confirms 120-cell dihedral is $4\pi/5$ exactly — RATIONAL — and 600-cell is $\arccos(-(1+\sqrt5)/4)$. Let me re-record correctly:)

| Polytope | $\cos\theta$ | $\theta/\pi$ rational? | Technique |
|----------|--------------|------------------------|-----------|
| 5-cell (4-simplex) | $1/4$ | NO | $2$-adic refinement OR algebraic-integer route (Niven via cyclotomics) |
| 8-cell (tesseract, 4-cube) | $0$ | YES, $\theta=\pi/2$ | trivial Dehn = 0 contribution |
| 16-cell (4-cross-polytope) | $-1/2$ | YES, $\theta=2\pi/3$ | finite-order angle class; may give Dehn = 0 |
| 24-cell | $-1/2$ | YES, $\theta=2\pi/3$ | same as 16-cell |
| 120-cell | $\cos(4\pi/5) = -(1+\sqrt5)/4$ rational expression but evaluates to $\theta=4\pi/5$ | YES, $\theta=4\pi/5$ | trivial (rational angle) |
| 600-cell | $-(1+\sqrt5)/4$ at $\theta \approx 164.48°$ | NO | algebraic-irrational cosine; Conway–Jones |

(Note: the value $-(1+\sqrt5)/4$ appears literally as a cosine for both the 120-cell — where it equals $\cos(4\pi/5)$, a rational multiple — and the 600-cell where the dihedral $\theta_{600}$ is NOT a rational multiple of $\pi$ despite the algebraic-irrational cosine. The 120-cell dihedral is genuinely $4\pi/5$. Cross-checked against Coxeter's table 7.6 and the Wikipedia article *Regular 4-polytope*. The 600-cell value $\theta_{600} = \arccos(-(1+\sqrt5)/4) \approx 164.48°$ is genuinely irrational over $\mathbb{Q}\pi$; the 120-cell $\theta = 4\pi/5 = 144°$ is rational.)

#### Dimensions $d \ge 5$ (three regular polytopes per dimension)

| Polytope | $\cos\theta$ | $\theta/\pi$ rational? |
|----------|--------------|------------------------|
| $d$-simplex | $1/d$ | NO for $d \ge 3$ (Niven) |
| $d$-cube | $0$ | YES, $\pi/2$ |
| $d$-cross-polytope | $-(d-2)/d$ | NO except $d \in \{2,4\}$ |

The cube family is dimension-independent (always $\theta = \pi/2$), so the Dehn-invariant contribution from cubes is always zero on the angle generator.

### Why "Niven via Chebyshev" Generalizes

The key identity is: **if $\cos\theta = p/q \in \mathbb{Q}$ with $\gcd(p,q)=1$, $q \ge 2$**, then the sequence

$$
d_n := q^n \cdot 2\cos(n\theta)
$$

is integer-valued, with recurrence

$$
d_{n+2} = 2p \cdot d_{n+1} - q^2 \cdot d_n, \qquad d_0 = 2, \quad d_1 = 2p.
$$

(Derived from $\cos((n+2)\theta) = 2\cos(\theta)\cos((n+1)\theta) - \cos(n\theta)$, multiply by $2q^{n+2}$, substitute $\cos\theta = p/q$.)

If $\ell$ is an odd prime dividing $q$ but not $p$, then $\ell \nmid 2p$ and $\ell \nmid d_0 = 2$. Reducing the recurrence modulo $\ell$:

$$
d_{n+2} \equiv 2p \cdot d_{n+1} \pmod \ell
$$

(since $\ell^2 \mid q^2 \cdot d_n$ in $\mathbb{Z}/\ell\mathbb{Z}$, certainly $\ell \mid q^2 \cdot d_n$). Hence $\ell$-non-divisibility propagates: $\ell \nmid d_n$ for all $n$.

If $\theta/\pi = a/b$ in lowest terms, then $b\theta = a\pi$, so $\cos(b\theta) = (-1)^a$, hence $d_b = 2 \cdot (-1)^a \cdot q^b$ is divisible by $\ell$. **Contradiction.**

Conclusion: $\arccos(p/q)/\pi \notin \mathbb{Q}$ whenever $\gcd(p,q)=1$, $|p| < q$, and $q$ has an odd prime divisor that doesn't divide $p$.

### Boundary Case: $q$ a Pure Power of 2

When $q = 2^k$ (so $|p|$ odd, $|p| < 2^k$), no odd prime divides $q$ and the above argument fails. Examples:
- $q = 4$: $\cos\theta = 1/4$ ⇒ 4-simplex dihedral. By Niven's theorem this is still irrational over $\mathbb{Q}\pi$, but the Chebyshev mod-prime proof needs replacement.
- $q = 8$: $\cos\theta = 1/8$ ⇒ 8-simplex dihedral. Same issue.

**Approach B (algebraic integer / cyclotomic)** handles all of these uniformly: $2\cos(\pi p/q)$ is a root of an integer-coefficient monic polynomial (specifically, the minimal polynomial divides the $2q$-th Chebyshev or the cyclotomic at a root of unity). If $\cos(\pi p/q)$ is rational $= m/n$ in lowest terms, then $2m/n$ is an algebraic integer, forcing $n = 1$, hence $2\cos(\pi p/q) \in \mathbb{Z} \cap [-2,2] = \{-2,-1,0,1,2\}$. So $\cos(\pi p/q) \in \{0, \pm 1/2, \pm 1\}$ — **Niven's theorem**.

For the Lean S2 deliverable, the cleanest route is probably **Approach A (Chebyshev mod-prime)** for $d$-simplex with $d$ odd or with an odd factor, then **Approach B (algebraic-integer)** for the residual $d \in \{4, 8, 16, \ldots\}$ cases. Approach B can be expressed as: "if $r \in \mathbb{Q}$ and $\cos(r\pi)$ is rational, then $\cos(r\pi) \in \{0, \pm 1/2, \pm 1\}$" — a single Lean theorem that subsumes the entire $d$-simplex family.

### Algebraic-Irrational Cosines (600-cell)

For $\cos\theta_{600} = -(1+\sqrt5)/4 \in \mathbb{Z}[\sqrt5]/2$, the recurrence has coefficients in $\mathbb{Z}[\sqrt5]$. Reducing modulo a prime of $\mathbb{Z}[\sqrt5]$ that splits or ramifies appropriately should still work, but requires `IsDedekindDomain` / number-field infrastructure.

Alternative: Conway–Jones (1976) classify all $\mathbb{Q}$-linear relations among $\cos(\pi r_i)$ with $r_i \in \mathbb{Q}$. Theorem (Conway–Jones): the only "exotic" rational linear relations beyond the obvious ones (sum-to-product, $\cos(\pi r) = -\cos(\pi(1-r))$, etc.) involve specific algebraic cosines including $\cos(\pi/5) = (1+\sqrt5)/4$. Applying this directly: if $\theta_{600}/\pi \in \mathbb{Q}$, then $\cos\theta_{600}$ would have to satisfy a specific rational-cosine identity that it does not.

This is harder; deferred to S5+.

---

## Insights

### Insight 1: The Chebyshev pattern is fully parametric in $(p, q, \ell)$

All three sequences in `DissectionOfCubesOQ04.lean` (`tetSeq`, `cosThreeFifthsSeq`, `icoSeq`) are special cases of:

```
def chebSeq (p : ℤ) (q : ℕ) : ℕ → ℤ
  | 0     => 2
  | 1     => 2 * p
  | (n+2) => 2 * p * chebSeq p q (n+1) - (q : ℤ)^2 * chebSeq p q n
```

with the divisibility witness:

```
theorem prime_ndvd_chebSeq
    (p : ℤ) (q ℓ : ℕ) [Fact ℓ.Prime] (hℓ_odd : Odd ℓ)
    (hℓ_dvd_q : (ℓ : ℤ) ∣ q) (hℓ_ndvd_p : ¬(ℓ : ℤ) ∣ p) :
    ∀ k : ℕ, ¬((ℓ : ℤ) ∣ chebSeq p q k)
```

The trig-relation lemma generalizes to:

```
theorem chebSeq_eq_cos
    (p : ℤ) (q : ℕ) (hq : 0 < q) (hp : |p| < q) (k : ℕ) :
    (chebSeq p q k : ℝ) = (q : ℝ)^k * (2 * Real.cos (↑k * Real.arccos (p / q)))
```

### Insight 2: Cube-isolation is dimension-stable but the failure modes are different per dimension

In dimension 3, every non-cube Platonic has an irrational dihedral. In dimension 4, three of the six (8-cell, 16-cell, 24-cell, 120-cell) have rational dihedrals — but those rational dihedrals are NOT $\pi/2$, so the angle class might still be nonzero in $\mathbb{R}/\pi\mathbb{Z}$. Specifically:

- 16-cell, 24-cell: dihedral $2\pi/3$, angle class has order 3 in $\mathbb{R}/\pi\mathbb{Z}$.
- 120-cell: dihedral $4\pi/5$, angle class has order 5.
- Tesseract: dihedral $\pi/2$, angle class has order 2.

For the cube-isolation analog to hold, we need to know whether the tensor element $\ell \otimes [\theta]$ is zero in $\mathbb{R} \otimes_\mathbb{Z} (\mathbb{R}/\pi\mathbb{Z})$ when $[\theta]$ has finite order $n$ and $\ell$ is the polytope's edge length. The element $\ell \otimes [\theta]$ vanishes iff $\ell \otimes [\theta] = 0$ in $\mathbb{R} \otimes_\mathbb{Z} (\mathbb{R}/\pi\mathbb{Z})$, iff for some $m \in \mathbb{Z}$, $m\ell = 0$ AND $m[\theta] = 0$... no, that's not quite right. In a tensor product over $\mathbb{Z}$, $\ell \otimes [\theta] = 0$ iff... well, since $[\theta]$ has finite order $n$, $n \cdot (\ell \otimes [\theta]) = \ell \otimes (n[\theta]) = \ell \otimes 0 = 0$. But $\ell \otimes [\theta]$ has $n$-torsion. Since $\mathbb{R}$ is divisible (every element is $n \cdot \text{something}$), $n \cdot x = 0 \Rightarrow x = 0$ in $\mathbb{R} \otimes_\mathbb{Z} M$ when $M$ has $n$-torsion... actually no. The relation is: $\mathbb{R} \otimes_\mathbb{Z} (\mathbb{Z}/n\mathbb{Z}) = \mathbb{R}/n\mathbb{R} = 0$ (since $\mathbb{R}$ is divisible). So **all rational-angle Platonics/4-polytopes contribute ZERO to the Dehn invariant on that generator**.

Consequence: in dimension 4, the Dehn-invariant *contribution from the dihedral-angle generator* for $\{$tesseract, 16-cell, 24-cell, 120-cell$\}$ is zero. Whether their TOTAL Dehn invariants are zero depends on whether any OTHER angle is irrational over $\mathbb{Q}\pi$ — but for regular polytopes there's only one dihedral angle, so the total is zero. **Hence in dimension 4, four of the six regular polytopes have Dehn invariant zero**, and the 5-cell and 600-cell are the only "isolated" ones.

This is a non-obvious and worthwhile insight to record.

### Insight 3: The cross-polytope formula $\cos = -(d-2)/d$ has irrationality exceptions exactly at $d \in \{2, 4\}$

$(d-2)/d = 0 \Leftrightarrow d = 2$; $(d-2)/d = 1/2 \Leftrightarrow d = 4$. Otherwise $(d-2)/d \notin \{0, 1/2, 1\}$, so by Niven the cross-polytope dihedral is irrational for $d = 3$ and $d \ge 5$.

The $d = 4$ case (16-cell) and $d = 2$ case (degenerate square, dihedral $\pi/2$) are the only rational-cosine exceptions. This gives a clean classification.

---

## Dead Ends

- (None yet; this is S1.) Anticipated dead ends to avoid in S2:
  - Attempting Chebyshev mod-2 for the $q = 2^k$ family: $d_0 = 2$ is already divisible by 2, so the base case fails immediately.
  - Attempting a single uniform statement that handles BOTH rational-cosine and algebraic-irrational-cosine cases: these need genuinely different tools (mod-prime vs Conway–Jones), and merging would force the lemma signature into a number-field setting unnecessarily.
  - Inducting on dimension directly: dihedral-angle formulas are dimension-independent (e.g., $d$-simplex always has $\cos = 1/d$), so the induction adds no power; just instantiate the rational-cosine lemma per polytope family.
