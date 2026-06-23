# gauss-wilson-non-cyclic-oq-01: Full Gauss–Wilson product formula from the 2-torsion characterization

**Parent gallery entry:** `gauss-wilson-non-cyclic` (`Proofs/GaussWilsonNonCyclic.lean`)
**Sibling OQ:** `gauss-wilson-non-cyclic-oq-03` (exact CRT count of square roots of unity; ACT iter 2)
**Tier:** B  **Significance:** 6  **Tractability:** 6  **Seeker tags:** cyclic-groups, group-theory, number-theory, wilson-gauss, zmod

## Open question (seeker phrasing)

> Can the full Gauss–Wilson product formula be derived from this 2-torsion characterization in a Lean 4 gallery entry?

## Formal statement

For every $n \geq 1$,
$$
\prod_{x \in (\mathbb{Z}/n\mathbb{Z})^\times} x \;=\;
\begin{cases}
-1 & \text{if } (\mathbb{Z}/n\mathbb{Z})^\times \text{ is cyclic}\\
\phantom{-}1 & \text{if } (\mathbb{Z}/n\mathbb{Z})^\times \text{ is non-cyclic}.
\end{cases}
$$

Equivalently, packaging the cyclic side with Mathlib's `ZMod.isCyclic_units_iff`:

$$
\prod_{x \in (\mathbb{Z}/n\mathbb{Z})^\times} x \;=\; -1
\quad\Longleftrightarrow\quad
n \in \{0,1,2,4\} \;\lor\; \exists p,m,\;p\text{ odd prime} \land m \geq 1 \land (n = p^m \lor n = 2p^m).
$$

The classical Wilson form $(n-1)! \equiv -1 \pmod n \iff n \in \{1\} \cup \mathrm{Primes}$ is the special-case projection through $\prod_{x \in (\mathbb{Z}/n\mathbb{Z})^\times} x.\mathrm{val} = (n-1)!$ when $n$ is prime (and is what `ZMod.wilsons_lemma` already proves in Mathlib).

## Why it matters

1. **Gallery completion.** The parent file proves only the *contrapositive group-theoretic core* (non-cyclic ⇒ 2-torsion ≥ 3). It does not produce the historic Gauss product formula. OQ-01 closes that gap and makes the gallery entry a complete formalization of Gauss's 1801 result (Disquisitiones Arithmeticae §78).

2. **A direct cyclic-vs-non-cyclic dichotomy.** The product is exactly $-1$ in the cyclic case and exactly $+1$ in the non-cyclic case. This is the cleanest known phrasing of when $\prod_{x \in G} x = 1$ for a finite abelian group $G$: the boundary is whether $|G[2]| = 2$ or $|G[2]| \geq 4$.

3. **Reuse outside this entry.** Provides a textbook-level Lean lemma `Finset.prod_univ_eq_neg_one_or_one_of_finite_commGroup` (or its specialization) that any future ZMod / Dirichlet-character / cyclotomic gallery entry can cite.

## Decomposition

OQ-01 splits cleanly into three independent sub-problems:

### OQ-01-A — Reduction to 2-torsion (abstract)
Prove the general lemma: for any finite commutative group $G$ (written multiplicatively),
$$
\prod_{x \in G} x \;=\; \prod_{x \in G,\,x^2=1} x.
$$
Mathlib already contains the key tool: `Finset.prod_involution` with the involution $x \mapsto x^{-1}$, which pairs every element of order $\neq 1,2$ with its distinct inverse so they multiply to $1$. The mapping is its own square and fixes exactly the 2-torsion.

**Status:** No prebuilt Mathlib lemma matches this exact statement, but `Finset.prod_involution` makes the proof ~10 lines. (Mathlib's `prod_univ_units_id_eq_neg_one` does this implicitly for `Kˣ` over an integral domain, getting $-1$ because $\{1,-1\}$ is *exactly* the 2-torsion in a domain. For a non-domain like `ZMod n` with $n$ composite, the 2-torsion can be larger.)

### OQ-01-B — Product over the 2-torsion
The 2-torsion $H = \{x \in G : x^2 = 1\}$ is itself a finite abelian group of exponent $\leq 2$; if non-trivial, it is an elementary abelian 2-group, hence $H \cong (\mathbb{Z}/2)^k$ for some $k \geq 0$. Two cases:

- **$k = 0$ (trivial $H$):** $\prod_{x \in H} x = 1$.
- **$k = 1$ ($H \cong \mathbb{Z}/2$):** $H = \{1, h\}$ for unique $h$ of order 2; $\prod = h$. In the setting of $G = (\mathbb{Z}/n\mathbb{Z})^\times$ with $n \geq 3$, the only candidate is $h = -1$, so $\prod = -1$.
- **$k \geq 2$ ($|H| \geq 4$):** $\prod_{x \in H} x = 1$. Proof: $H$ is symmetric under multiplication by any non-identity $h \in H$; pair $x \leftrightarrow xh$, each pair multiplies to $xh \cdot x = h$, and there are $|H|/2$ pairs, giving $h^{|H|/2}$. For $k \geq 2$, $|H|/2 = 2^{k-1}$ is even, so $h^{|H|/2} = 1$.

Equivalent additive argument: in the $\mathbb{F}_2$-vector space $(\mathbb{Z}/2)^k$, the sum of all elements is $(2^{k-1}, \ldots, 2^{k-1}) \equiv 0$ when $k \geq 2$.

### OQ-01-C — Identify the boundary on $(\mathbb{Z}/n\mathbb{Z})^\times$

By `ZMod.isCyclic_units_iff`:
- $G = (\mathbb{Z}/n\mathbb{Z})^\times$ is **cyclic** iff $n \in \{0,1,2,4\}$ or $n = p^m, 2p^m$ for odd prime $p$.
- In the cyclic case, $|G[2]| \leq 2$ (cyclic group has at most one element of order 2).
- In the non-cyclic case, the parent file's `card_sq_eq_one_ge_three` gives $|G[2]| \geq 3$. Combined with $G[2]$ being an elementary abelian 2-group (so $|G[2]|$ is a power of 2), we get $|G[2]| \geq 4$, hence OQ-01-B-k≥2 applies.

The cases unify as: the product is $-1$ exactly when $G[2] = \{1, -1\}$, which happens exactly when $G$ is cyclic (using $-1 \neq 1$ for $n \geq 3$, plus the small-case enumeration for $n \in \{1, 2, 4\}$).

## Approach map

Three independent Lean files, each shippable on its own:

| File | Content | Estimated LOC | Sorries |
|------|---------|--------------:|--------:|
| `GaussWilsonNonCyclicOQ01A.lean` | Abstract lemma `Finset.prod_univ_eq_prod_two_torsion` for any finite `CommGroup` | ~40 | 0 |
| `GaussWilsonNonCyclicOQ01B.lean` | Product over an elementary abelian 2-group of order ≥ 4 equals 1 | ~60 | 0–1 |
| `GaussWilsonNonCyclicOQ01.lean` | Main theorem: `prod_univ_units_zmod_eq_neg_one_iff_isCyclic` | ~80 | 0–2 |

**Total budget:** ~180 lines, 0–3 sorries (close in subsequent ACT sessions).

## Mathlib readiness (as of Mathlib v4.26.0)

- ✅ `Finset.prod_involution` — generic pairing lemma (already used by `prod_univ_units_id_eq_neg_one`)
- ✅ `ZMod.isCyclic_units_iff` — full characterization at `Mathlib/RingTheory/ZMod/UnitsCyclic.lean`
- ✅ `ZMod.wilsons_lemma` — prime case, `(p-1)! ≡ -1 (mod p)`
- ✅ `prod_univ_units_id_eq_neg_one` — integral domain case (`Mathlib/FieldTheory/Finite/Basic.lean`)
- ⚠️ No standalone `prod_univ_of_isCyclic` or `prod_univ_of_not_isCyclic` for general finite abelian groups
- ⚠️ Elementary abelian 2-group product = 1 (for $|H| \geq 4$) appears not to be packaged

## Sibling overlap with OQ-03

OQ-03 (exact count `#{x : x² = 1} = 2^(ω_odd(n) + ε₂(n))`) and OQ-01 (product formula) share the 2-torsion infrastructure but diverge in the consumption:

- OQ-03 needs the **cardinality** of the 2-torsion as a function of $n$.
- OQ-01 needs only the **dichotomy** $|G[2]| \in \{1, 2, \geq 4\}$ together with the product over the 2-torsion.

OQ-01 is *strictly easier* than OQ-03 in the sense that the cyclic / non-cyclic dichotomy is already in Mathlib (`isCyclic_units_iff`), while the exact count requires hand-crafted CRT machinery. OQ-01 can ship without waiting for OQ-03 progress.

## Suggested S2 next action

S2 ACT: create `proofs/Proofs/GaussWilsonNonCyclicOQ01A.lean` (Phase A only, the abstract `prod_univ_eq_prod_two_torsion` lemma). This is a single self-contained statement with a ~30-line proof using `Finset.prod_involution` and no dependency on the parent file. Build verification should be straightforward (uses only `Mathlib.Algebra.BigOperators.Group.Finset.Basic`).

After S2 lands, S3 attacks Phase B (elementary abelian 2-group product), and S4 assembles Phase C on top.

## References

- Gauss, C. F. (1801). *Disquisitiones Arithmeticae* §78. The original statement of the full product formula.
- Hardy & Wright (1979). *An Introduction to the Theory of Numbers*, §6.3 (Wilson's theorem and Gauss's generalization).
- OEIS A103131 (sign of Gauss product as a function of $n$; equivalently $\chi_2(n)$ where $\chi_2$ is the unique primitive real character of conductor dividing 4 for the cyclic case).
