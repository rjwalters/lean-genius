# Problem: Additive Exponent — n·x = 0 in a Finite Abelian Group of Order n

**Slug**: lagrange-theorem-oq-07-oq-02
**Created**: 2026-06-23
**Status**: Active
**Source**: gallery-gap <!-- open question of verified parent lagrange-theorem-oq-07 (multiplicative exponent | order) -->

## Problem Statement

### Formal Statement

Let $G$ be a finite **additive** abelian group with $|G| = n$. Then for every $x \in G$:

$$
n \cdot x \;=\; 0 .
$$

Equivalently, in multiplicative notation $g^{|G|} = 1$ for all $g$ — the additive transcription of the parent's exponent-divides-order result. The parent `lagrange-theorem-oq-07` establishes (multiplicatively) that the order of every element, and hence the exponent of the group, divides $|G|$, so $g^{|G|}=1$. This open question asks for the clean **additive** statement $n \bullet x = 0$, the form used in module theory and in additive number theory, recovering the additive analogues of Fermat/Euler.

### Plain Language

Lagrange's theorem says the size of any subgroup divides the size of the group. A direct corollary: if you take any element and "repeat" the group operation $|G|$ times, you return to the identity. In a group written additively (where the operation is $+$ and the identity is $0$), that statement reads $n \cdot x = 0$ — adding $x$ to itself $n$ times always gives zero, where $n$ is the number of elements. This problem asks to state and prove this additive version in Lean, the form that matches how finite abelian groups appear in module theory and number theory (e.g. "$n$ kills the group $\mathbb{Z}/n\mathbb{Z}$").

### Why This Matters

The additive corollary is the workhorse behind: the additive analogue of Fermat's little theorem ($n \cdot x = 0$ in $\mathbb{Z}/n$), the fact that a finite abelian group of order $n$ is a module over $\mathbb{Z}/n\mathbb{Z}$, torsion bounds in the structure theory of finite abelian groups, and elementary results in additive combinatorics. While Mathlib has the multiplicative `pow_card_eq_one` and `orderOf_dvd_card`, the explicitly *additive* `n • x = 0` phrasing (with $n = $ `Nat.card G` / `Fintype.card G`) is the directly citable statement for module-flavored downstream work. Shipping it bridges the parent's group-theoretic result to the additive/module setting.

## Known Results

### What's Already Proven

- Multiplicative exponent-divides-order and `pow_card_eq_one : g ^ (Fintype.card G) = 1` — gallery parent `lagrange-theorem-oq-07` and Mathlib.
- `orderOf_dvd_card`, `orderOf_dvd_of_pow_eq_one`, exponent API (`Monoid.exponent`, `Group.exponent_dvd_card`) — Mathlib.
- Additive ↔ multiplicative bridging: `Multiplicative`/`Additive` type equivalences and `AddSubgroup`/`Subgroup` correspondence; `nsmul`/`pow` translation lemmas (`ofMul_pow`, `toMul_nsmul`, etc.) — Mathlib.
- For the additive side directly: `AddMonoid.nsmul`, `addOrderOf`, `addOrderOf_dvd_card` (`addOrderOf_dvd_natCard`) — Mathlib.

### What's Still Open (here)

- The clean top-level additive theorem `∀ x : G, (Nat.card G) • x = 0` (equivalently with `Fintype.card`) for a finite `AddCommGroup` (or `AddGroup`) `G`.
- The corollary instances: $n \cdot x = 0$ in `ZMod n` and in an arbitrary finite abelian group, framed as additive Fermat/Euler.

### Our Goal

Ship `(Nat.card G) • x = 0` for finite `G` as a verified, 0-axiom theorem — either by transporting the parent's `pow_card_eq_one` through the `Additive`/`Multiplicative` equivalence, or directly from `addOrderOf_dvd_natCard` + `addOrderOf_nsmul_eq_zero`-style lemmas. Provide the `ZMod n` specialization as a sanity corollary.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| lagrange-theorem-oq-07 | direct parent (multiplicative exponent | order) | `orderOf_dvd_card`, `pow_card_eq_one` |
| lagrange-theorem | base Lagrange/coset API | subgroup index, `Subgroup.card_subgroup_dvd_card` |
| euler-totient-oq-05 | sibling additive/Euler corollaries | `ZMod`, `nsmul` |

## Initial Thoughts

### Potential Approaches

1. **Transport via `Additive`/`Multiplicative`** (primary): apply the parent/Mathlib `pow_card_eq_one` to `Multiplicative G`, then translate $g^{n} = 1$ back to $n \bullet x = 0$ using the `toMul`/`ofMul` and `pow`↔`nsmul` correspondence lemmas.
   - Why it might work: reuses the already-proven multiplicative result verbatim; the equivalence lemmas are mechanical.
   - Risk: friction in the `Additive`/`Multiplicative` cast lemma names (`ofMul_pow`, `Additive.forall`, etc.).

2. **Direct additive proof** (alternative, cleaner): use `addOrderOf_dvd_natCard : addOrderOf x ∣ Nat.card G` together with `addOrderOf_nsmul_eq_zero`/`nsmul_eq_zero_of_dvd` to conclude `Nat.card G • x = 0` directly.
   - Why it might work: avoids the multiplicative round-trip entirely; Mathlib already has the additive order API.
   - Risk: confirming the exact additive lemma names (`addOrderOf_nsmul_eq_zero`, `nsmul_eq_zero_iff` analogues); none deep.

### Key Difficulties

- Locating the correct additive-order lemma names in current Mathlib (additive API sometimes lags the multiplicative one).
- `Nat.card` vs. `Fintype.card` bookkeeping (state both or relate via `Nat.card_eq_fintype_card`).
- Whether `AddCommGroup` is needed or `AddGroup` suffices (Lagrange does not require commutativity, though the headline targets abelian).

### What Would a Proof Need?

- Key lemma 1: `addOrderOf_dvd_natCard` (or `pow_card_eq_one` on `Multiplicative G`).
- Key lemma 2: `nsmul_eq_zero_of_dvd` / `addOrderOf` vanishing under divisibility.
- Technical requirements: `Nat.card_eq_fintype_card`, `Additive`/`Multiplicative` translation lemmas if using approach 1.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- The mathematics is the parent result restated additively; Mathlib supplies both the multiplicative source and the additive order API.
- This is primarily a transport/restatement exercise — the kind of clean corollary that ships quickly and 0-axiom.
- Strong precedent in sibling Lagrange/Euler gallery entries.

**Estimated Effort**:
- Exploration: 1 hour
- If tractable: a few hours to half a day

## References

### Papers
- Any standard algebra text (Dummit & Foote, Ch. 3) — corollaries of Lagrange's theorem; additive analogue of Fermat/Euler.

### Online Resources
- Standard statement that a finite abelian group of order $n$ is annihilated by $n$ (is a $\mathbb{Z}/n$-module).

### Mathlib
- `Mathlib.GroupTheory.OrderOfElement` — `pow_card_eq_one`, `orderOf_dvd_card`, `addOrderOf_dvd_natCard`.
- `Mathlib.Algebra.Group.TypeTags` — `Additive`/`Multiplicative` equivalences and `ofMul_pow` family.
- `Mathlib.Data.ZMod.Basic` — for the `ZMod n` specialization corollary.

## Metadata

```yaml
tags:
  - group-theory
  - finite-groups
  - order-of-element
  - lagrange-theorem
  - module-theory
related_proofs:
  - lagrange-theorem-oq-07
  - lagrange-theorem
difficulty: low
source: gallery-gap
created: 2026-06-23
```
