# Knowledge: erdos-476-oq-05

## Key Facts

### Parent Results (erdos-476 / Cauchy-Davenport)
- `erdos-476` proves: for prime $p$ and $A, B \subseteq \mathbb{Z}/p\mathbb{Z}$ nonempty, $|A+B| \geq \min(p, |A|+|B|-1)$
- This is the **Cauchy-Davenport theorem** (1813/1935). (verified, 0 sorries)

### The Equality Case: Vosper's Theorem (1956)
- **Statement**: If $|A+B| = |A|+|B|-1$ and $|A|, |B| \geq 2$ and $|A|+|B|-1 \leq p-1$, then:
  - $A$ and $B$ are both arithmetic progressions with the **same common difference** $d$
  - i.e., $A = \{a, a+d, \ldots, a+(|A|-1)d\}$ and $B = \{b, b+d, \ldots, b+(|B|-1)d\}$ in $\mathbb{Z}/p\mathbb{Z}$
- Edge cases:
  - $|A| = 1$ or $|B| = 1$: equality holds trivially (no structure constraint)
  - $|A|+|B|-1 = p$: $A+B = \mathbb{Z}/p\mathbb{Z}$, trivially satisfied

### Arithmetic Progressions in Z/pZ
- AP: set of the form $\{a + id \mid 0 \leq i < k\}$ for $d \neq 0$ in $\mathbb{Z}/p\mathbb{Z}$
- Since $p$ is prime, any $d \neq 0$ generates all of $\mathbb{Z}/p\mathbb{Z}$

### Proof Strategy (Vosper 1956)
1. Induction on $|A|$
2. Base case $|A|=2$: $A = \{a, a+d\}$ for some $d$; equality in CD forces $B = \{b, b+d, \ldots\}$ (same $d$)
3. Inductive step: Remove element, apply CD on smaller set, deduce AP structure propagates

## Open Questions
- How does `erdos-476` prove Cauchy-Davenport? Polynomial method or compression?
- Is there existing Mathlib infrastructure for APs in `ZMod`?
- What's the Lean name for AP in `ZMod p`? (`Finset.image` of linear function?)

## References
- Vosper, A.G. (1956): "The fraction of subsets of integers summing to a given value"
- Nathanson, M.B. *Additive Number Theory: Inverse Problems*, §2.4
- Parent proof: `proofs/Proofs/Erdos476.lean`
- `Mathlib.Data.ZMod.Basic` — ZMod infrastructure
- `Mathlib.Combinatorics.Additive` — additive combinatorics in Mathlib
