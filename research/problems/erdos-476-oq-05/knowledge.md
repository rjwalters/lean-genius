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

### Proof Strategy (Vosper 1956) — Currently Implemented
1. Induction on $|A|$
2. **Base case** $|A|=2$: Proved via `vosper_base` (0 sorries)
   - $A = \{a, b\}$, $d = b-a$; equality in CD forces $|B \cap (B + d)| = |B|-1$
   - Hence $|B \setminus (B+d)| = 1$, so `ap_of_near_periodic` gives $B$ is AP with diff $d$
3. **Key lemma** `ap_of_near_periodic` (0 sorries): Proved via orbit-cardinality contradiction
   - If $|B \setminus B.\text{image}(\cdot + d)| = 1$ and $d \neq 0$ and $|B| < p$, then $B$ is AP with diff $d$
   - Proof: Strong induction. If $b_0 + kd \in B$ but $b_0 + (k+1)d \notin B$, then $B \setminus \{b_0, \ldots, b_0+kd\}$
     is closed under $b \mapsto b-d$. Any $x_0$ in this set generates $\{x_0 - nd : 0 \leq n < p\}$
     (orbit of size $p$, injective map from $\text{Fin}(p)$). But this subset of $B$ has size $p > |B|$. Contradiction.
4. **Full theorem** `vosper` (2 sorries): Structured recursive proof
   - Uses `termination_by A.card` for well-founded recursion
   - **SORRY 1**: Case 1 existence — find $a_0 \in A$ with $|(A \setminus \{a_0\}) + B| = |A|+|B|-2$
   - **SORRY 2**: AP extension — given $A' = A \setminus \{a_0\}$ and $B$ are APs with diff $d$, show $a_0$
     is adjacent (predecessor/successor) to $A'$ → $A$ is AP with diff $d$

## Open Questions (for future sessions)
- Prove SORRY 1: Case 1 existence
  - Approach: Counting argument. If ALL $a \in A$ satisfy $|(A\setminus\{a\})+B| = |A+B|$ (Case 2),
    then for each $x \in A+B$, $|A \cap (x-B)| \geq 2$ (every element has $\geq 2$ representations).
    Summing: $|A| \cdot |B| \geq 2(|A|+|B|-1)$, i.e., $(|A|-2)(|B|-2) \geq 2$.
    For $|A|=3, |B| \leq 3$: $1 \cdot (|B|-2) < 2$. Contradiction for $|B| \in \{2,3\}$.
    For $|A|,|B| \geq 4$: Needs additional argument (iterative removal).
- Prove SORRY 2: AP extension
  - Approach: Show $A'+B$ is AP with diff $d$ (from `IsAP` of $A'$ and $B$ + CD equality).
    Then $\{a_0\}+B$ and $A'+B$ are APs with same diff; $|\{a_0\}+B \setminus A'+B| = 1$ forces
    missing element to be endpoint of $\{a_0\}+B$, i.e., $a_0$ is adjacent to $A'$. QED.

## References
- Vosper, A.G. (1956): "The fraction of subsets of integers summing to a given value"
- Nathanson, M.B. *Additive Number Theory: Inverse Problems*, §2.4
- Parent proof: `proofs/Proofs/Erdos476.lean`
- `Mathlib.Combinatorics.Additive.CauchyDavenport` — `ZMod.cauchy_davenport`
- `Mathlib.Data.ZMod.Basic` — ZMod infrastructure

## Session History

## Session 2026-04-22 (Session 3) — Structured recursive proof for vosper

**Mode**: REVISIT (rebased onto main, continued from previous sessions)
**Outcome**: Progress — 1 opaque sorry split into 2 specific sorries with clear mathematical proofs

### What I Did
- Rebased `feature/researcher-7` onto `main` to get the improved file from PR #11197
- Replaced the single opaque `sorry` in `theorem vosper` with a structured recursive proof:
  - Uses `termination_by A.card` for well-founded recursion
  - Base case (`|A|=2`): calls `vosper_base` directly
  - Inductive step: finds non-redundant a₀, applies IH recursively, extends AP
  - Sorry 1: Case 1 existence (counting argument)
  - Sorry 2: AP extension (endpoint argument)
- Docker build verified the file compiles with the new structure

### Key Findings
- The recursive `theorem` with `termination_by` pattern works cleanly in Lean 4
- The extension argument is mathematically clear: both A'+B and {a₀}+B are APs with diff d;
  |(a₀+B) \ (A'+B)| = 1 forces the missing element to be an endpoint, placing a₀ adjacent to A'
- The Case 1 existence argument is the harder sorry: works for small |A|,|B| via counting;
  needs additional work for large sets

### Files Modified
- `proofs/Proofs/Erdos476OQ05Problem.lean`: Replaced opaque sorry with structured proof

### Next Steps
1. Prove SORRY 1 (Case 1 existence) for all |A|,|B|
2. Prove SORRY 2 (AP extension) — should be tractable given infrastructure in place
3. Both sorries are good Aristotle candidates once well-formalized
