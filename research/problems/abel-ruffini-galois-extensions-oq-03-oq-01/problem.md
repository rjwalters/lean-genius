# Problem: Every Nontrivial Normal Subgroup of Aₙ (n ≥ 5) Contains a 3-Cycle

**Slug**: abel-ruffini-galois-extensions-oq-03-oq-01
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion (open question `abel-ruffini-galois-extensions-oq-03`)

## Problem Statement

### Formal Statement

$$
\forall\, \alpha \text{ a finite type with } 5 \le |\alpha|,\quad
\forall\, N \trianglelefteq \mathrm{Alt}(\alpha),\ N \ne \{1\}
\;\Longrightarrow\; \exists\, \sigma \in N,\ \sigma \text{ is a 3-cycle.}
$$

Consequently, via Mathlib's
`isSimpleGroup_of_forall_normal_contains_threeCycle`, one obtains
`IsSimpleGroup (alternatingGroup α)` for every `α` with `5 ≤ Fintype.card α`.

### Plain Language

The alternating group Aₙ (even permutations of n letters) is simple for every
n ≥ 5 — it has no normal subgroups other than the trivial one and the whole
group. Mathlib already reduces this fact to a single combinatorial lemma: any
normal subgroup that contains more than the identity must contain a 3-cycle
(and since the 3-cycles generate Aₙ and are all conjugate in Aₙ for n ≥ 5, that
forces the subgroup to be everything). The goal here is to supply that lemma for
general n, removing the current file's reliance on the black-box
`alternatingGroup.isSimpleGroup_five` (the n = 5 special case).

### Why This Matters

Simplicity of Aₙ for n ≥ 5 is the group-theoretic heart of the Abel–Ruffini
theorem: because Aₙ (hence Sₙ) is not solvable for n ≥ 5, the general polynomial
of degree ≥ 5 is not solvable by radicals. The parent gallery entry proves
Abel–Ruffini using only the n = 5 instance; generalizing simplicity to all
n ≥ 5 makes the unsolvability argument uniform in the degree and provides a
reusable Mathlib-style lemma about the alternating group.

## Known Results

### What's Already Proven

- `isSimpleGroup_of_forall_normal_contains_threeCycle` (Mathlib) — reduces
  simplicity of `alternatingGroup α` to: every nontrivial normal subgroup
  contains a 3-cycle.
- `alternatingGroup.isSimpleGroup_five` (Mathlib) — the n = 5 base case, used as
  a black box by the parent entry `abel-ruffini-galois-extensions-oq-03`.
- 3-cycles generate `alternatingGroup α` and are a single conjugacy class in
  `Alt(α)` once `5 ≤ |α|` (standard; available in Mathlib's `AlternatingGroup`
  development to varying degrees).

### What's Still Open

- The uniform-in-n proof of the 3-cycle containment lemma is not yet present in
  the gallery; the parent entry only invokes the n = 5 result.
- Whether the cleanest formalization proceeds by the classical commutator
  cycle-type case analysis or by an induction/stabilizer reduction.

### Our Goal

Prove the containment lemma "every nontrivial normal subgroup N of Alt(α)
contains a 3-cycle" for `5 ≤ card α`, then package
`IsSimpleGroup (alternatingGroup α)` for all n ≥ 5 and use it to discharge the
black box in the parent Abel–Ruffini file.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| abel-ruffini-galois-extensions-oq-03 | Direct parent; currently uses the n=5 black box | Galois solvability, Aₙ simplicity |
| abel-ruffini-galois-extensions | Abel–Ruffini via solvability of the Galois group | Solvable groups, radical towers |
| abel-ruffini-oq-06 | Contrasting small-n structure: A₄ is NOT simple | Composition series A₄ ▷ V₄ ▷ 1 |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Classical cycle-type case analysis.** Take a non-identity
   element sigma of N; by considering the cycle type of sigma and forming a
   commutator with a well-chosen 3-cycle tau, manufacture a nontrivial element
   of N of smaller/bounded support, and iterate down to a 3-cycle.
   - Why it might work: it is the standard textbook proof and every step is
     elementary permutation algebra that `Equiv.Perm` and `decide` can support
     on bounded support.
   - Risk: the case split on cycle type is fiddly to formalize cleanly; keeping
     the "manufacture a shorter element" bookkeeping Lean-friendly is the crux.

2. **Approach B — Reduction/induction on n via point stabilizers.** Use that a
   normal subgroup meeting the stabilizer of a point non-trivially descends to
   Aₙ₋₁, plus a transitivity/base-case argument, to reduce to n = 5.
   - Why it might work: turns the problem into a clean induction anchored at the
     Mathlib n = 5 result.
   - Risk: requires careful handling of the primitivity/transitivity of the
     Aₙ-action and the descent to `Alt(Fin (n-1))`.

### Key Difficulties

- Formalizing "manufacture a 3-cycle from a commutator with a well-chosen
  3-cycle" without an unwieldy explicit case analysis.
- Bridging between abstract `alternatingGroup α` statements and concrete
  `Equiv.Perm (Fin n)` computations for the small-support base cases.

### What Would a Proof Need?

- Key lemma 1: from any non-identity element of N, a nontrivial element of N of
  strictly smaller support (or of bounded support) via commutators with
  3-cycles.
- Key lemma 2: 3-cycles are conjugate in `Alt(α)` for `5 ≤ |α|`, so one 3-cycle
  in N forces all of them (hence N is the whole group).
- Technical requirements: Mathlib's `Equiv.Perm.IsThreeCycle`, cycle-type API,
  `alternatingGroup`, and `isSimpleGroup_of_forall_normal_contains_threeCycle`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematics is classical and completely standard (undergraduate algebra).
- Mathlib already provides the reduction lemma and the n = 5 base case, so the
  scope is one well-identified combinatorial lemma rather than the whole theorem.
- Related permutation-group case analyses have been formalized in the gallery
  (A₄/V₄ composition series), showing the tooling is adequate.

**Estimated Effort**:
- Exploration: 1–2 days (survey Mathlib's alternating-group API, choose approach)
- If tractable: 1–2 weeks
- If hard: unknown (if the cycle-type case analysis resists clean formalization)

## References

### Papers
- E. Galois, foundational work on solvability by radicals (historical context).

### Online Resources
- Standard algebra texts (Dummit & Foote, chapter on the alternating group) —
  the 3-cycle containment argument for simplicity of Aₙ.

### Mathlib
- `Mathlib.GroupTheory.SpecificGroups.Alternating` — `alternatingGroup`,
  `isSimpleGroup_of_forall_normal_contains_threeCycle`,
  `alternatingGroup.isSimpleGroup_five`.
- `Mathlib.GroupTheory.Perm.Cycle.Type` — cycle-type API, `IsThreeCycle`.

## Metadata

```yaml
tags:
  - algebra
  - group-theory
  - alternating-group
  - simple-groups
  - galois-theory
related_proofs:
  - abel-ruffini-galois-extensions-oq-03
  - abel-ruffini-galois-extensions
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```
