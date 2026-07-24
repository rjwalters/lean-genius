# Problem: Complete the Lean Formalization of Erdős Problem #18 (Practical Numbers and h(n!))

**Slug**: erdos-18-wip-01
**Created**: 2026-07-09T17:33:19-07:00
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
m \text{ practical} \iff \forall k,\ 1 \leq k < m \implies \exists S \subseteq \mathrm{divisors}(m),\ \sum_{d \in S} d = k, \qquad \text{Conjecture: } h(n!) < n^{o(1)}.
$$

Here $h(m)$ is the minimum number of divisors of $m$ needed so that every $k < m$ is a sum of distinct chosen divisors, and the $\$250$ conjecture asks whether $h(n!)$ grows subpolynomially in $n$.

### Plain Language

The completion task is to strengthen the work-in-progress Lean 4 formalization of Erdős Problem #18 on practical numbers. A positive integer $m$ is *practical* if every smaller positive integer can be written as a sum of distinct divisors of $m$; the first examples are $1, 2, 4, 6, 8, 12, 16, 18, \ldots$ (OEIS A005153). Erdős asked how few divisors are actually needed: writing $h(m)$ for that minimum, is $h(n!)$ subpolynomial in $n$, i.e. $h(n!) < n^{o(1)}$? This carries a $\$250$ prize and remains open. The current Lean file defines practicality, the representation predicate, the function $h(m)$, and the main conjectures, and verifies that $1$ and $2$ are practical; the Stewart–Sierpiński characterization, the density results, and the Erdős and Vose bounds appear only in comments. Our goal is to formalize the provable supporting facts and keep the open conjecture cleanly stated but not overclaimed.

### Why This Matters

1. **A live Erdős prize problem**: The subpolynomial-$h(n!)$ question is unsolved and carries a $\$250$ Erdős prize, so an honest, well-structured formalization documents a genuine research frontier.
2. **Divisor-completeness theory**: Practical numbers satisfy proven analogues of Goldbach's conjecture (Melfi 1996) and admit infinitely many "practical twins," making them a rich, tractable model for additive questions about divisors.
3. **Reusable characterization**: Formalizing the Stewart–Sierpiński prime-factorization test for practicality would give Mathlib a decidable criterion useful well beyond this single entry.

## Known Results

### What's Already Proven

- Stewart–Sierpiński characterization — $m = 2^{a_0} p_1^{a_1} \cdots p_k^{a_k}$ is practical iff each $p_i \leq 1 + \sigma(2^{a_0} p_1^{a_1} \cdots p_{i-1}^{a_{i-1}})$ (Stewart 1954, Sierpiński 1955); documented in the Lean file only.
- Practical Goldbach — every even $n \geq 2$ is a sum of two practical numbers (Melfi, 1996).
- Density and counting — practical numbers have a positive-proportion counting function of order $x/\log x$ (Hausman–Shapiro 1984, Weingartner 2015).

### What's Still Open

- Whether $h(n!) < n^{o(1)}$ (main conjecture, $\$250$ prize), and the stronger $h(n!) < (\log n)^{O(1)}$.
- Whether there are infinitely many $m$ with $h(m) < (\log\log m)^{O(1)}$.

### Our Goal

Complete the WIP Lean file `Proofs/Erdos18Problem.lean`: extend the verified base cases ($1$ and $2$ practical) to further concrete facts that Mathlib can discharge — e.g. that $3$ and $5$ are *not* practical, that powers of two are practical via binary representation, and small `decide`-checked membership of the OEIS list — and, where feasible, formalize one direction of the Stewart–Sierpiński criterion as a stated theorem. The main $h(n!)$ conjectures must remain `Prop`s (open, prize-bearing) and any deep bound (Erdős's $h(n!) < n$, Vose's $\sqrt{\log m}$ result) that is asserted must be explicitly axiomatized and disclosed, never presented as verified.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-18 | Parent gallery entry (badge wip): defines `IsPractical`, `IsRepresentable`, `h`, `PracticalNumbers`, and the three main conjectures, with `one_practical`/`two_practical` proved and the rest in comments. | Divisor subset sums, `Finset.powerset`, `omega`/`interval_cases`, sigma function |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Discharge finite membership and non-membership facts by decision procedures.
   - Why it might work: For fixed small $m$, "$m$ is practical" is a finite check over subsets of `divisors m`, so `decide` (or `Finset` enumeration) settles $3, 5$ non-practical and $4, 6, 8$ practical.
   - Risk: naive `decide` over powersets can blow up combinatorially; may need a smarter representation predicate.

2. **Approach B**: Formalize the easy direction of Stewart–Sierpiński (practical implies the $\sigma$-inequality) and the powers-of-two lemma.
   - Why it might work: The binary-representation argument for $2^n$ is constructive and the $\sigma$-monotonicity direction follows from divisor-sum bounds already in Mathlib.
   - Risk: the full biconditional and the closure-under-multiplication step require an inductive divisor-sum argument that may be lengthy.

### Key Difficulties

- The powerset-based `IsRepresentable` predicate makes brute-force decisions expensive; efficient reformulation matters.
- The $h(n!)$ conjecture depends on the fine multiplicative structure of factorials and cannot be resolved within scope.

### What Would a Proof Need?

- Key lemma 1: powers of two are practical, via the greedy/binary divisor construction.
- Key lemma 2: the Stewart–Sierpiński $\sigma$-inequality characterization (at least one direction).
- Technical requirements: `Nat.divisors`, `Nat.sigma`, `Finset.sum`, and a tractable decidable form of the subset-sum representation predicate.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Concrete practicality/non-practicality checks and the powers-of-two lemma are clearly tractable and would raise the verified content of the entry.
- The headline $h(n!)$ conjecture is an open, prize-bearing problem and is out of scope to resolve.
- Mathlib supplies divisors, the sigma function, and finite-set summation, which cover the tractable lemmas but not the analytic bounds on $h$.

**Estimated Effort**:
- Exploration: 1-2 days
- If tractable: 1-2 weeks for the concrete lemmas and one direction of Stewart–Sierpiński
- If hard: unknown for any nontrivial bound on $h(n!)$

## References

### Papers
- A. K. Srinivasan, "Practical numbers", Current Science 17 (1948), 179–180 — original definition.
- P. Erdős, "On practical numbers", in Number Theory (Budapest 1987), Colloq. Math. Soc. János Bolyai 51, 453–459 — growth of $h(n!)$.
- M. Hausman and H. N. Shapiro, "On practical numbers", Comm. Pure Appl. Math. 37 (1984), 801–812 — asymptotic density.

### Online Resources
- https://erdosproblems.com/18 — canonical statement, open status, and $\$250$ prize.
- https://oeis.org/A005153 — the sequence of practical numbers.

### Mathlib
- `Mathlib.Data.Nat.Divisors` — `Nat.divisors` and divisor-sum lemmas underpinning practicality.
- `Mathlib.NumberTheory.Divisors` — the `sigma` function used in the Stewart–Sierpiński criterion.

## Adversarial Checklist (t = 9 record-setter claim, 2026-07-24)

For the claim `minimal_hErdos_nine : IsLeast {m | IsPractical m ∧ hErdos m = 9} 348`
(and its corollaries `record_setter_nine_lt_two_pow`, `not_hErdos_le_log_two`):

- **Wrong-h near-miss**: the claim must be about `hErdos m = (Finset.range m).sup (repLength m)`
  (max over targets `k < m` of the minimum representation size), NOT the universal-set
  `h` of the parent file. Confirm the theorem statement uses `hErdos`, and that
  `repLength` is a true minimum (`repLength_spec` + `repLength_le_of_witness`).
- **Lower-bound scope**: `IsLeast` needs `hErdos m ≠ 9` for EVERY practical `m < 348`,
  not just `m ∈ [256, 348)`. Confirm `hErdos_le_eight_of_lt_threefortyeight` chains
  through `hErdos_le_seven_of_lt_twofiftysix` for `m < 256` (which itself chains all
  prior thresholds down to `m = 1`), and that `interval_cases` covers all of `[256, 348)`
  with every non-practical value excluded by kernel `decide`, not skipped.
- **Exactness at 348**: `hErdos 348 = 9` needs both directions. Upper: sub-family
  engine on 10 of the 11 proper divisors (`116` droppable since `116 = 29 + 87`).
  Lower: `le_hErdos_of_card` at the single hard target `k = 347` quantifies over the
  FULL powerset of `divisors 348` (2¹² subsets, kernel `decide`) — confirm no restricted
  sub-family is used on the lower side (a restricted lower search would be unsound).
- **sInf/sup degeneracy**: `hErdos` is a `Finset.sup` over `range m`, so it is total
  (no `sInf ∅ = 0` trap); but for NON-practical `m` some `repLength m k` values sit on
  an empty attainment set — confirm the `IsLeast` membership component carries
  `IsPractical 348` explicitly and the lower-bound component only ever evaluates
  `hErdos` under an `IsPractical` hypothesis.
- **Kernel trust**: all decides are kernel `decide` (with `maxRecDepth`/`maxHeartbeats`
  bumps), never `native_decide` — `#print axioms minimal_hErdos_nine` must show only
  `propext`/`Classical.choice`/`Quot.sound`, no `Lean.ofReduceBool`.
- **Circularity**: no axiom or hypothesis as strong as the claim — the file is 0-axiom;
  confirm `grep -c "^axiom "` is 0 and no structure-encoded assumptions exist.
- **Scope honesty**: this settles a session-internal record-setter question only; the
  prize conjecture `h(n!) < n^{o(1)}` is untouched and must remain open.

## Metadata

```yaml
tags:
  - erdos
  - number-theory
  - practical-numbers
  - divisor-sums
  - subset-sums
  - open-problem
related_proofs:
  - erdos-18
difficulty: high
source: proof-suggestion
created: 2026-07-09T17:33:19-07:00
```

**Significance**: 7/10
**Tractability**: 5/10
