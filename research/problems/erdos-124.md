# Erdos Problem #124: Complete Sequences of Integer Powers

**Research Status**: Complete
**Epic**: #334
**Implementation Issue**: #336
**Date**: 2026-01-09

---

## Executive Summary

Erdos Problem #124 was the first open mathematical conjecture solved autonomously by an AI system. In November 2025, Harmonic's Aristotle AI solved and formally verified the problem in 6 hours with no human assistance. The Lean proof is publicly available and compatible with Lean Genius's toolchain.

**Key Finding**: The proof requires Lean 4.24.0 / Mathlib v4.24.0. Lean Genius uses 4.26.0 - full compatibility expected.

---

## Proof Source

### Repository
- **URL**: https://github.com/plby/lean-proofs
- **File**: `src/v4.24.0/ErdosProblems/Erdos124b.lean`
- **Requirements**: Lean 4.24.0, Mathlib v4.24.0
- **Live Verification**: https://live.lean-lang.org/

### Alternative Sources
- **Google DeepMind Formal Conjectures**: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/124.lean (statement only, contains known typo)
- **erdosproblems.com**: https://www.erdosproblems.com/124

### Compatibility Assessment

| Component | Proof Requires | Lean Genius Has | Status |
|-----------|---------------|-----------------|--------|
| Lean | v4.24.0 | v4.26.0 | Compatible (newer) |
| Mathlib | v4.24.0 | v4.26.0 | Compatible (newer) |

**Conclusion**: The proof should work with minimal or no adaptation.

---

## The Mathematics

### Original Paper

**Title**: "Complete sequences of sets of integer powers"
**Authors**: S. A. Burr, P. Erdos, R. L. Graham, W. Wen-Ching Li
**Journal**: Acta Arithmetica 77.2 (1996): 133-138
**DOI**: 10.4064/aa-77-2-133-138

### Problem Statement

For integers $d \geq 1$ and $k \geq 0$, let $P(d,k)$ denote the set of integers expressible as sums of distinct powers $d^i$ where $i \geq k$ (i.e., numbers with only digits 0,1 in base $d$, starting from the $k$-th position).

Given integers $3 \leq d_1 < d_2 < \cdots < d_r$ satisfying:
$$\sum_{1 \leq i \leq r} \frac{1}{d_i-1} \geq 1$$

**Question (Weak Version - SOLVED)**: Can all sufficiently large integers be expressed as $\sum_i c_i a_i$ where $c_i \in \{0,1\}$ and $a_i \in P(d_i, 0)$?

**Question (Strong Version - OPEN)**: If additionally $\gcd(d_1, \ldots, d_r) = 1$, can all sufficiently large integers be expressed as $\sum_i c_i a_i$ where $c_i \in \{0,1\}$ and $a_i \in P(d_i, k)$ for any $k \geq 1$?

### The Two Versions

| Aspect | Weak Version | Strong Version |
|--------|--------------|----------------|
| Power range | $P(d,0)$ - includes $d^0 = 1$ | $P(d,1)$ - excludes 1 |
| GCD condition | Not required | $\gcd(d_1,...,d_r) = 1$ |
| Status | **SOLVED** by Aristotle | **OPEN** |
| Difficulty | Elementary greedy proof | Requires advanced techniques |

### Why the Distinction Matters

Including $d^0 = 1$ fundamentally changes the problem:
- **With 1 allowed**: Elementary greedy/completeness arguments succeed
- **Without 1**: Powers can create gaps approaching $d_i$, requiring "something like Baker's theorem" (Terence Tao) to prevent dangerous clustering

The formalization process revealed this ambiguity - Erdos's 1997 reformulations may have accidentally created the easier version.

---

## Proof Structure

### Key Components

**Main Theorems**:
- `erdos_124`: Strengthened statement removing unnecessary assumptions
- `formal_conjectures_erdos_124`: Version matching DeepMind's statement
- `formal_conjectures_erdos_124_corrected`: Fixes inequality typo (= vs >=)

**Central Lemmas**:
- `browns_criterion`: Sequences with small gaps have universal subset sum representability
- `u_seq_monotone`: The constructed sequence is non-decreasing
- `u_seq_gap`: Verifies gap conditions required by Brown's criterion
- `digits_of_subset_sum_u_seq`: Decomposes subset sums into binary-digit representations

**Algorithmic Construction**:
- `e_seq`: Exponent sequence tracking which base receives increments
- `u_seq`: Main sequence where each term equals a power of the minimized base
- `chosen_index`, `chosen_exponent`: Extract the base and power at each step

### Proof Strategy

The proof employs an algorithmic greedy approach:
1. Merge power sequences from all bases into one sorted sequence
2. At each step, select the base with smallest current power and increment its exponent
3. Apply Brown's criterion: verify $a_{n+1} - 1 \leq a_1 + \cdots + a_n$
4. The reciprocal sum condition $\sum 1/(d_i-1) \geq 1$ ensures gaps stay small enough

This is described as an "olympiad-style proof" - elegant but elementary once the key insight (using Brown's criterion) is identified.

---

## The AI Story

### Timeline

| Date | Event |
|------|-------|
| 1996 | Burr, Erdos, Graham, Li publish original paper |
| 1997 | Erdos reformulates problem (introduces ambiguity) |
| Nov 2025 | Boris Alexeev selects problems for Aristotle beta test |
| Nov 2025 | Aristotle solves Problem #124 in 6 hours |
| Nov 2025 | Lean verification completes in 1 minute |
| Nov 28, 2025 | Public announcement |
| Dec 2025 | Discussion of "weak vs strong" distinction |

### Key People

- **Boris Alexeev**: Research mathematician who ran Aristotle on selected problems
- **Terence Tao**: Provided analysis distinguishing weak/strong versions
- **Thomas Bloom**: Maintains erdosproblems.com, acknowledged achievement with caveats
- **Vlad Tenev**: Harmonic founder, announced "Vibe proving is here"

### The Discovery Story

Boris Alexeev selected several Erdos problems, launched Aristotle's beta version with enhanced reasoning, and went to sleep. He reported being "not emotionally prepared to wake up to an email that Aristotle had successfully resolved Problem 124."

The proof was generated with **100% autonomy** - no human participation or assistance throughout the solving process.

### What Makes This Historic

1. **First autonomous AI solution** to an open mathematical conjecture
2. **Formal verification** provides machine-checkable guarantee of correctness
3. **Revealed problem ambiguity** - 30 years of humans missed that formalization would expose two interpretations
4. **Speed**: 6 hours solving + 1 minute verification vs decades of human attempts

### Critical Perspective

Terence Tao's assessment: "Aristotle solved 'a' version of this problem (indeed, with an olympiad-style proof), but not 'the' version."

The strong version (what Burr et al. originally intended) remains open. However:
- The AI correctly solved the problem as literally stated
- The formalization exposed ambiguity humans hadn't noticed
- This itself demonstrates the value of formal methods

---

## Annotation Strategy

### Recommended Sections

**Section 1: Historical Context** (~15 annotations)
- The 1996 paper and its authors (Erdos, Graham, etc.)
- What "complete sequences" means intuitively
- Why this problem resisted solution for 30 years
- The 1997 reformulation that introduced ambiguity

**Section 2: Problem Statement** (~10 annotations)
- Definition of $P(d,k)$ with examples
- The reciprocal sum condition and why it's necessary
- The two interpretations (weak vs strong)
- Why formal verification revealed the ambiguity

**Section 3: Proof Walkthrough** (~25 annotations)
- Brown's criterion as the key insight
- The greedy construction algorithm
- Key lemmas with intuitive explanations
- How the reciprocal condition ensures small gaps

**Section 4: The AI Story** (~10 annotations)
- Harmonic's Aristotle system
- The 6-hour autonomous solution
- What "formally verified" means in practice
- Implications for mathematics and AI collaboration

### Key Educational Points

1. **Brown's Criterion**: The theorem that sequences with bounded gaps have all large integers as subset sums
2. **Greedy Construction**: Why selecting the smallest power at each step works
3. **The Reciprocal Condition**: Intuition for why $\sum 1/(d_i-1) \geq 1$ is necessary and sufficient
4. **Formalization Value**: How precise statement exposed 30-year-old ambiguity

---

## Implementation Checklist

### Lean Proof File
- [ ] Download `Erdos124b.lean` from plby/lean-proofs
- [ ] Adapt imports for Lean Genius structure
- [ ] Test compilation with `lake build`
- [ ] Verify no sorries remain

### Frontend Data
- [ ] Create `src/data/proofs/erdos-124-complete-sequences/`
- [ ] Write `meta.json` with Erdos-specific fields
- [ ] Write `annotations.json` following section strategy above
- [ ] Create `index.ts` import file
- [ ] Register in proof modules and listings

### Special Considerations
- Include `erdosNumber: 124` in metadata
- Add `solvedBy: "Harmonic Aristotle"` attribution
- Link to erdosproblems.com
- Consider "AI-Solved" badge variant

---

## References

### Primary Sources
- [Original Paper (PDF)](https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=59a181547d8dba31bb51ff444bc3e1996fb67865) - Burr, Erdos, Graham, Li (1996)
- [Lean Proof Repository](https://github.com/plby/lean-proofs) - plby/lean-proofs
- [erdosproblems.com/124](https://www.erdosproblems.com/124) - Official problem page
- [Discussion Thread](https://www.erdosproblems.com/forum/thread/124) - Community discussion

### Context Sources
- [Xena Project Blog](https://xenaproject.wordpress.com/2025/12/05/formalization-of-erdos-problems/) - Formalization of Erdos Problems
- [Harmonic News](https://harmonic.fun/news) - Official announcements
- [Google DeepMind Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) - Statement repository

### Media Coverage
- [Mindplex Article](https://magazine.mindplex.ai/post/harmonics-ai-aristotle-claims-solution-to-historic-math-puzzle)
- [Office Chai Article](https://officechai.com/ai/robinhood-ceo-vlad-tenevs-math-ai-startup-claims-to-have-solved-an-erdos-problem-that-was-open-for-30-years/)
- [Hacker News Discussion](https://news.ycombinator.com/item?id=46094037)
