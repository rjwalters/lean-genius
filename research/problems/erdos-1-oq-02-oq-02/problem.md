# Problem: DFX Lower Bound: Fix dfx_lower_bound Base Cases

**Slug**: erdos-1-oq-02-oq-02
**Created**: 2026-04-23T11:58:33+02:00
**Status**: COMPLETED — resolved 2026-04-26 by PR [#12782](https://github.com/rjwalters/lean-genius/pull/12782); the `dfx_lower_bound` sorry was eliminated by tightening the theorem's preconditions (`hN : 2 ≤ N`, `hA_pos : ∀ a ∈ A, 0 < a`) rather than by computational base-case checks. See `knowledge.md` for the full resolution narrative.
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{For } n = 1, 2: \quad N(n) \geq \left\lfloor \sqrt{\frac{2}{\pi}} \cdot \frac{2^n}{\sqrt{n}} \right\rfloor
$$

where $N(n)$ is the maximum size of a set $A \subseteq \{1, \ldots, M\}$ with distinct subset
sums (Erdős #1 problem). Specifically, fix the sorry in the Lean theorem `dfx_lower_bound`
by providing the base cases $n = 1$ and $n = 2$ computationally.

### Plain Language

The Dubroff-Fox-Xu (DFX) lower bound framework (from Erdős #1 gallery entry `erdos-1-oq-02`)
proves a lower bound $N(n) \geq \sqrt{2/\pi} \cdot 2^n / \sqrt{n}$ for large $n$. The Lean
proof has a `sorry` in `dfx_lower_bound` that handles the **base cases** $n = 1, 2$.

For small $n$, the bound must be verified directly (the inductive argument doesn't kick in
until $n$ is sufficiently large). For $n=1$: any singleton $\{a\}$ has distinct subset sums
trivially, so $N(1) \geq 1$; for $n=2$: $N(2) \geq 1$ or $N(2) \geq 2$ depending on the
exact constant. The fix requires a `by norm_num` or `by native_decide` computation.

### Why This Matters

Completing this sorry makes the DFX lower bound proof fully formal without any `axiom` or
open `sorry`. It contributes to the completeness of the Erdős #1 formalization, one of the
flagship entries in the gallery. It's also a good example of sorry repair: the mathematical
content is known, only the Lean formalization of the base check is missing.

## Known Results

### What's Already Proven

- The DFX lower bound for large $n$ (inductive step) is formalized in `erdos-1-oq-02`
- The `anticoncentration_bound` axiom is separate (this sorry is specifically about base cases)
- For $n=1, 2$, the bound values are computable and small enough for `norm_num` or `decide`

### What's Still Open

- The base case check for $n = 1$ in `dfx_lower_bound`
- The base case check for $n = 2$ in `dfx_lower_bound`

### Our Goal

Replace the `sorry` in `dfx_lower_bound` with a `by norm_num` or `by native_decide` proof
for the base cases, or a direct computation showing $N(n) \geq \text{bound}(n)$ for $n = 1, 2$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-1-oq-02` | Parent proof containing the sorry | DFX framework, anticoncentration |
| `erdos-1` | Root Erdős #1 formalization | Distinct subset sums, 2^n bound |

## Initial Thoughts

### Potential Approaches

1. **Computational check**: Use `native_decide` or `norm_num` to verify the inequality for
   $n = 1, 2$ numerically.
   - Why it might work: The values are small and concrete (e.g., $N(1) = 1$, bound ≈ 0.8).
   - Risk: The bound uses `Real.sqrt` and `pi`, which may not reduce in `norm_num` without work.

2. **Direct construction**: For $n=1$ and $n=2$, explicitly construct a DSS set of the required
   size and verify it satisfies the distinct-subset-sums property by `decide`.
   - Why it might work: Small cases are fully enumerable.
   - Risk: Need to match the exact Lean definition of `dfx_lower_bound`.

3. **Manual arithmetic**: Compute the RHS bound for $n=1,2$ manually, note it's $< 2$,
   observe $N(1) \geq 1$ trivially, and use `norm_num` to close.
   - Why it might work: The bound for small $n$ is not tight; any singleton works.
   - Risk: The formal statement may require matching the exact definition type.

### Key Difficulties

- The `dfx_lower_bound` lemma's exact Lean statement may have hypotheses that complicate
  the base case: need to read `Proofs/ErdosOQ02.lean` (or similar) carefully.
- `Real.sqrt` and `Real.pi` are real-number terms that don't always reduce computationally.

### What Would a Proof Need?

- Read the actual Lean file for `erdos-1-oq-02` to find `dfx_lower_bound`'s exact signature
- Check whether `norm_num` can handle `⌊√(2/π) · 2^n / √n⌋` for $n=1,2$
- Possibly: `Nat.cast_le`, `Real.sqrt_le_sqrt`, bounds on `Real.pi`

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- This is a sorry repair for a finite base case check
- The mathematics is not in question — only the Lean formalization of two numerical checks
- `native_decide` or `norm_num` extensions should handle this

**Estimated Effort**:
- Exploration: 1 hour (find and read the sorry'd lemma)
- If tractable: 1-4 hours (write the base case proof)
- If hard: 1-3 days (if real-number arithmetic in Lean is stubborn)

## References

### Papers
- Dubroff, Fox, Xu — "Subset Sums and the Erdős-Moser Conjecture" (2021)

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Sqrt` — `Real.sqrt` API
- `Mathlib.Tactic.NormNum` — numerical verification
- `Mathlib.Data.Real.Pi.Bounds` — bounds on `Real.pi`

## Metadata

```yaml
tags:
  - number-theory
  - combinatorics
  - sorry-repair
  - erdos
related_proofs:
  - erdos-1-oq-02
  - erdos-1
difficulty: low
source: gallery-gap
created: 2026-04-23T11:58:33+02:00
```
