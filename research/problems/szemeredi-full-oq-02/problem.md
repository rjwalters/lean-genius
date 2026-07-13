# Problem: Szemerédi's Theorem — Uniform Sets Not Containing k-AP Are o(N) Dense

**Slug**: szemeredi-full-oq-02
**Created**: 2026-04-23T05:52:30+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall k \geq 1,\; \forall \varepsilon > 0,\; \exists N_0 : \forall N \geq N_0,\;
\text{if } A \subseteq \{1, \ldots, N\} \text{ is } k\text{-AP-free, then } |A| \leq \varepsilon N
$$

Equivalently: any $k$-AP-free subset of $\{1, \ldots, N\}$ has density $o(N)$ (vanishing density).

In Lean 4 (target sketch):
```lean
theorem szemeredi_density (k : ℕ) (hk : 1 ≤ k) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
    (∀ a ∈ A, a ≤ N) →
    IsAPFree (A : Set ℕ) k →
    (A.card : ℝ) / N ≤ ε := by
  sorry
```

### Plain Language

Szemerédi's theorem says: any set of integers with positive upper density contains
arbitrarily long arithmetic progressions. This formulation asks the contrapositive:
if a set A ⊆ {1,...,N} has NO k-term arithmetic progression, then |A|/N → 0.

In other words, k-AP-free sets are *sparse* — they can't occupy a positive fraction of
any long initial segment of the integers.

### Why This Matters

This is the *quantitative* density statement of Szemerédi's theorem. The gallery proof
`szemeredi-full` handles the *existence* direction (positive density ⟹ k-APs exist)
with k≥4 axiomatized. This problem asks for the *density bound* formulation, which:

1. Completes the logical picture for the gallery's Szemerédi orbit
2. Connects to Gowers uniformity norms and quantitative bounds
3. Links the combinatorial and ergodic-theoretic perspectives
4. Is needed to make the `szemeredi-full-oq-01` Furstenberg approach computable

## Known Results

### What's Already Proven

- **k=3 (Roth's theorem)**: `rothNumberNat` is in Mathlib; the `szemeredi-full` gallery
  proof uses it via `Mathlib.Combinatorics.Additive.Corner.Roth`
- **Szemerédi Regularity Lemma**: In Mathlib via `Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma`
- **Triangle/Corners theorem**: In Mathlib, used to prove Roth's theorem
- **k=1,2**: Trivial (any set is 1-AP-free only if empty; 2-AP-free impossible for |A|≥2)
- **The full theorem**: Proved by Szemerédi (1975), Furstenberg ergodic (1977), Gowers (2001)

### What's Still Open in Lean

- **k≥4 quantitative density bound**: Requires hypergraph regularity, NOT in Mathlib
- The k≥4 case in `szemeredi-full` is axiomatized as `szemeredi_large_k`
- Quantitative Gowers-norm approach not yet formalized

### Our Goal

Formalize the density statement for at least **k=3** (Roth) and see how far we can
push towards **k=4** or general k. The k=3 case is tractable via Mathlib's existing
Roth machinery. The general k case needs to either:
1. Extract from the axiom in `szemeredi-full`, or
2. Formalize partial density bounds that don't require full hypergraph regularity

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `szemeredi-full` | Core Szemerédi formalization; k≥4 axiomatized | Case analysis, Roth k=3 |
| `szemeredi-regularity` | Regularity lemma (key tool for density bounds) | Graph regularity |
| `szemeredi-counting` | Hypergraph counting lemma | Hypergraph regularity |
| `szemeredi-theorem` | Alternative statement in the gallery | AP definition |

## Initial Thoughts

### Potential Approaches

1. **Roth-first (Tractable)**: Focus on k=3 density bound from Mathlib's `rothNumberNat`.
   - Mathlib provides `rothNumberNat n` = max size of 3-AP-free subset of {0,...,n-1}
   - The density bound is: `rothNumberNat n / n → 0` as `n → ∞`
   - This should be extractable from Mathlib's Salem-Spencer API
   - Why it might work: Mathlib already has the theorem, just needs wrapping
   - Risk: API mismatch between our `IsAPFree` and Mathlib's `ThreeAPFree`/`AddSalemSpencer`

2. **Axiom-derivation**: Derive density from `szemeredi-full`'s existing axiom.
   - The `szemeredi-full` proof has `axiom szemeredi_large_k : ...`
   - Could state density as a corollary of the existence theorem
   - Why it might work: Logical equivalence is straightforward
   - Risk: The axiom gives existence, not quantitative bounds

3. **Furstenberg ergodic (Moonshot)**: Connect to `szemeredi-full-oq-01`'s approach
   - Would require substantial ergodic theory infrastructure
   - Why it might work: Furstenberg's proof is measure-theoretic, potentially more formalization-friendly
   - Risk: Very high — ergodic theory not well-developed in Lean 4

### Key Difficulties

- **API surface mismatch**: Our `IsAPFree` vs Mathlib's `AddSalemSpencer`/`ThreeAPFree`
- **Quantitative vs. qualitative**: Mathlib may only have existence, not density bounds
- **Density formulation**: Need ε-N formulation or filter/tendsto for the o(N) statement
- **k≥4 gap**: No hypergraph regularity in Mathlib blocks general case

### What Would a Proof Need?

- Equivalence lemma: `IsAPFree S k ↔` Mathlib's k-AP-free predicate
- For k=3: `∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, rothNumberNat N ≤ ε * N`
- For k≥4: Either extract from axiom or accept as axiomatized

## Tractability Assessment

**Difficulty**: High (k=3 sub-problem: Medium; general k: Moonshot)

**Justification**:
- The k=3 density bound is likely available from Mathlib's `rothNumberNat` asymptotics
- The general k case requires hypergraph regularity — not in Mathlib, very hard
- A meaningful contribution: prove the o(N) statement for k=3, state k≥4 as axiom
- Similar problems solved: `szemeredi-full` (existence), Roth k=3 in Mathlib

**Estimated Effort**:
- Exploration (OBSERVE/ORIENT): 1-2 iterations to understand API
- k=3 tractable path: 3-5 iterations if Mathlib API cooperates
- General k: Likely needs to remain axiomatized

## References

### Papers
- Szemerédi, "On sets of integers containing no k elements in AP" (1975)
- Furstenberg, "Ergodic behavior of diagonal measures" (1977)
- Gowers, "A new proof of Szemerédi's theorem" (2001)
- Dillies & Mehta, "Formalising Szemerédi's Regularity Lemma in Lean 4" (ITP 2022)

### Mathlib
- `Mathlib.Combinatorics.Additive.AP.Three.Defs` — 3-AP definitions
- `Mathlib.Combinatorics.Additive.Corner.Roth` — Roth's theorem (k=3)
- `Mathlib.Combinatorics.Additive.SalemSpencer` — Salem-Spencer (AP-free sets)
- `Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma` — Regularity lemma
- `Mathlib.Topology.Algebra.Order.LiminfLimsup` — Asymptotic bounds if needed

## Metadata

```yaml
tags:
  - combinatorics
  - arithmetic-progressions
  - szemeredi
  - density
  - regularity
related_proofs:
  - szemeredi-full
  - szemeredi-regularity
  - szemeredi-counting
difficulty: high
source: gallery-gap
created: 2026-04-23T05:52:30+02:00
```

**Significance**: 8/10
**Tractability**: 3/10
