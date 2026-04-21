# Problem: Prove erdos_1941_divergence via Lebesgue Function Growth

**Slug**: erdos-1151-oq-04
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-extension

## Problem Statement

### Plain Language

The gallery proof `Erdos1151Problem.lean` formalizes Erdős problem #1151 using an axiom
`erdos_1941_divergence`. This open question asks:

**Can the axiom `erdos_1941_divergence` be proved in Lean 4 by formalizing the Lebesgue
function growth rate Λₙ(cos(πp/q)) → ∞ for rational cosine points with odd p, q?**

The Erdős (1941) result states that for any odd integers p, q with 1 < q, the Chebyshev
interpolation sequence at x = cos(πp/q) diverges to +∞.

### Formal Axiom to Prove

```lean
axiom erdos_1941_divergence (p q : ℕ) (hp : Odd p) (hq : Odd q) (hq1 : 1 < q)
    (x : ℝ) (hx : x = Real.cos (↑p * Real.pi / ↑q)) :
    Filter.Tendsto (fun n => chebyshevInterpSeq (fun _ => 0) x n)
      Filter.atTop Filter.atTop
```

### Why This Matters

- Eliminates an axiom from `Erdos1151Problem.lean`, moving from axiomatized to verified
- Connects classical approximation theory (Chebyshev nodes, Lebesgue function) to Lean 4
- Demonstrates how divergence growth rate estimates can be formalized in Mathlib
- The result (Erdős 1941) is a cornerstone of interpolation theory

## Known Results

### From Parent Proof (`Erdos1151Problem.lean`)

- `chebyshevNode_mem_Icc`: Chebyshev nodes lie in [-1, 1]
- `chebyshevNodes_injective`: nodes are distinct
- `limitPointSet_isClosed`: limit point sets are closed
- `chebyshevInterpSeq`: the interpolation sequence is defined
- `erdos_1941_divergence`: **this is the axiom we want to prove**

### Mathematical Facts

1. **Lebesgue function**: Λₙ(x) = Σₖ |ℓₖⁿ(x)| where ℓₖⁿ are the Lagrange basis polynomials
   at Chebyshev nodes
2. **Growth bound**: Λₙ(cos(πp/q)) ≥ C·log(n) for rational cosines with odd p, q
3. **Divergence**: Since Λₙ(x) → ∞, by the Banach-Steinhaus theorem (or direct construction
   of bump functions), the interpolation sequence diverges at x

### Key Identity

For Chebyshev nodes xₖ = cos((2k-1)π/(2n)), the Lebesgue function satisfies:

    Λₙ(cos(πp/q)) = (1/n) |Σₖ cot((2k-1-2pn/q)π/(2n))|

This trigonometric product grows logarithmically for rational arguments.

## Suggested Approach

### Phase 1: OBSERVE
1. Read `Erdos1151Problem.lean` fully — understand `chebyshevInterpSeq` definition
2. Check `Mathlib.Analysis.Polynomial.Chebyshev` for Chebyshev polynomial theory
3. Search for `Lebesgue function` or `lagrangeBasis` in Mathlib
4. Read Chebyshev node definitions: are they the standard (2k-1)π/(2n) nodes?

### Phase 2: ORIENT
1. Determine if Lebesgue function is defined or can be constructed from Mathlib pieces
2. Find trigonometric sum bounds: cotangent sum estimates
3. Assess: prove full Λₙ → ∞ or prove divergence more directly?

### Phase 3: DECIDE
1. If Lebesgue function approach: prove Λₙ ≥ C·log(n) then apply to get divergence
2. If direct: construct bump function f_n with |f_n| ≤ 1, |Iₙ(f_n, x)| → ∞
3. Fallback: state Λₙ growth as a sorry-lemma, prove the implication

### Phase 4: ACT

```lean
-- Key lemma to prove
lemma lebesgue_function_growth (p q : ℕ) (hp : Odd p) (hq : Odd q) (hq1 : 1 < q) :
    Filter.Tendsto (fun n => lebesgueFunction n (Real.cos (↑p * Real.pi / ↑q)))
      Filter.atTop Filter.atTop := by
  -- Use cotangent sum identity + partial fraction estimates
  sorry

-- Then derive erdos_1941_divergence from Lebesgue function growth
theorem erdos_1941_divergence_proof (p q : ℕ) (hp : Odd p) (hq : Odd q) (hq1 : 1 < q)
    (x : ℝ) (hx : x = Real.cos (↑p * Real.pi / ↑q)) :
    Filter.Tendsto (fun n => chebyshevInterpSeq (fun _ => 0) x n)
      Filter.atTop Filter.atTop := by
  -- chebyshevInterpSeq (fun _ => 0) = 0, so this is 0 → ∞?
  -- Wait: need to check if the zero function gives divergence
  -- Re-read the parent proof more carefully
  sorry
```

**Note**: Need to verify whether `chebyshevInterpSeq (fun _ => 0)` is identically zero
(in which case the statement seems contradictory) or represents something else.

## Related Gallery Proofs

- `erdos-1151`: Parent — Erdős problem #1151 (direct parent)
- `chebyshev-pnt-bridge`: Chebyshev polynomial theory in gallery
- `fourier-series`: Related: Fourier interpolation and divergence

## Quality Assessment

- **Tractability**: 4/10 — Lebesgue function bounds require careful analysis
- **Significance**: 7/10 — Eliminates axiom from gallery, important result
- **Domain**: Analysis / approximation theory
- **Risk**: High — cotangent sum estimates may need substantial Mathlib infrastructure
