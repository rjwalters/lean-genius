# Knowledge: erdos-1151-oq-04

## Key Facts

### The Lebesgue Function
- Λₙ(x) = Σₖ |ℓₖⁿ(x)| where ℓₖⁿ are Lagrange basis polynomials at Chebyshev nodes
- Measures worst-case amplification of interpolation errors
- For Chebyshev nodes: Λₙ(x) ≈ (2/π)·log(n) + O(1) for most x ∈ [-1, 1]
- For rational cosine arguments: Λₙ(cos(πp/q)) grows at least logarithmically

### The Erdős (1941) Result
- For odd p, q with q > 1: Chebyshev interpolation of the zero function diverges at cos(πp/q)?
- Wait: need to re-read — Erdős result likely concerns a specific non-zero function
- The axiom `erdos_1941_divergence` takes `fun _ => 0` — this seems suspicious
- **Key question**: Does the axiom statement make mathematical sense as written?

### Chebyshev Nodes
- Standard: xₖⁿ = cos((2k-1)π/(2n)) for k = 1, ..., n
- Lie in (-1, 1)
- `chebyshevNode_mem_Icc` in parent: nodes lie in [-1, 1]

### Mathlib Resources (to verify)
- `Mathlib.Analysis.Polynomial.Chebyshev`: Chebyshev polynomials T_n
- Lagrange interpolation: likely not formalized for arbitrary nodes
- Trigonometric sums: `Mathlib.Analysis.SpecialFunctions.Trigonometric`

## Open Questions
- Is `chebyshevInterpSeq (fun _ => 0) x n` always 0? If so, how can it → +∞?
- What is the actual Lean definition of `chebyshevInterpSeq`?
- Does Mathlib have Lagrange interpolation at Chebyshev nodes?

## References
- Erdős, P. (1941): "On the convergence of trigonometric series"
- Natanson, I.P.: "Constructive Function Theory" Vol. III
- Parent proof: `proofs/Proofs/Erdos1151Problem.lean`
