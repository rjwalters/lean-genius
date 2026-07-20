# Erdős Problem #748: The Cameron-Erdős Conjecture on Sum-Free Sets

**Lean file**: `proofs/Proofs/Erdos748Problem.lean`
**Sorries**: 0 (all base cases f(1),f(2),f(3),… discharged by kernel `decide`)
**Status**: axiomatized — at achievable ceiling (2 deep axioms remain)
**Tier**: A | **Significance**: 8/10 | **Tractability**: 5/10

> **State (2026-07-19, researcher-1):** The file is host-verified clean on
> v4.31.0 (0 sorries, exactly 2 axioms). The three base cases below were long
> since proved by `decide`; the "sorries" section is retained only as historical
> context. The entire LOWER-bound side is unconditional and axiom-free
> (`sharp_lower_bound`, odd-family and two-family constructions, the log-asymptotic
> lower conjunct, strict monotonicity, non-uniqueness of extremal sets). The two
> remaining axioms carry only the UPPER bound and are genuinely deep literature
> results (both >1000 lines to formalize) — see the Adversarial checklist below.

## Problem Statement

Let f(n) count sum-free subsets A ⊆ {1,...,n}. Conjecture: f(n) = 2^{(1+o(1))n/2}.

**Status**: PROVED — Green (2004) and Sapozhenko (2003).

## The Sorries

### Easy: Base Cases (Sorries 2-4)
```lean
theorem f_1 : f 1 = 2 := by sorry   -- f(1) = |{{}, {1}}| = 2
theorem f_2 : f 2 = 3 := by sorry   -- f(2) = |{{}, {1}, {2}}| = 3
theorem f_3 : f 3 = 6 := by sorry   -- f(3) = |{{},{1},{2},{3},{1,3},{2,3}}| = 6
```
These are computable! Count sum-free subsets of {1,2,3} directly.

### Hard: Main Theorem (Sorry 1)
```lean
theorem cameron_erdos : ∀ ε > 0, ∀ᶠ n in atTop,
    |Real.log (f n) - (n/2 * Real.log 2)| ≤ ε * n := by
  sorry -- Full proof requires careful asymptotic analysis
```

## Approach: Start with Base Cases

For `f_1 : f 1 = 2`:
- Sum-free subsets of {1}: {} and {1} (trivially sum-free since no triple a,b,c)
- Try `decide` if `f` is computable, or explicit enumeration

For `f_2 : f 2 = 3`:
- Subsets: {}, {1}, {2}, {1,2}. Is {1,2} sum-free? 1+1=2 ∈ {1,2} → NO. So 3 sum-free subsets.

For `f_3 : f 3 = 6`:
- Need to enumerate all 8 subsets and check sum-free condition

## Key Questions

1. Is `f` computable in the Lean file? If yes, try `native_decide` or `decide`
2. What is the definition of sum-free in this file?
3. Are there auxiliary lemmas already proved?

## Related Gallery Proof

- `src/data/proofs/erdos-748/` — Erdős Problem #748
- `proofs/Proofs/Erdos748Problem.lean` — file with sorries

## First Steps (OBSERVE phase)

1. Read `Erdos748Problem.lean` fully
2. Check if `f` is `Decidable` / computable
3. Try `decide` or `native_decide` on the base cases first
4. For main theorem: read Green's proof structure in the file comments

## Must prove exactly / does not count

The pinned target is the Cameron–Erdős asymptotic for the COUNT of sum-free sets:
`f(n) = 2^{(1+o(1))·n/2}`, i.e. `log₂ f(n) = (1 + o(1))·n/2`, where
`f n := (Finset.Icc 1 n).powerset.filter IsSumFree |>.card`.

- **Does not count:** the *largest* sum-free subset having size `⌈n/2⌉`. That is a
  different (structural, not counting) statement — owned by open PR #30202. Proving
  it does NOT establish the count asymptotic.
- **Does not count:** the lower bound alone. `log₂ f(n) ≥ n/2` (via `sharp_lower_bound`
  / `cameronErdos_lower_unconditional`) is unconditional and already fully proved; the
  conjecture's content is the matching UPPER bound `f(n) ≤ 2^{(1/2+o(1))n}` (Green 2004).
- **Does not count:** any bound of the form `f(n) ≤ 2^{cn}` with `c > 1/2`. The trivial
  `f(n) ≤ 2^n` and cruder sieve bounds do not reach the `1/2` exponent.
- **Does not count:** parity-blind constants. `precise_asymptotic` requires the
  parity-dependent constant `c_n` (Green/Sapozhenko); a single `c` is a near-miss.

## Adversarial checklist

How a "solved" claim here could be wrong — check each before upgrading status:

1. **Axiom smuggling.** Confirm `green_upper_bound` / `precise_asymptotic` are still
   `axiom` declarations, not silently invoked as hypotheses of a theorem presented as
   axiom-free. `#print axioms` on any UPPER-bound theorem must list them.
2. **Lower-for-upper substitution.** Confirm no theorem claims the upper bound while its
   proof only re-derives a lower bound (the two-family / odd-family lemmas are all lower
   bounds; none may masquerade as the upper conjunct).
3. **Statement mismatch on `f`.** Confirm `f` counts sum-free subsets of `Icc 1 n`
   (range `{1,…,n}`), not `{0,…,n}` or `Finset.range`; the base-case values
   `f 1 = 2, f 2 = 3, f 3 = 6` pin this — a shifted range breaks them.
4. **⌈n/2⌉ vs ⌊n/2⌋ off-by-one.** The sharp lower exponent is `⌈n/2⌉ = (n+1)/2`; a claim
   using `⌊n/2⌋` is the weaker (superseded) `trivial_lower_bound`, not the sharp result.
5. **Largest-set ≠ count.** Confirm the claim is about `f(n)` (a count), not about the
   size of the largest sum-free subset (PR #30202's target).
6. **Constant in `precise_asymptotic`.** If someone discharges `precise_asymptotic`,
   confirm the constant is genuinely parity-dependent (`c_n`), not a single averaged `c`.
