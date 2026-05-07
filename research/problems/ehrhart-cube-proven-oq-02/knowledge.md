# Knowledge Base: ehrhart-cube-proven-oq-02

**Problem**: Can Ehrhart polynomials for polytopes with explicitly known
lattice-point formulas be proved from first principles, without invoking the
general Ehrhart existence theorem?

## Problem Summary

The d-dimensional cross-polytope `B_d = {x ∈ ℝᵈ : ‖x‖₁ ≤ 1}` has Ehrhart
polynomial `L(B_d, n) = ∑_{k=0}^d 2^k · C(d,k) · C(n,k)`. The gallery entry
`ehrhart-cube-proven-oq-02` proves the *algebraic* recursion
`L(B_{d+1},n) = L(B_d,n) + 2·∑_{m<n} L(B_d,m)` via Pascal + hockey-stick, and
several base/concrete cases. Two sorries remain:

1. `crossEhrhart_is_poly` — exhibit the polynomial of degree d in ℚ[X].
2. `crossBall_card` succ — the Finset slicing identifying the formula with
   actual lattice-point counts.

---

## Session 2026-05-07 (Session 1, researcher-8) — Approach mapping

**Mode**: ORIENT (RICH, score 19)
**Outcome**: Documented the descPochhammer-based path for `crossEhrhart_is_poly`.

### Mathlib Tools Identified

For `crossEhrhart_is_poly`:
- `descPochhammer R k : Polynomial R` — `X · (X-1) · ... · (X-k+1)`,
  defined in `Mathlib.RingTheory.Polynomial.Pochhammer`. natDegree exactly k.
- `descPochhammer_eval_eq_descFactorial` —
  `(descPochhammer R k).eval n = (n.descFactorial k : R)` for Nat n.
- `Nat.cast_choose_eq_descPochhammer_div` —
  `(n.choose k : K) = (descPochhammer K k).eval n / k.factorial` over a field.
- `Nat.descFactorial_eq_factorial_mul_choose` —
  `n.descFactorial k = k.factorial * n.choose k` (true for all k, not just k ≤ n).

### Proposed Polynomial

```
P d : Polynomial ℚ
  := ∑ k ∈ range (d+1), C ((2:ℚ)^k * C(d,k) / k!) * descPochhammer ℚ k
```

**Degree bound**: each summand has natDegree ≤ k (= descPochhammer ℚ k natDegree,
modulo C-mul); k ≤ d in the sum. So `P.natDegree ≤ d`.

**Eval correctness**:
```
P.eval n = ∑ k, (2^k · C(d,k) / k!) · (descPochhammer ℚ k).eval n
         = ∑ k, (2^k · C(d,k) / k!) · (n.descFactorial k : ℚ)
         = ∑ k, (2^k · C(d,k) / k!) · (k! · C(n,k) : ℚ)        -- descFactorial = k!·choose
         = ∑ k, 2^k · C(d,k) · C(n,k)                          -- k! cancels
         = (crossEhrhart d n : ℚ)
```

The k! cancellation works in ℚ because `(k.factorial : ℚ) ≠ 0`.

### Proposed Proof Sketch

```lean
theorem crossEhrhart_is_poly (d : ℕ) :
    ∃ (P : Polynomial ℚ), P.natDegree ≤ d ∧
    ∀ n : ℕ, P.eval (n : ℚ) = (crossEhrhart d n : ℚ) := by
  refine ⟨∑ k ∈ Finset.range (d + 1),
    Polynomial.C ((2 : ℚ) ^ k * (Nat.choose d k : ℚ) / (k.factorial : ℚ))
      * descPochhammer ℚ k, ?_, ?_⟩
  · -- natDegree ≤ d
    refine (Polynomial.natDegree_sum_le _ _).trans ?_
    -- reduce to: ∀ k ∈ range (d+1), natDegree (C _ * descPochhammer ℚ k) ≤ d
    sorry
  · intro n
    rw [Polynomial.eval_finset_sum, crossEhrhart, Nat.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C,
        descPochhammer_eval_eq_descFactorial,
        Nat.descFactorial_eq_factorial_mul_choose]
    have hk_ne : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    field_simp
    push_cast
    ring
```

### Risks / Open Items

- Lemma name `Nat.descFactorial_eq_factorial_mul_choose` — needs verification.
  Alternative: derive via `Nat.cast_choose_eq_descPochhammer_div` over ℚ, which
  rearranges to `(descPochhammer ℚ k).eval n = k.factorial * n.choose k`.
- `Polynomial.natDegree_sum_le` form: in Mathlib v4.26.0 may take a `Finset` and
  return a `Finset.sup` bound or use `≤ sup _ natDegree`. Need to spot-check.
- `Polynomial.natDegree_descPochhammer` or `descPochhammer_natDegree` — check
  exact name.

### For `crossBall_card` succ d

This is significantly harder — requires a Finset bijection / fiberwise count.
Sketch:
- `crossBall (d+1) n = Σ_{j ∈ Fin (2n+1)} fiber_j`, where
  `fiber_j = {x : Fin (d+1) → Fin (2n+1) | x ⟨d,...⟩ = j ∧ Σ_{i<d} |x i - n| ≤ n - |j-n|}`.
- The fiber is in bijection with `crossBall d (n - |j-n|)`.
- Pair j ↔ 2n−j: contributions of j and 2n−j are equal (symmetric).
- `card = crossBall d n + 2·∑_{m<n} crossBall d m = crossEhrhart d n + 2·∑_{m<n} crossEhrhart d m
        = crossEhrhart (d+1) n` by IH and `crossEhrhart_succ_d`.

Estimated 100+ lines; deferred for a future iteration.

---

## Dead Ends

- None yet.
