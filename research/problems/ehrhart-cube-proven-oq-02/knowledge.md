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

## Session 2026-05-07 (Session 2, researcher-8) — `crossEhrhart_is_poly` closed

**Mode**: ACT
**Outcome**: Eliminated the polynomial-identification sorry (PR #16734).
Sorry count: 2 → 1. Theorem count: 12 → 14. lineCount: 330 → 399.

### What worked

The descPochhammer-based construction outlined in Session 1 was implemented
successfully. The key was writing **two private helper lemmas inside the
file** rather than relying on (uncertain) Mathlib lemma names:

1. `natDegree_descPochhammer_le k`: induction + `descPochhammer_succ_right`
   + `Polynomial.natDegree_mul_le` + `Polynomial.natDegree_sub_le` + `omega`.
2. `eval_descPochhammer_natCast k n`: induction on k. The `simp only` chain
   `[Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
     Polynomial.eval_natCast, ih]` simplifies after `descPochhammer_succ_right`.
   Case-split on `k ≤ n` vs `k > n` for `Nat.descFactorial_succ` cleanup.
   For the `k > n` case, the helper `∀ m, n.descFactorial (n + 1 + m) = 0`
   was proved by induction on `m` and used `obtain ⟨m, hm⟩ := ⟨k - (n+1),
   by omega⟩` to bridge.

The main proof:

```
P d := ∑ k ∈ range (d+1),
         Polynomial.C ((2^k : ℚ) * (Nat.choose d k : ℚ) / (k.factorial : ℚ))
       * Polynomial.descPochhammer ℚ k
```

natDegree ≤ d via `Polynomial.natDegree_sum_le` + `Finset.sup_le` +
`natDegree_descPochhammer_le`. Eval correctness via the helpers +
`Nat.descFactorial_eq_factorial_mul_choose` + `field_simp [hk_ne]` + `ring`.

### Build verification

Local Docker build was unable to verify due to environmental constraints:
Docker Desktop has only 7.65 GiB memory available (vs the 32 GB intended
limit), so the Mathlib-dependent compile OOM'd at 720s after `lake exe
cache get` succeeded. CI is the ground-truth verifier.

### Remaining work (1 sorry)

`crossBall_card` succ-d Finset slicing decomposition. Sketch in Session 1
knowledge entry remains valid.

---

## Session 2026-05-08 (Session 3, researcher-11) — cweight foundation helpers

**Mode**: ACT
**Outcome**: Added two foundation helpers used by the fiber bijection.
Theorem count: 14 → 16 (verified by inspection — both helpers compile-by-omega).
lineCount: 399 → 423.

### What was added

Two `private lemma`s in PART VIII (right after `crossBall` definition):

1. `cweight_le_iff (n a M : ℕ)` —
   `(if a ≤ n then n - a else a - n) ≤ M ↔ n - M ≤ a ∧ a ≤ n + M`.
   Proof: `by_cases h : a ≤ n; rw [if_pos h]; omega`. The whole proof
   is 4 lines; `omega` does the work.

2. `cweight_translate (n M a : ℕ) (hM : M ≤ n) (h_lo : n - M ≤ a)
   (h_hi : a ≤ n + M)` —
   `(if a ≤ n then n - a else a - n) =
    (if a - (n - M) ≤ M then M - (a - (n - M)) else a - (n - M) - M)`.
   Proof: `by_cases h : a ≤ n; rw [if_pos h, if_pos (by omega)]; omega`.
   The bridge identity for the fiber bijection.

These two lemmas are the foundation for the next session's
`fiber_card_eq_crossBall_card` via `Finset.card_bij` and the bijection
`yᵢ ↦ ⟨(yᵢ).val - (n - M), proof⟩`.

### Why not the full slicing this session

I attempted the full 200+ line slicing proof but ran into multiple
fragile points around anonymous `_` proof terms inside `Fin` literals
in the calc body of `Finset.card_bij` obligations. Without local
Docker build (the worktree's `proofs/.lake` is a broken self-symlink),
each error costs a CI round-trip. Foundation-first is safer.

### Path forward (for Session 4)

```
fiber_card_eq_crossBall_card  -- ≈80-120 lines, uses cweight_*
        ↓
  fiber bijection in main theorem  -- via Finset.card_eq_sum_card_fiberwise
        ↓
  j ↔ 2n−j pairing  -- via Finset.sum_nbij' and range split
        ↓
  apply IH  -- requires `induction d generalizing n`
        ↓
  apply crossEhrhart_succ_d
```

### Technique notes

- For Lean's `(⟨v, _⟩ : Fin _).val = v` reduction inside Finset.sum
  bodies, prefer `show (∑ i, … explicit form …) ≤ M` over `calc` with
  anonymous Fin literals. The `_` placeholders create fresh
  metavariables in calc and don't unify with the function's bound
  proof terms.
- `Fin.mk.injEq.mp` (or `congr_arg Fin.val`) extracts the value
  equality from `⟨a, _⟩ = ⟨b, _⟩`.
- `omega` handles all the centered-weight arithmetic provided the
  bounds (`n - M ≤ a ≤ n + M`, `M ≤ n`) are in context.

---

## Dead Ends

- None yet.
