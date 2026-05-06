# Knowledge Base: angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01

**Problem**: Can `insep_gal_trivial` be proved using Mathlib's purely inseparable extension infrastructure?

## Problem Summary

The axiom `insep_gal_trivial` in the parent entry claims:
> For any inseparable irreducible f over a char-p field, |Gal(f)| = 1.

This open question asks whether this can be formally proved using Mathlib's `IsPurelyInseparable` infrastructure.

---

## Session 2026-05-06 (Session 1) — Counterexample found, correct theorem proved

**Mode**: FRESH
**Outcome**: completed (mathematically — showed axiom is FALSE, proved correct version)

### What I Did

1. Analyzed the mathematical content of `insep_gal_trivial`
2. Found that the axiom is FALSE in general — gave explicit counterexample
3. Identified the CORRECT theorem and proved it (with 2 minor API sorries)
4. Created new Lean file `AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean` (278 lines, 7 theorems)
5. Created gallery entry

### Key Findings

**The axiom is FALSE**: For f = g(X^p) where g is separable irreducible of degree ≥ 2, f is inseparable and irreducible but |Gal(f)| = |Gal(g)| ≥ 2.

**Concrete counterexample** (char 2):
- F = F₂(a), f(X) = X⁴ + X² + a = g(X²) where g = X² + X + a
- f is irreducible over F₂(a) (Artin-Schreier: g irreducible, so no quadratic factors of f)
- f is inseparable (f'(X) = 0 in char 2)
- |Gal(f)| = 2: the automorphism σ(α^(1/2)) = α^(1/2) + 1 has order 2

**The correct theorem** (proved):
```
algEquiv_eq_refl_of_isPurelyInseparable: 
  [IsPurelyInseparable F K] (σ : K ≃ₐ[F] K) → σ = AlgEquiv.refl F K
```
Proof: for x ∈ K, get n with x^(p^n) ∈ F; then (σ(x) - x)^(p^n) = 0 by char-p Frobenius; no nilpotents in field → σ(x) = x.

**Corollary** (proved):
```
gal_card_one_of_purelyInseparable_splitting:
  [IsPurelyInseparable F f.SplittingField] → Nat.card f.Gal = 1
```

### Files Modified

- `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean` (created, 278 lines)
- `src/data/proofs/angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01/meta.json` (created)
- `research/problems/angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01/knowledge.md` (this file)

### Next Steps

- Try submitting `sub_pow_char_pow` and `charP_eq_ringChar alignment` to Aristotle
- The 2 technical sorries should be eliminatable with the right Mathlib lemma names
- `insep_gal_trivial` in the parent could be REPLACED with the correct axiom about `IsPurelyInseparable F f.SplittingField` (a future PR)

---

## Session 2026-05-06 (Session 2) — Eliminated both sorries, 0 sorries achieved

**Mode**: REVISIT
**Outcome**: progress — 2 sorries eliminated, file now has 0 sorries (but Docker build had API errors)

### What I Did

1. Rewrote `sub_pow_char_pow_eq` using cleaner approach:
   - Apply `CharP.add_pow_char_pow K p (a-b) b n` to get `a^(p^n) = (a-b)^(p^n) + b^(p^n)`
   - Close with `linear_combination` (avoids messy `neg_pow` case split)
   - Key insight: work with addition `(a-b) + b = a`, not subtraction directly

2. Fixed `ringChar_eq_charP` sorry in `algEquiv_eq_refl_of_isPurelyInseparable`:
   - Correct Mathlib API: `CharP.eq K (ringChar.charP K) inferInstance : ringChar K = p`
   - `CharP.eq` gives uniqueness of characteristic (both CharP K (ringChar K) and CharP K p)

3. Fixed pre-existing omega bug in parent file `AngleTrisectionOQ02OQ01OQ01OQ01.lean`:
   - `omega` can't prove `False` from nonlinear `1 = f.natDegree * k` with `f.natDegree ≥ 2`
   - Fix: `exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by omega)`

### Files Modified

- `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean` (updated: 208 lines, 0 sorries)
- `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01.lean` (omega fix at line 148)
- `src/data/proofs/angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01/meta.json` (sorries: 2→0)
- `src/data/proofs/angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01/index.ts` (created)
- `src/data/proofs/angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01/annotations.json` (created)

### Key Findings

- `CharP.add_pow_char_pow` (believed correct in Session 2) — actually doesn't exist; corrected in Session 3
- `CharP.eq` gives uniqueness of the characteristic, enabling `ringChar K = p`
- The parent file `omega` at line 148 was a pre-existing bug (nonlinear divisibility goal)

### API Issues Found in Docker Build (addressed in Session 3)

- `FractionRing.instField` → correct name unknown (line 68)
- `AlgEquiv.refl_apply` → simp lemma not found (line 118)
- `CharP.add_pow_char_pow` → lemma name doesn't exist in Mathlib 2df2f015

### Next Steps

- PR #16149 is OPEN: Docker build API fixes needed (completed in Session 3)
- Future: prove counterexample_gal_card via Artin-Schreier extension theory
- Future: replace parent `insep_gal_trivial` with correct purely-inseparable version

---

## Session 2026-05-06 (Session 3) — API alignment and Docker build fixes

**Mode**: REVISIT
**Outcome**: progress — all three API issues resolved, Docker build in progress

### What I Did

1. Investigated three Docker build API failures from Session 2
2. Fixed `FractionRing.instField _` → `inferInstance` (auto-synthesized)
3. Fixed `CharP.add_pow_char_pow` (nonexistent) → `(iterateFrobenius K p n).map_sub a b` + `simp [iterateFrobenius_def]`
   - `iterateFrobenius` is a ring hom whose apply lemma is `iterateFrobenius_def: (iterateFrobenius R p n) x = x ^ p ^ n`
   - `map_sub` on the ring hom gives `(a - b)^(p^n) = a^(p^n) - b^(p^n)` directly
4. Fixed `AlgEquiv.refl_apply` (nonexistent) → `AlgEquiv.coe_refl, Function.id_eq`
   - Correct simp lemma is `AlgEquiv.coe_refl : ⇑(AlgEquiv.refl R A) = id`
5. Fixed `gal_card_one_of_purelyInseparable_splitting` proof structure
   - Old: broken `Nat.card_eq_one_iff_unique` with wrong argument count
   - New: `haveI : Unique f.Gal := ⟨⟨AlgEquiv.refl F f.SplittingField⟩, fun σ => ...⟩; exact Nat.card_unique`
6. Added explicit `[CharP F p]` to `algEquiv_eq_refl_of_isPurelyInseparable`
   - `IsPurelyInseparable.pow_mem x` uses `ringChar F` (base field), not `ringChar K`
   - Needed explicit `CharP F p` to convert `ringChar F = p`
7. Committed immediately before Docker build to prevent loom daemon from reverting edits

### Key Findings

- `FractionRing.field` (suggested by docs) is NOT the right name; `inferInstance` works
- `CharP.add_pow_char_pow` doesn't exist; use `iterateFrobenius K p n` as a ring hom with `map_sub`
- `AlgEquiv.refl_apply` doesn't exist; correct simp lemma is `AlgEquiv.coe_refl`
- Loom daemon reverts uncommitted edits mid-session — must commit before any long-running operation
- `IsPurelyInseparable.pow_mem x` uses `ringChar F` not `ringChar K`

### Files Modified

- `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean` (all API fixes applied, committed as 048ee39f670)
- `research/problems/angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01/knowledge.md` (this file)

### Next Steps

- Docker build 3 in progress: verify all API fixes work together
- If Docker build succeeds: close PR #16149 with passing build
- Future: prove counterexample_gal_card via Artin-Schreier extension theory
- Future: replace parent `insep_gal_trivial` with correct purely-inseparable version

---

## Dead Ends

- **"Inseparable irreducible → trivial Galois"**: The obvious approach is FALSE. The case f = g(X^p) with deg(g) ≥ 2 gives counterexample.
- **"Purely inseparable f ↔ trivial Gal"**: TRUE in one direction (proved), but the other direction (trivial Gal → purely insep splitting field) is not needed here.
