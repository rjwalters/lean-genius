# Three Squares Theorem - Knowledge Base

## Problem Statement

**Legendre's Three Squares Theorem (1797-1798)**: A natural number n can be expressed as the sum of three integer squares if and only if n is NOT of the form 4^a(8b + 7).

## Session 2026-01-01

### Literature Reviewed
- [Wikipedia: Legendre's three-square theorem](https://en.wikipedia.org/wiki/Legendre's_three-square_theorem)
- [Archive of Formal Proofs: Three Squares](https://www.isa-afp.org/entries/Three_Squares.html) - Isabelle formalization
- [Dirichlet's proof paper](https://pollack.uga.edu/finding3squares-6.pdf)
- Mathlib documentation for SumFourSquares, Dirichlet L-series

### Mathlib Infrastructure Assessment

| Component | Status | Notes |
|-----------|--------|-------|
| `Nat.sum_four_squares` | ✅ Available | Lagrange's four squares theorem |
| Modular arithmetic | ✅ Available | For necessity proof |
| Dirichlet L-series | ✅ Available | `Mathlib.NumberTheory.LSeries.Dirichlet` |
| Dirichlet characters | ✅ Available | `Mathlib.NumberTheory.DirichletCharacter` |
| Primes in AP (full) | ⚠️ Very recent | `PrimesInAP.lean` not in our Mathlib version |
| Ternary quadratic forms | ❌ Not available | Would need custom development |
| Class number formulas | ❌ Not available | Complex infrastructure |

### What We Built

**File**: `proofs/Proofs/ThreeSquares.lean`

**Status**: SURVEYED (compiles, uses axioms for hard directions)

**Proved**:
1. `IsExcludedForm` - Definition of excluded numbers
2. `nat_sq_mod_eight` - Squares mod 8 ∈ {0, 1, 4}
3. `legendre_three_squares` - Main theorem (with axioms)
4. `fourth_square_essential` - Connection to four squares
5. Examples verifying specific cases

**Axioms Used**:
1. `excluded_form_not_sum_three_sq` - Necessity direction
2. `not_excluded_form_is_sum_three_sq` - Sufficiency direction

### Why Axioms Were Needed

**Necessity (→)**: The proof is elementary but requires careful handling of:
- Integer modular arithmetic (tricky API in Mathlib for ℤ vs ℕ casts)
- The descent argument: if 4|n and n=a²+b²+c², then 2|a,b,c

The modular arithmetic is provable but hit API friction with `Int.sq_mod`, `Int.emod_mul_right`, etc.

**Sufficiency (←)**: Fundamentally hard. Known proofs require:
1. **Dirichlet's theorem approach**: Need primes ≡ 3 (mod 8) exist, plus ternary form theory
2. **Quadratic form approach**: Genus theory, class numbers

Mathlib recently added Dirichlet's theorem on primes in AP, but:
- Our Mathlib version (commit 05147a76b4) may not have `PrimesInAP.lean`
- Even with it, connecting to three squares requires additional development

### Insights Gained

1. **Two-vs-Three squares gap**: Two squares (Fermat) characterizes primes ≡ 1 (mod 4). Three squares excludes 4^a(8b+7). The proofs are fundamentally different in difficulty.

2. **Isabelle precedent**: The AFP entry explicitly depends on Dirichlet L-functions, confirming this isn't a simple proof.

3. **Wiedijk 100 candidate**: Four squares is #19; three squares would be a natural addition.

4. **Infrastructure path**: To fully prove this, one would need:
   - Upgrade Mathlib to include `PrimesInAP.lean`
   - Develop ternary quadratic form basics
   - Connect Dirichlet's theorem to representation theory

### Next Steps for Future Sessions

1. **Check if Mathlib update helps**: Newer Mathlib may have `PrimesInAP.lean`
2. ~~**Focus on necessity**: The elementary direction could be fully proved with more work on API~~ **DONE!**
3. **Alternative approach**: Look for simpler elementary proofs (unlikely to avoid deep results)

### Files Modified

- `proofs/Proofs/ThreeSquares.lean` (new)
- `research/candidate-pool.json` (status: in-progress → surveyed)
- `research/problems/three-squares-theorem/knowledge.md` (new)

---

## Session 2026-01-01 (Second Session) - NECESSITY PROVED!

### Major Achievement

**FULLY PROVED the necessity direction** - removed the `excluded_form_not_sum_three_sq` axiom!

### Proof Strategy

The proof uses strong induction on n with two cases:

**Base Case (k = 0)**: n = 8m + 7 ≡ 7 (mod 8)
- Key lemma: `int_sq_mod_eight` - Integer squares mod 8 are in {0, 1, 4}
- Key lemma: `sum_three_sq_mod_eight_ne_seven` - Sum of three from {0,1,4} never equals 7 mod 8
- Case analysis on all 27 combinations (3³ = 27 residue combinations)

**Inductive Case (k = k' + 1)**: n = 4^(k'+1) * (8m + 7)
- Since 4 | n and n = a² + b² + c², we have 4 | (a² + b² + c²)
- Key lemma: `four_dvd_sum_three_sq_implies_even` - If 4 | (a² + b² + c²), then 2 | a, 2 | b, 2 | c
- Descent: n/4 = (a/2)² + (b/2)² + (c/2)² and n/4 = 4^k' * (8m + 7)
- Apply IH to n/4 < n for contradiction

### New Lemmas Proved

1. `int_sq_mod_eight` - Integer squares mod 8 ∈ {0, 1, 4}
2. `check_sum_ne_7` - Helper for residue combination check
3. `sum_three_sq_mod_eight_ne_seven` - Main mod 8 impossibility
4. `seven_mod_eight_not_sum_three_sq_int` - Numbers ≡ 7 (mod 8) excluded
5. `int_sq_mod_four` - Integer squares mod 4 ∈ {0, 1}
6. `sq_mod_four_zero_implies_even` - Square ≡ 0 (mod 4) implies even
7. `four_dvd_sum_three_sq_implies_even` - Descent lemma
8. `div_four_excluded` - Division preserves excluded form structure
9. `excluded_form_not_sum_three_sq` - **THEOREM** (was axiom!)

### Technical Challenges Overcome

1. **ℤ vs ℕ coercions**: Required careful use of `Int.ofNat_ediv`, `Int.toNat`, and `omega`
2. **Modular arithmetic API**: Used `Int.mul_emod`, `Int.add_emod`, `Int.emod_emod_of_dvd`
3. **Strong induction setup**: `Nat.strong_induction_on` with proper decreasing argument
4. **Case splitting**: 27 combinations for mod 8, 8 combinations for mod 4

### Current Status

| Component | Status |
|-----------|--------|
| Necessity (→) | ✅ **FULLY PROVED** (0 axioms) |
| Sufficiency (←) | ❌ Axiom (requires Dirichlet/quadratic forms) |
| Main theorem | Uses 1 axiom (sufficiency only) |

### Statistics

- **Lines added**: ~120 lines of new proofs
- **Axioms removed**: 1 (necessity direction)
- **Axioms remaining**: 1 (sufficiency direction)

### Next Steps

1. **Sufficiency**: Would require:
   - Primes ≡ 3 (mod 8) existence (Dirichlet's theorem)
   - Ternary quadratic form representation theory
   - This is fundamentally harder and may require Mathlib updates

### Files Modified

- `proofs/Proofs/ThreeSquares.lean` (major update: +120 lines, -1 axiom)

---

## Session 2026-01-01 (Research Iteration) - SCOUTING

### Mode
REVISIT - Scouting for new knowledge that could enable sufficiency proof

### What We Found

**Major discovery**: Dirichlet's theorem on primes in arithmetic progressions is NOW in Mathlib!

- `Mathlib.NumberTheory.LSeries.PrimesInAP` - Complete formal proof
- `Nat.infinite_setOf_prime_and_eq_mod` - For q positive, a unit in ZMod q, infinitely many primes p with (p : ZMod q) = a
- `Nat.forall_exists_prime_gt_and_modEq` - Constructive version

We already have `proofs/Proofs/DirichletsTheorem.lean` wrapping this infrastructure!

### Infrastructure Assessment Update

| Component | Status | Notes |
|-----------|--------|-------|
| Dirichlet's theorem (primes in AP) | ✅ **AVAILABLE** | `Mathlib.NumberTheory.LSeries.PrimesInAP` |
| Sum of two squares | ✅ **AVAILABLE** | `Mathlib.NumberTheory.SumTwoSquares` |
| Fermat's two squares theorem | ✅ **AVAILABLE** | `Nat.Prime.sq_add_sq` |
| Quadratic forms (general) | ✅ **AVAILABLE** | `Mathlib.LinearAlgebra.QuadraticForm.*` |
| Sylvester's law of inertia | ✅ **AVAILABLE** | `equivalent_one_neg_one_weighted_sum_squared` |
| Ternary quadratic form theory | ❌ Not available | Specific representation lemmas needed |
| Genus theory / class numbers | ❌ Not available | Deep infrastructure |

### Proof Requirements for Sufficiency

Based on literature review ([Dirichlet's proof](https://pollack.uga.edu/finding3squares-6.pdf), [Warwick notes](https://warwick.ac.uk/fac/sci/maths/people/staff/michaud/thirdyearessay.pdf), [AFP formalization](https://www.isa-afp.org/entries/Three_Squares.html)):

**Dirichlet's 1850 Proof Strategy** (3 main lemmas):

1. **Lemma A**: For n ≡ 3 (mod 8), find prime p = Dn - 1 where D ≡ 2 (mod 4), p ≡ 3 (mod 8)
   - Uses Dirichlet's theorem on primes in AP ✅ AVAILABLE

2. **Lemma B**: Show -D is a quadratic residue mod p
   - Uses quadratic reciprocity (available in Mathlib)

3. **Lemma C (KEY)**: If n = p + 1 where p prime, -D QR mod p, then n = x² + y² + 2Dz²
   - This requires ternary quadratic form representation theory ❌ NOT AVAILABLE
   - The AFP formalization explicitly depends on L-function infrastructure

### BUILD vs BLOCK Assessment

**Size estimate for ternary form representation**: ~500-1000 lines
- Need to formalize representation by x² + y² + 2z²
- Need to connect Legendre symbols to representation
- Need case analysis for all residue classes mod 8

**Alternative approaches considered**:
1. **Geometry of Numbers (Ankeny 1957)**: Requires Minkowski's convex body theorem - partially in Mathlib but gaps
2. **Direct descent**: Works for four squares but not three
3. **Class number formula**: Even more infrastructure needed

**Decision**: BLOCKED (for now)

The gap is not Dirichlet's theorem (now available) but the ternary quadratic form representation theory. This requires ~500-1000 lines of specialized infrastructure connecting:
- Quadratic residues to representations
- Case analysis for each residue class mod 8
- Representation lemmas for x² + y² + Dz² forms

This is significant specialized work beyond what we can complete in a single session.

### What Changed Since Last Session

| Before | After |
|--------|-------|
| Dirichlet's theorem ⚠️ "very recent, may not be available" | ✅ Confirmed available, wrapped in DirichletsTheorem.lean |
| Need primes ≡ 3 (mod 8) | ✅ Can prove with `infinitely_many_primes_3_mod_4` pattern |
| Gap: ternary QF theory | ❌ Still the blocker |

### Outcome

**Scouted** - Found that Dirichlet's theorem is now available, but the remaining gap (ternary quadratic form representation) still requires ~500-1000 lines of custom development.

**Status remains**: `surveyed` - No code changes this session, knowledge updated.

### Next Steps (if returning)

1. **Build ternary QF basics**: Define representation by x² + y² + 2z², prove key lemma
2. **Consider alternative**: Look for more elementary proof avoiding full genus theory
3. **Check Mathlib updates**: Future Mathlib may add more QF infrastructure

### Sources

- [Mathlib: Primes in AP](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/PrimesInAP.html)
- [Mathlib: Sum Two Squares](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/SumTwoSquares.html)
- [Mathlib: Quadratic Forms](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/QuadraticForm/Real.html)
- [AFP: Three Squares](https://www.isa-afp.org/entries/Three_Squares.html)
- [Dirichlet's Algorithmic Proof](https://pollack.uga.edu/finding3squares-6.pdf)

---

## Session 2026-01-01 (Revisit 2) - VERIFICATION

### Mode
REVISIT - Verifying previous session's claims about Mathlib infrastructure

### Verification Results

**CORRECTION**: Previous session's claim about PrimesInAP availability was INCORRECT.

Build test of `DirichletsTheorem.lean`:
```
error: bad import 'Mathlib.NumberTheory.LSeries.PrimesInAP'
error: bad import 'Mathlib.NumberTheory.LSeries.DirichletContinuation'
error: bad import 'Mathlib.NumberTheory.LSeries.Nonvanishing'
```

**Actual Mathlib status**:
- Our project uses Mathlib commit `05147a76b4` (September 8, 2024)
- `PrimesInAP.lean` was added to Mathlib on November 22, 2024 (commit `fe0e8bcc2ddc`)
- DirichletsTheorem.lean was written speculatively but does NOT compile

### Updated Infrastructure Assessment

| Component | Status | Notes |
|-----------|--------|-------|
| Dirichlet's theorem (primes in AP) | ❌ **NOT AVAILABLE** | Our Mathlib (Sept 2024) predates PrimesInAP (Nov 2024) |
| Sum of two squares | ✅ Available | `Mathlib.NumberTheory.SumTwoSquares` |
| Ternary quadratic form theory | ❌ Not available | ~500-1000 lines to build |

### Implication

Even upgrading Mathlib to get PrimesInAP would still leave us ~500-1000 lines short of the ternary quadratic form infrastructure needed for sufficiency.

**Total infrastructure gap**:
- Mathlib upgrade + ~500-1000 lines ternary QF theory

**Decision**: Remains `surveyed`. Would need both:
1. Mathlib version bump (non-trivial, may break other proofs)
2. ~500-1000 lines of ternary QF development

### Outcome

**Scouted** - Corrected inaccurate claim from previous session. Dirichlet's theorem is NOT in our Mathlib version. The gap is larger than previously documented.
