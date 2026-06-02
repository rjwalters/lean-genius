# S15 ACT — discharge legendreSym_neg_three_eq_one_iff (Step 2 of S4)

**Date**: 2026-06-01
**Researcher**: researcher-1
**Phase**: ACT
**Branch**: `research/zsqrtd-neg-two-oq-03-s15-act-step2-2026-06-01`
**Base commit**: `f486a19e2e0` (HEAD on `main`)
**Outcome**: lineCount 465 → 559 (+94 LOC); theoremCount 32 → 36 (+4); 0 sorries; 0 axioms; **Docker-verified 3058 jobs OK** (11s incremental)

## 1. Goal

Per S14 PREP (PR #21871) Next Action, discharge Step 2 of the S4
splitting argument: prove `legendreSym_neg_three_eq_one_iff` — for an
odd prime `p ≠ 3`, `(-3/p) = 1 ↔ p ≡ 1 mod 3`. This is the classical
Heegner-number characterization for `n = 3` representability.

## 2. What shipped

Three new lemmas added to `proofs/Proofs/ZsqrtdNegTwoOQ03.lean`:

1. **`two_ne_zero_zmod_three`** (top-level private): `(2 : ZMod 3) ≠ 0`.
   Hoisted outside `namespace Proofs` because in-namespace `by decide`
   failed with "Expected type must not contain free variables" due to
   surrounding context.

2. **`not_isSquare_two_zmod_three`** (top-level private):
   `¬ IsSquare (2 : ZMod 3)`. Hoisted for the same reason; proof uses
   `rintro ⟨r, hr⟩` then a `decide` on `∀ x : ZMod 3, x * x ≠ 2`.

3. **`legendreSym_three_eq_one_iff_p_mod_three_eq_one`** (private,
   inside `namespace Proofs`): the helper bridging `(p/3) = 1 ↔ p ≡ 1 mod 3`
   for `p ≠ 3`. Uses `legendreSym.eq_one_iff'` + `ZMod.natCast_mod` +
   case split on `p % 3`. ~28 LOC.

4. **`legendreSym_neg_three_eq_one_iff`** (public, inside
   `namespace Proofs`): the S4 ACT Step 2 deliverable. ~30 LOC including
   the `h3cast` coercion shim required to match QR's RHS pattern.

## 3. Proof structure

The main lemma:

```
legendreSym p (-3) = 1 ↔ p % 3 = 1
```

splits as:

1. **Decompose via Step 1** (`legendreSym_neg_three` from PR #21226):
   `(-3/p) = (-1/p) · (3/p)`.

2. **Compute `(-1/p)` via `legendreSym.at_neg_one`**:
   `(-1/p) = χ₄ p`.

3. **Case-split on `p % 4 ∈ {1, 3}`** (forced by `p ≠ 2`, omega):

   - **`p % 4 = 1`**: `χ₄ p = 1` (via `ZMod.χ₄_nat_one_mod_four`); QR
     for `p % 4 = 1` gives `(p/3) = (3/p)`. After `one_mul` and the
     `(3 : ℤ) ↔ ((3 : ℕ) : ℤ)` `h3cast`, rewriting `legendreSym p ↑3`
     to `legendreSym 3 p` via QR reduces to the helper.

   - **`p % 4 = 3`**: `χ₄ p = -1` (via `ZMod.χ₄_nat_three_mod_four`);
     QR for `p, q ≡ 3 mod 4` gives `(p/3) = -(3/p)`. After substituting
     and simplifying `(-1) * -(3/p)` to `(3/p)`, reduces to the helper.

4. **Helper closes both branches**: `(p/3) = 1 ↔ p ≡ 1 mod 3` via
   `legendreSym.eq_one_iff'` + `IsSquare` characterization on
   `(p : ZMod 3)`.

## 4. Build iteration log (4 Docker iters)

| Iter | Failure | Root cause | Fix |
|------|---------|------------|-----|
| 1 | `Unknown identifier 'χ₄_nat_one_mod_four'` (and `_three_mod_four`) | Lives in `namespace ZMod` not in scope | Namespace-qualify: `ZMod.χ₄_nat_*_mod_four` |
| 2 | `Expected type must not contain free variables: ∀ (x : ZMod 3), x * x ≠ 2` | In-namespace `decide` cannot evaluate the closed prop because the surrounding context (with `p : ℕ`, `hp_fact`, etc.) is treated as free vars | Hoisted helper above `namespace Proofs` |
| 3a | `rw failed: Did not find an occurrence of legendreSym p ↑3 in target` | Target has `legendreSym p (3 : ℤ)` via `OfNat`; QR's RHS has `legendreSym p ((3 : ℕ) : ℤ)` via `Nat.cast`. Defeq but not syntactically equal. | Added `h3cast : (3 : ℤ) = ((3 : ℕ) : ℤ)` (proved `by norm_cast`); `rw [h3cast]` before QR |
| 3b | `Application type mismatch: 3 % 4 = 3 vs p % 4 = 3` | QR_three_mod_four's first hypothesis is for OUR prime `p`, not for the constant `3`. I had the args swapped. | Swapped: `hp4` first, `(by decide : 3 % 4 = 3)` second |
| 4 | `Type mismatch: False vs p % 3 = 1` | `h_squares r hr.symm : False` doesn't unify with the goal `p % 3 = 1` automatically | Use `(... ).elim` to extract any goal from False |
| ✓ | — | — | All 3058 jobs succeed in 11s |

## 5. Bearer table (all pin-verified at SHA 2df2f0150c)

| API | File:Line |
|-----|-----------|
| `legendreSym.at_neg_one` | `Mathlib/NumberTheory/LegendreSymbol/Basic.lean:272` |
| `legendreSym.eq_one_iff'` | `Mathlib/NumberTheory/LegendreSymbol/Basic.lean:181` |
| `ZMod.χ₄_nat_one_mod_four` | `Mathlib/NumberTheory/LegendreSymbol/ZModChar.lean:89` |
| `ZMod.χ₄_nat_three_mod_four` | `Mathlib/NumberTheory/LegendreSymbol/ZModChar.lean:94` |
| `legendreSym.quadratic_reciprocity_one_mod_four` | `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean:134` |
| `legendreSym.quadratic_reciprocity_three_mod_four` | `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean:142` |
| `ZMod.natCast_mod` | `Mathlib/Data/ZMod/Basic.lean:736` |
| `Nat.Prime.mod_two_eq_one_iff_ne_two` | core / Mathlib (one_iff variant) |

## 6. Risks fired vs prediction (S14 PREP §5 risk inventory)

| Risk | Predicted | Actual fire | Severity |
|------|-----------|-------------|----------|
| R1 PASTE-ONLY (steps a-c) | should fire automatically | ✓ fired, no work | — |
| R2 LOW (p%4 case-split) | solid bearer | ✓ closed via `omega` | — |
| R3 MEDIUM (p%3 ≠ 0) | bearer cited | ✓ closed via `Nat.Prime.eq_one_or_self_of_dvd` | — |
| R4 MEDIUM (sub-lemma `(p/3) = 1 ↔ p % 3 = 1`) | needs ~10 LOC, 2 decide sub-sorries | ✓ closed via `legendreSym.eq_one_iff'` + `IsSquare` characterization | medium |
| R5 INFRA Docker | run before shipping | ✓ Docker reachable; build clean | — |
| **R6 NEW** (decide free-var) | not predicted | hoist helpers outside namespace | **post-mortem-add** |
| **R7 NEW** (ℤ-coercion mismatch on QR's `↑3`) | not predicted | `h3cast` shim | **post-mortem-add** |
| **R8 NEW** (QR arg order) | not predicted | swap args | **post-mortem-add** |

## 7. File metrics

| Metric | Pre-S15 | Post-S15 | Δ |
|--------|---------|----------|---|
| LOC | 465 | 559 | +94 |
| sorries | 0 | 0 | 0 |
| axioms | 0 | 0 | 0 |
| theorems (grep) | ~32 | 36 | +4 |

The +94 LOC overshoots the S14 PREP §5 estimate of ~50 LOC by ~88%
(main reason: the 3 post-mortem-added risks above each consumed 10-20 LOC).

## 8. Gallery `meta.json` updates

- `meta.lineCount` 465 → 559
- `meta.theoremCount` 24 → 36 (also closes S14 PREP §7 drift acknowledgement)
- `leanFile.lineCount` / `leanFile.theoremCount` mirror

## 9. Sibling-coordination

`gh pr list --search "ZsqrtdNegTwoOQ03 is:open"` returns 0 open PRs at
S15 ACT push time. No race risk.

## 10. S16+ readiness (Step 3 next)

S4 ACT Step 3 (per S14 PREP §6): extract `α : Eisenstein` with
`norm α = p` from `IsSquare (-3 : ZMod p)`; parity case-split on
`x_int`. Budget ~30 LOC. Uses `legendreSym.eq_one_iff` (ℤ form) +
`PrincipalIdealRing.to_uniqueFactorizationMonoid` +
`UniqueFactorizationMonoid.irreducible_iff_prime`.

After Step 3 lands, S5 ACT (the main theorem
`sq_add_three_sq_of_prime_one_mod_three`, ~100 LOC) closes the
gallery entry.

## 11. Decisions log

- **Hoisting `decide` helpers**: 2 helpers (`two_ne_zero_zmod_three`,
  `not_isSquare_two_zmod_three`) hoisted out of `namespace Proofs`
  because in-namespace `decide` fails on closed props inside a
  parameterized context. Cleanest workaround; alternative `decide +revert`
  was not attempted but would have been equivalent.
- **`h3cast` shim**: chose explicit `have h3cast : (3 : ℤ) = ((3 : ℕ) : ℤ) := by norm_cast`
  over `push_cast`/`norm_cast` in the proof body, because the rewrite
  target is a single subterm in a binder context where the global tactic
  could over-rewrite.
- **`.elim` over `exfalso; exact ...`**: chose `(not_isSquare_two_zmod_three hLS).elim`
  for the contradiction path because it's a single token and Lean's
  elaborator can produce any goal type from `False`.
- **Hybrid PREP/ACT execution**: S14 PREP had marked Step 2 as
  "paste-ready ~50 LOC". The actual discharge took ~94 LOC and 4 Docker
  iterations due to 3 unanticipated risks (R6-R8). All resolved within
  the same session — no PREP follow-up needed.
