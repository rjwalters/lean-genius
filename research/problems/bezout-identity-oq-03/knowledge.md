# bezout-identity-oq-03: CRT via Bézout's Identity for Integers

## Problem

**Question**: "Is there a clean formalization of the Chinese Remainder Theorem building on bezout_int?"

**Answer**: YES - and it's remarkably clean.

## Session 2026-02-21 (Session 1) - Complete Proof

**Mode**: FRESH
**Outcome**: completed

### What I Did

1. Read existing Bezout identity proofs (`BezoutIdentity.lean`, `BezoutIdentityOQ01.lean`)
2. Read existing CRT formalizations (`ChineseRemainderConstructive.lean`)
3. Designed integer-native CRT proof building directly on `bezout_int`
4. Wrote `proofs/Proofs/BezoutIdentityOQ03.lean` (282 lines, 0 sorries)
5. Built successfully with Docker (`./proofs/scripts/docker-build.sh Proofs.BezoutIdentityOQ03`)
6. Created gallery data files in `src/data/proofs/bezout-identity-oq-03/`

### Key Findings

- **IsCoprime IS Bézout**: In Lean 4, `IsCoprime m n := ∃ u v, u * m + v * n = 1`
  This is exactly Bézout's identity with gcd = 1. The connection is direct.

- **Explicit formula**: x = a * n * v + b * m * u (where m*u + n*v = 1 from Bézout)
  - n*v ≡ 1 (mod m): so a*n*v ≡ a, and b*m*u ≡ 0 (mod m) vanishes
  - m*u ≡ 1 (mod n): so b*m*u ≡ b, and a*n*v ≡ 0 (mod n) vanishes

- **Proof tactic**: `linear_combination` with `-a * hbez` or `-b * hbez` closes each
  congruence goal in one line after converting via `Int.modEq_iff_dvd`

- **Uniqueness**: `IsCoprime.mul_dvd` directly gives the uniqueness result

- **Key difference from existing CRT**: `ChineseRemainderConstructive.lean` uses
  naturals + `Nat.chineseRemainder`. This new file works over ℤ directly,
  building on `bezout_int` explicitly.

### Files Modified

- Created: `proofs/Proofs/BezoutIdentityOQ03.lean` (282 lines, 0 sorries)
- Created: `src/data/proofs/bezout-identity-oq-03/meta.json`
- Created: `src/data/proofs/bezout-identity-oq-03/index.ts`
- Created: `src/data/proofs/bezout-identity-oq-03/annotations.json`

### Core Theorems Proved

1. `bezout_int`: restatement of ∃ x y, gcd(a,b) = a*x + b*y
2. `coprime_bezout`: specialization to gcd = 1 case
3. `crt_exists_via_bezout`: existence with explicit formula
4. `isCoprime_of_gcd_eq_one`: connects Int.gcd = 1 to IsCoprime
5. `crt_unique_via_bezout`: uniqueness mod m*n
6. `crt_via_bezout`: combined existence + uniqueness
7. `crt_iscop`: CRT via IsCoprime directly
8. `crtInt`: computable explicit CRT function
9. `crtInt_mod_left/right`: correctness of crtInt

### Next Steps

- Gallery registration (add to proofs index)
- Aristotle submission (all sorries are resolved, nothing to submit)
