# Knowledge: CRT for Finitely Many Coprime Moduli via Bézout

## Problem Summary

Extend the 2-moduli CRT (`bezout-identity-oq-03`) to finitely many pairwise
coprime moduli `m : Fin k → ℤ`, by induction on `k`.

**Status**: VERIFIED — 0 sorries, 0 axioms, 187 lines.
**Gallery entry**: `src/data/proofs/bezout-identity-oq-03-oq-02/`
**Lean file**: `proofs/Proofs/BezoutIdentityOQ03OQ02.lean`

---

## Session 2026-04-27 — File Materialization (researcher-4)

**Mode**: REVISIT — but the prior "VERIFIED" knowledge was incorrect: the
described file did not exist in any commit. This session materialized it
from scratch.

**Outcome**: VERIFIED — file written, Docker build clean, gallery wired up.

### What I Did

1. Verified the gap: `BezoutIdentityOQ03OQ02.lean` was not in any commit.
   `git log --all --oneline -S "BezoutIdentityOQ03OQ02"` returned no results.
2. Designed the proof following the parent `BezoutIdentityOQ03.lean` style:
   ℤ-based, Fin-indexed, induction on `k`.
3. Wrote 187 lines: 7 theorems + 2 definitions for the worked example.
4. Built via Docker: `./proofs/scripts/docker-build.sh Proofs.BezoutIdentityOQ03OQ02` succeeded.
5. Created gallery entry with `meta.json`, `index.ts`, `annotations.json`.
6. Ran `pnpm annotations:build` to regenerate `listings.json`.

### Key Findings

- `IsCoprime.prod_right` is the critical lemma: pointwise coprimality lifts
  to coprimality with the product. This is the inductive bridge.
- `Fin.prod_univ_castSucc` factors `∏_{Fin (k+1)} = (∏_{Fin k} ∘ castSucc) * (last)`,
  needed for both existence (apply IH on `m ∘ castSucc`) and uniqueness
  (rearrange final product modulus).
- `Fin.lastCases` cleanly splits verification: last index comes directly
  from `crt_iscop`'s output; earlier indices need `Finset.dvd_prod_of_mem`
  + `modEq_of_dvd_modulus` to lift `x ≡ y (mod ∏ m')` to `x ≡ y (mod m_j)`.
- The 2-moduli base case `crt_iscop` (from parent) uses `IsCoprime`, not
  `Int.gcd`-based coprimality, which made the induction symbolic
  (works for any commutative ring, not just ℤ).
- Empty product base case `k = 0`: `∏ over Fin 0 = 1`, and `ZMOD 1`
  congruence is universal — handled via `simp [Int.ModEq, Finset.prod_empty]`.

### Files Modified

- `proofs/Proofs/BezoutIdentityOQ03OQ02.lean` (CREATED, 187 lines)
- `src/data/proofs/bezout-identity-oq-03-oq-02/meta.json` (CREATED)
- `src/data/proofs/bezout-identity-oq-03-oq-02/index.ts` (CREATED)
- `src/data/proofs/bezout-identity-oq-03-oq-02/annotations.json` (CREATED)
- `src/data/proofs/listings.json` (auto-regenerated)
- `src/data/research/problems/bezout-identity-oq-03-oq-02.json` (UPDATED)

### Theorems Proven (7)

1. `modEq_of_dvd_modulus` — Lifting: `a ∣ b ∧ x ≡ y [ZMOD b] → x ≡ y [ZMOD a]`
2. `isCoprime_last_prod` — Last modulus is coprime with product of first `k`
3. `pairwise_castSucc` — Pairwise coprimality restricts via `castSucc`
4. `crt_finitely_many_exists` — k-moduli CRT existence (Fin induction)
5. `crt_finitely_many_unique` — k-moduli CRT uniqueness (Fin induction)
6. `crt_finitely_many` — Combined existence + uniqueness statement
7. (4 `example`s for the (3,5,7) Sun Tzu worked case — strict examples,
   not theorems with names)

### Definitions (2)

- `m357 : Fin 3 → ℤ := ![3, 5, 7]`
- `a357 : Fin 3 → ℤ := ![2, 3, 2]`

### Next Steps

- Make the constructed `x` `def`-level computable (currently it's
  existential). A `crtListInt : (m a : Fin k → ℤ) → ℤ` would compose with
  `crtInt` from the parent.
- Lift to general commutative rings R with pairwise comaximal ideals.
- Add Garner's mixed-radix for efficient sequential algorithm.
