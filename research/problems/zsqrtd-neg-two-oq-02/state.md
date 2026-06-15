# Research State: zsqrtd-neg-two-oq-02

## S3 — GAP found in PR #24443's DirichletWitnessProperty (researcher-5, 2026-06-15)

Build-free AUDIT (Docker blackout). Open PR #24443 reduces the sufficiency axiom
to a uniform `DirichletWitnessProperty`; **that property is FALSE for n ≡ 3 (mod 8)**.

- Certified (`verify_dirichlet_witness.py`): `legendreSym(d·n−1, −d)` is a function
  of `(n%8, d%8)`; n≡3 mod 8 has NO +1 class ⇒ no witness for any of the 750
  witness-less n<6000 (all ≡3 mod 8, all genuinely sums of three squares).
- So #24443's `three_sq_of_dirichlet_witness` is conditionally valid but its
  hypothesis can't be discharged; the proposed next step is impossible as written.
- Correct n≡3 route (certified): ∃ odd t, (n−t²)/2 = a²+b² ⇒ n = t²+(a+b)²+(a−b)²
  (Mathlib two-squares, not dirichlet_key_lemma).
- **Fix**: split the witness property by residue (require n%8≠3; add the n≡3
  two-squares branch). See `WITNESS-GAP-S3.md`.

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15 (S3 ACT, researcher-2)
**Iteration**: 3

## Current Focus
Axiom reduction. `ThreeSquares.lean` has 2 axioms; this session shrinks the
SUFFICIENCY axiom `not_excluded_form_is_sum_three_sq` to a single isolated
Dirichlet-witness existence statement, discharging all the surrounding
descent/assembly with no new axioms or sorries.

## Active Approach
Numerical OBSERVE (no Docker): verify the target iff, measure the `x²+2y²`
subset, exhibit gap witnesses, and isolate the Lean-ready forward direction.

## Verified This Session (Python, reproducible)
- three-square ⟺ `¬4ᵃ(8b+7)` holds over 0..20000 (0 mismatches).
- `x²+2y²` (ℤ[√−2] norm) covers only **36.1%** of three-square numbers;
  smallest miss = **5**. Subset inclusion `x²+2y² ⟹ 3 squares` clean (0 viol).
- Forward obstruction decomposition: squares mod 8 ∈ {0,1,4} (omits 7) + 4-descent.

See `verify_three_square_observe.py` and `knowledge.md`.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (numerical OBSERVE)

## Blockers
- Docker unavailable (`docker ps` hangs) → ACT (Lean forward obstruction) deferred.

## Next Action
Discharge `DirichletWitnessProperty` (the sole open piece, `ThreeSquaresSufficiency.lean`):
for `n>1`, `4∤n`, `¬excluded n`, produce `d>0` and prime `p = d·n−1` with
`legendreSym p (−d) = 1`. Ingredients now in Mathlib:
`Nat.infinite_setOf_prime_and_eq_mod` (Dirichlet primes in AP, PrimesInAP.lean:476)
+ quadratic reciprocity to fix the residue class of `p` so `−d` is a QR mod `p`.
Discharging it eliminates the sufficiency axiom from `ThreeSquares.lean` (2 axioms → 1).
Docker-gated: verify `ThreeSquaresSufficiency.lean` builds when Docker returns.
