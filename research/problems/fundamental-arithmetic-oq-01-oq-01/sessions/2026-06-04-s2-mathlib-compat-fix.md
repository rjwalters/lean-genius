# Session 2 — Mathlib v4.26.0 API compatibility repair

**Date**: 2026-06-04
**Researcher**: researcher-11
**Mode**: REPAIR (re-validation against current Mathlib)
**Outcome**: Build clean — Docker build of `Proofs.FundamentalArithmeticOQ01OQ01` succeeds; 0 sorries, 0 axioms, 12 theorems + 1 private lemma, 220 lines.

## What I Did

Re-ran the existing `FundamentalArithmeticOQ01OQ01.lean` (from Session 1, PR #15233) against the current Mathlib pin (`v4.26.0`). Several API drifts had accumulated since the original work:

1. **`Finset.induction_on` binder shape changed.** The `insert` case now expects explicit element/finset binders (`| @insert a s ha ih`) rather than the older `| insert ha ih` + `rename_i a s _` pattern. Without this, `rename_i a s _` produces "too many variable names provided" and `ha` is misinterpreted.
2. **`Finset.prod_ne_zero` removed.** Replaced with `Finset.prod_ne_zero_iff.mpr`.
3. **`Nat.mem_primeFactors` is now an iff, not a hypothesis-consuming term.** `Nat.mem_primeFactors hn` no longer typechecks; use bare `Nat.mem_primeFactors` and rewrite. The result is now a triple conjunction `p.Prime ∧ p ∣ n ∧ n ≠ 0`, so the projection is `h.2.1`, not `h.2`.
4. **`Nat.coprime_iff_disjoint` unknown.** The current Mathlib API is `Nat.Coprime.disjoint_primeFactors : Disjoint m.primeFactors n.primeFactors`. Bridge to factorization-support via `Nat.support_factorization`.
5. **`Finset.sum_ite_eq` vs `Finset.sum_ite_eq'`.** The indicator-sum produced has the form `if x = a then ... else 0` (bound variable on the left). The matching lemma is the primed variant `Finset.sum_ite_eq'`, not the original.
6. **`Finsupp.not_mem_support_iff` deprecated.** Renamed to `Finsupp.notMem_support_iff` (camelCase convention).
7. **`native_decide` fails on `Finsupp.single` equalities.** `Finsupp.single` is noncomputable, so equality checks on Finsupp sums cannot be reduced by `native_decide`. Reformulated the affected `example`s to test pointwise factorization values (`(12 : ℕ).factorization 2 = 2`) and primeFactors-set equalities, which both reduce cleanly.
8. **Generalized helper `factorization_finset_prod`.** The original lemma was specialized to `∏ m ∈ s, m` (identity product), so the `rw` at the key-lemma site (`∏ p ∈ f.support, p ^ f p`) did not match. Generalized to `{ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℕ)`, with explicit `g`. The `DecidableEq ι` requirement came from `Finset.induction_on`.
9. **Suppressed `_hn` and `_hp` unused-binder warnings** in `fta_uniqueness` and `prime_exponent_eq_factorization` (kept for API symmetry but unused in the body).

## Files Modified

- `proofs/Proofs/FundamentalArithmeticOQ01OQ01.lean` (25 insertions, 25 deletions; net zero LOC)

## Verification

```
./proofs/scripts/docker-build.sh Proofs.FundamentalArithmeticOQ01OQ01
=> Build succeeded.
```

No sorries, no axioms, no `set_option` overrides. Same theorem count and statements as session 1 — this session is API repair only.

## Next Steps

- Commit and push branch
- Open PR labeled `research`
