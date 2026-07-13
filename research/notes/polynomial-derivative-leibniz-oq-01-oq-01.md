# Discriminant Identity for a Split Polynomial
Open Question: polynomial-derivative-leibniz-oq-01-oq-01 (child of polynomial-derivative-leibniz-oq-01)

## Result
Over any `CommRing R` with a linearly ordered index type `ι`, for `p = ∏_{i∈s} (X − rᵢ)`:

1. `prod_eval_derivative_eq` : ∏_{i∈s} p'(rᵢ) = ∏_{i∈s} ∏_{j∈s.erase i} (rᵢ − rⱼ)
   (full off-diagonal product of node differences), from the parent entry's
   `eval_derivative_prod_X_sub_C`.

2. `prod_eval_derivative_eq_sign_mul_sq` :
       ∏_{i∈s} p'(rᵢ) = (−1)^N · ( ∏_{i∈s} ∏_{j∈s, i<j} (rᵢ − rⱼ) )²
   where N = ∑_{i∈s} #{ j ∈ s : i < j } is the number of unordered pairs of s (= C(#s,2)).
   The squared factor is the Vandermonde product of node differences, so the RHS is the
   discriminant of the split polynomial up to the sign (−1)^N.

Answers open question #1 left by the parent entry.

## Proof idea
Split `s.erase i` into elements below/above `i` (linear order). The below-half, after
swapping the two indices (`Finset.prod_comm'`), pairs term-by-term with the above-half;
each pair `(rᵢ−rⱼ)(rⱼ−rᵢ) = −(rᵢ−rⱼ)²` yields a square and a factor of −1. Collect the
signs with `prod_pow_eq_pow_sum` and the squares with `prod_pow`.

Lemmas used (all confirmed present in Mathlib v4.26.0): Finset.prod_union, prod_comm',
prod_mul_distrib, prod_const, prod_pow, prod_pow_eq_pow_sum, lt_or_gt_of_ne, lt_asymm.
No axioms, no sorries, no native_decide/decide.

## Verification status (2026-07-02)
- Proof ELABORATED CLEANLY via `lake env lean` (EXIT=0, zero errors) on a self-contained
  inlined copy (parent lemma inlined, `import Mathlib` only), during a consistent cache
  window.
- Authoritative `docker-build.sh` verification BLOCKED: host disk 100% full (131Mi free),
  causing Docker containerd meta.db I/O errors AND intermittent host `.lake` olean
  corruption (segfaults / invalid-header). Same infra outage documented previously.
- ACTION NEEDED: re-run `./proofs/scripts/docker-build.sh Proofs.PolynomialDerivativeLeibnizOQ01OQ01`
  once host disk is freed, then promote to a verified gallery entry (0-axiom).
