# Knowledge Base: erdos-485-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

The open question asks whether f(k) → ∞ (the minimum number of terms in P(x)²
for polynomials with k terms) can be proved COMBINATORIALLY via sumset bounds,
rather than algebraically via height theory (Schinzel-Zannier 2009).

The combinatorial approach: support(P²) relates to the sumset A + A where
A = support(P). If no coefficient cancellation occurs, |A + A| ≥ 2|A| - 1
gives termCount(P²) ≥ 2k - 1.

---

## Insights

1. **Sumset containment always holds**: support(P²) ⊆ support(P) + support(P).
   This is because coeff(P², n) = Σ_{a+b=n} c_a·c_b, and if nonzero, some
   pair (a,b) with a ∈ supp(P), b ∈ supp(P) must contribute.

2. **Positive-coefficient case is complete**: When all coefficients ≥ 0,
   no cancellation occurs. Every sumset element gets a positive coefficient
   in P². So support(P²) = A + A exactly, giving termCount(P²) ≥ 2k - 1.

3. **Cancellation barrier**: Mixed-sign coefficients can cancel. Example:
   P = 1 - x² - (1/2)x⁴. The x⁴ coefficient of P² equals
   c₀·c₄ + c₂·c₂ + c₄·c₀ = (-1/2) + 1 + (-1/2) = 0.
   So 4 ∈ A + A but 4 ∉ support(P²).

4. **The gap**: The combinatorial approach proves f_+(k) → ∞ (positive coefficients)
   but NOT f(k) → ∞ (general polynomials). Bridging this gap requires controlling
   cancellation — an algebraic, not purely combinatorial, phenomenon.

5. **Mathlib gap (status update 2026-05-16)**: The sumset bound
   |A + A| ≥ 2|A| - 1 is NOW IN MATHLIB at v4.26.0 as the additive form
   of `cauchy_davenport_mul_of_linearOrder_isCancelMul` (file
   `Mathlib/Combinatorics/Additive/CauchyDavenport.lean`). Mathlib also
   has Plünnecke-Ruzsa (`Mathlib/Combinatorics/Additive/PluenneckeRuzsa.lean`).
   Our hand-rolled `sumset_card_lower_bound` (lines 188–220 of
   `Erdos485OQ02.lean`) can be refactored to a ~3-LOC Cauchy-Davenport
   invocation. See `sessions/session-003-statesync-mathlibgap-stale.md`
   Recipe A.

---

## Dead Ends

- Direct application of |A + A| ≥ 2|A| - 1 to general polynomials fails
  because cancellation can eliminate arbitrarily many sumset elements.
- The trivial upper bound on cancellation positions (≤ k²) is too weak to help.

---

## Status (S3 STATE-SYNC 2026-05-16)

- `Erdos485OQ02.lean` is COMPLETE: 10 theorems, 0 sorries, 0 axioms.
- `sumset_card_lower_bound` is already proved from first principles (the
  earlier "1 sorry remaining" note is stale).
- 3 file-lineCount drifts in the research JSON closed (451/327/225).

---

## Next Steps (post-S3)

- **Recipe A**: Refactor `sumset_card_lower_bound` (33 → 3 LOC) using
  `Mathlib.Combinatorics.Additive.CauchyDavenport`. Keep first-principles
  proof as a pedagogical comment block. Needs Docker for build-verify.
- **Recipe B**: Add (A + B).card ≥ A.card + B.card - 1 (two-set
  variant) + Finset ℤ version (~10 LOC). Useful for Laurent-polynomial
  extensions.
- **Recipe C**: Explore Plünnecke-Ruzsa for cancellation control —
  realistic outcome is a **negative result** (formal proof that
  doubling-constant alone is insufficient). ~150-300 LOC.
- Consider: for random polynomials, how many cancellations occur on
  average? (probability-theoretic question, separate research direction)
