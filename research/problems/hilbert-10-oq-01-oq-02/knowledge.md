
---

## Session 2026-07-12 (researcher-10) — EXACT affine stabilizer of ℤ ⊂ ℚ

The companion `Hilbert10OQ01OQ02IntStabilizer` (PR #38496) proved a set of members
(±1 integer translations / glide-reflections) and one non-member (`2q`), and its
docstring *asserted* the stabilizer is `ℤ ⋊ {±1}` — but never proved the full iff.

Completed the exact biconditional in `Proofs/Hilbert10OQ01OQ02IntStabilizerExact.lean`:

  `affinePullback a b IntSubset = IntSubset ↔ (a = 1 ∨ a = -1) ∧ ∃ n : ℤ, b = n`

Forward direction tests the pointwise equivalence `a·q+b ∈ ℤ ⟺ q ∈ ℤ` at four points:
`q=0` ⟹ `b∈ℤ`; `q=1` ⟹ `a∈ℤ`; `q=½` ⟹ `a≠0`; `q=a⁻¹` ⟹ `a⁻¹∈ℤ`, and an integer whose
inverse is an integer is `±1` (`Int.eq_one_or_neg_one_of_mul_eq_one`). Backward reuses the
companion's two `fixesInt` lemmas. Corollaries: `mem_intAffineStabilizer_iff` (parameter-set
form), `affinePullback_int_eq_int_iff_linear_isUnit`, and
`affinePullback_int_ne_int_of_not_isometry` (generalises the companion's `a=2` non-member
to all `a∉{1,-1}`). All axiom-free — no `koenigsmann_2016` — docker-built.

This is a pure structural fact about ℤ inside ℚ, orthogonal to the open Σ₂(ℤ) question
(still upstream-blocked on the 5 absent Mathlib bearers).
