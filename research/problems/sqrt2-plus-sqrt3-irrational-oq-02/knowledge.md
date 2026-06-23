# Knowledge: sqrt2-plus-sqrt3-irrational-oq-02

## Established Facts

- **n = 2 concrete case (merged, PR #25630).** `{1, √2, √3, √6}` is ℚ-linearly
  independent, axiom-free, via the elementary regroup-over-ℚ(√2) +
  conjugate-multiplication method. Induction heart: `√3 ∉ ℚ(√2)`.
- **General biquadratic case (this session).** For *any* coprime squarefree
  `a, b > 1`, `{1, √a, √b, √(ab)}` is ℚ-linearly independent, i.e.
  `[ℚ(√a, √b) : ℚ] = 4`. The same `linear_combination` certificate that proves
  the `{2,3}` instance works verbatim with `a, b` symbolic — verified by an
  explicit polynomial-identity check before building (the conjugate identity
  `√b·(r² − a·s²) = (a·q·s − p·r) + (p·s − q·r)·√a` is the same in both).
- Squarefree `n > 1` ⟹ `¬ IsSquare n` (`not_isSquare_of_squarefree`) ⟹
  `Irrational (√n)` via Mathlib `irrational_sqrt_natCast_iff`. This replaces the
  radicand-specific divisor-bound irrationality inputs of the n=2 file.

## Open Questions Within This Problem

- The main open question (general Besicovitch, see `problem.md`).
- n = 3 concrete: `{√d : d ∣ 30 squarefree}` (8 radicands) — needs two nested
  conjugate steps / degree-8 multiquadratic field.
- The general induction heart `sqrt_prime_not_mem_multiquadratic` (arbitrary
  finite prime set) remains `sorry` in the sibling
  `Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ02` — BUILD-class (~250–450 LOC),
  needs the "squares of a multiquadratic field are `r²·∏_{T⊆ps} q`" lemma.

## Failed Approaches

(None this session — the generalization went through as designed.)

## Promising Leads

- The two-radicand degree-doubling lemma (`sqrtb_not_in_Qsqrta`, general `a,b`)
  is the genuine n=2 layer of Besicovitch's induction. The next structural step
  is to make the conjugate-multiplication argument relative: `√c ∉ ℚ(√a, √b)`
  for a third coprime squarefree `c`, using a ℚ(√a,√b)-conjugate. If that
  generalizes uniformly it gives the induction heart elementarily, bypassing the
  powerset-squares characterization route currently sketched in the sibling file.
- `irrational_sqrt_of_squarefree` and `not_isSquare_of_squarefree` are clean,
  reusable, and plausibly Mathlib-contribution candidates.

## Session Log

### 2026-06-18 (REVISIT, FRESH-continuation) — generalize n=2 to coprime squarefree pairs

**Outcome:** progress (added verified, axiom-free general theorem).

- Confirmed PR #25630 (n=2 concrete `{1,√2,√3,√6}`) merged to main.
- Generalized to `linearIndependent_one_sqrt_sqrt_sqrt`: coprime squarefree
  `a,b > 1` ⟹ `{1,√a,√b,√(ab)}` ℚ-independent. Added supporting
  `not_isSquare_of_squarefree`, `irrational_sqrt_of_squarefree`, general heart
  `sqrtb_not_in_Qsqrta`, and a consistency corollary recovering the `{2,3}` case.
- Verified the symbolic transfer of the conjugate identity by hand before
  building (no enumeration; one structural generalization covering infinitely
  many biquadratic fields).
- File: `proofs/Proofs/Sqrt2PlusSqrt3IrrationalOQ02.lean` (already registered).
