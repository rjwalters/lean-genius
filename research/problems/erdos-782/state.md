# Research State: erdos-782

## Current State
**Phase**: AXIOMATIZED
**Path**: full
**Since**: 2026-03-28T09:25:00Z (graduated from active research)
**Iteration**: 2

## Outcome

Formalization complete with 3 axioms encoding deep results. The
gallery entry is published with `status: axiomatized`, badge
`axiom`, 0 sorries.

- Lean file: `proofs/Proofs/Erdos782Problem.lean` (328 lines)
- Sorries: 0
- `axiom` declarations: 3 (all deep, all classical/published)
- `opaque` declarations: 1 (`BombieriLangConjecture`, not an axiom)
- Theorems proved: 10 (including 3 explicit constructions)

## Mathematical Content

**Problem (open):** Brown-Erdős-Freedman [BEF90] asked
1. Do the squares contain arbitrarily long quasi-progressions
   (sequences with bounded gap variation)?
2. Do the squares contain arbitrarily large combinatorial cubes
   `a + {∑ εᵢbᵢ : εᵢ ∈ {0,1}}`?

Q1 ⟹ Q2. Solymosi conjectured ¬Q2; Cilleruelo-Granville proved
¬Q2 conditional on Bombieri-Lang.

**Proved theorems:**
- `squares_contain_3AP`: {1, 25, 49} = {1², 5², 7²} is an AP with d=24
- `squares_contain_2cube`: {0, 9, 16, 25} = {0², 3², 4², 5²}
  via the Pythagorean triple 3² + 4² = 5²
- `question1Weak_true`: weak Q1 (C may depend on k) is trivially
  true via consecutive squares (1², 2², ..., k²) with d = 3, C = 2k
- `question1_implies_question1Weak`: quantifier-swap reduction
- `no_cubes_implies_no_quasiprog`: contrapositive of Q1 ⟹ Q2
- `conditional_q2_negative`: BombieriLang ⟹ ¬Q2
- `solymosi_equiv`: Solymosi conjecture has equivalent ∃-form

## Axioms (3 — all deep)

1. **`no_4AP_in_squares`**: ¬ContainsAP Squares 4. Classical
   (Fermat 1640 / Euler), provable via `not_fermat_42` from
   `Mathlib.NumberTheory.FLT.Four`. The reduction (4 squares in
   AP ⟹ Fermat42 contradiction) is ~50–100 lines of Pythagorean
   parametrization + descent.

2. **`question1_implies_question2`**: Question1 → Question2.
   A combinatorial Ramsey-type argument from [BEF90].

3. **`cilleruelo_granville`**: BombieriLang →
   ∃ k, ¬ContainsCube Squares k. Conditional result of
   Cilleruelo-Granville (2007); requires algebraic geometry
   machinery (varieties of general type) beyond current Mathlib.

## Blockers

None for the current axiomatized status. For axiom elimination:

- **`no_4AP_in_squares`**: tractable, ~50–100 lines using
  `Mathlib.NumberTheory.FLT.Four.not_fermat_42`. The standard
  reduction proceeds: 4 squares p² < q² < r² < s² in AP gives
  2q² = p² + r² and 2r² = q² + s²; Pythagorean parametrization
  forces an x⁴ + y⁴ = z² solution, contradicting `not_fermat_42`.

- **`question1_implies_question2`**: deep combinatorial reduction;
  estimated 200+ lines.

- **`cilleruelo_granville`**: blocked on Mathlib's lack of
  general-type variety machinery; not tractable in the current
  ecosystem.

## Next Action

Optional axiom-elimination target: prove `no_4AP_in_squares`
via `Mathlib.NumberTheory.FLT.Four.not_fermat_42`. Otherwise,
no further research work required at the current axiomatized
status; pool entry is `completed`.
