# Problem: Solution of the Cubic: Connection to Quartic via Resolvent Cubic

## Statement

### Plain Language

Formalize the algebraic chain linking Cardano's cubic formula (Wiedijk #37,
`SolutionOfCubic.lean`) to Ferrari's quartic solution (Wiedijk #46, `GeneralQuartic.lean`)
via the **resolvent cubic**.

Ferrari's method for solving a quartic y⁴ + py² + qy + r = 0 introduces an auxiliary
parameter m, leading to the resolvent cubic:

  8m³ + 20pm² + (16p² − 8r)m + (4p³ − 4pr − q²) = 0

The key formalization goal: prove that a root of this resolvent cubic (found via Cardano's
formula) yields a factorization of the quartic into two quadratics. This chains the two
proofs: `SolutionOfCubic.cardano_formula_is_root` feeds into `GeneralQuartic.ferrari_factorization`.

### Formal Statement

```lean
-- Goal: if m is a root of the resolvent cubic, then the quartic factors
theorem quartic_factors_given_resolvent_root (p q r m : ℂ)
    (hm : Polynomial.eval m (GeneralQuartic.resolventCubic p q r) = 0) :
    ∃ (α β : ℂ), ∀ y : ℂ,
    Polynomial.eval y (GeneralQuartic.depressedQuartic p q r) =
    Polynomial.eval y ((X^2 + C (p/2 + m) - C α * X - C β) *
                       (X^2 + C (p/2 + m) + C α * X + C β)) := by
  sorry

-- Bridge: Cardano's formula gives a root of the resolvent cubic
theorem cardano_gives_resolvent_root (p q r : ℂ) :
    let (P, Q) := GeneralQuartic.resolventCubicCoeffs p q r
    Polynomial.eval (SolutionOfCubic.cardanoRoot P Q)
      (GeneralQuartic.resolventCubic p q r) = 0 := by
  sorry
```

## Classification

```yaml
tier: B
significance: 7
tractability: 6
tags:
  - algebra
  - cubic
  - quartic
  - resolvent
  - galois-theory
  - wiedijk
  - cardano
  - ferrari
```

**Significance**: 7/10 — Completes the chain Wiedijk #37 → #46, demonstrating
autonomous Lean research can connect major classical results. Creates a reusable
bridge between two independently formalized theorems.

**Tractability**: 6/10 — The algebra is classical and fully understood; the
challenge is aligning two independent formalizations that may use different
conventions (complex numbers, polynomial representations, cube root definitions).

## Why This Matters

1. **Chaining gallery proofs**: `GeneralQuartic.lean` already defines `resolventCubic`
   and mentions dependence on Cardano's formula — proving this connection completes
   the mathematical chain.
2. **Wiedijk database completeness**: Both #37 and #46 are in the gallery; linking them
   shows Lean can formalize the dependencies between classical results.
3. **Methodological value**: Demonstrates how to bridge two independently-developed
   proof namespaces (`SolutionOfCubic` and `GeneralQuartic`).

## Existing Infrastructure

```
proofs/Proofs/
  SolutionOfCubic.lean         -- Wiedijk #37: Cardano's formula (depressed cubic)
  GeneralQuartic.lean          -- Wiedijk #46: Ferrari's method (quartic)
  SolutionOfCubicOQ03.lean     -- OQ-03 extension (Vieta's formulas)
```

**Key definitions to link:**

In `SolutionOfCubic`:
- `depressedCubic p q : ℂ[X]` — X³ + pX + q
- `cardanoRoot p q : ℂ` — the Cardano formula value
- `cardano_formula_is_root` — theorem that cardanoRoot is a root

In `GeneralQuartic`:
- `resolventCubic p q r : ℂ[X]` — 8m³ + 20pm² + (16p²-8r)m + (4p³-4pr-q²)
- `depressedQuartic p q r : ℂ[X]` — y⁴ + py² + qy + r
- The quartic proof has a TODO: "Explicit solution using cubic formula"

**The gap to fill**: Normalize `resolventCubic` to depressed form so `cardanoRoot`
applies, then show its value achieves the discriminant = 0 condition for Ferrari's
factorization.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `solution-of-cubic` | Source: provides `cardanoRoot` and `cardano_formula_is_root` |
| `general-quartic` | Target: contains `resolventCubic`, needs the bridge |
| `solution-of-cubic-oq-03` | Vieta's formulas for cubic roots (useful for root sum/product) |
| `solution-of-cubic-oq-03-oq-01` | Discriminant analysis for cubic |

## Suggested First Steps

1. **OBSERVE**: Read `GeneralQuartic.lean` fully — understand what's already proven
   and where the TODO "depends on cubic formula" lives. Identify the missing theorems.
2. **ORIENT**: Reduce `resolventCubic p q r` to depressed form via substitution
   m = n − 20p/24. Compute the depressed form's P and Q parameters. Verify they
   match `SolutionOfCubic.discriminant`.
3. **DECIDE**: Prove `cardano_gives_resolvent_root` first — this bridges the two
   namespaces. Then use it to fill the gap in `ferrari_factorization`.

## Known Obstacles

- `SolutionOfCubic.cubeRoot` uses `z ^ (1/3 : ℂ)` which is multivalued — the correct
  branch must be chosen for the quartic application. May need `Complex.cpow` lemmas.
- `GeneralQuartic.resolventCubic` has a leading coefficient of 8 (not 1) — must
  normalize before applying Cardano's depressed cubic formula.
- Two independent namespaces with different helper lemma styles; bridging requires
  explicit type annotations and coercions.

## Initial State

- Phase: OBSERVE
- Attempts: 0
- Last updated: 2026-04-22
