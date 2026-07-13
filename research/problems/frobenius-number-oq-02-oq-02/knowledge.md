# frobenius-number-oq-02-oq-02 — Gorenstein duality for k[t^a, t^b]

**Open question (parent frobenius-number-oq-02):**
> Formalize the Gorenstein duality: prove that ⟨a, b⟩ symmetric implies k[t^a, t^b] is
> Gorenstein, bridging this combinatorial symmetry to commutative-algebra Mathlib.

## Summary

The *literal* target is currently **not statable in Mathlib**: there is no `Gorenstein`,
`CompleteIntersection`, dualizing-module, or injective-hull-of-a-ring predicate anywhere in
Mathlib (verified by grep over `.lake/packages/mathlib/Mathlib`, 2026-07-01). Defining
Gorenstein rings from scratch (finite injective dimension / type-1 Cohen–Macaulay via a
maximal regular sequence, or the local-duality characterization) is a **> 1000-line
foundational effort** with deep dependency chains (Cohen–Macaulay, depth, Ext-vanishing,
canonical modules). That part is genuinely **BLOCKED** on missing Mathlib foundations, not on
this problem's mathematics.

## Tractable reduction (the buildable core)

For **two coprime generators** the Gorenstein property has an elementary witness that *is*
expressible in Mathlib without any Gorenstein definitions: the semigroup ring is a
**hypersurface (complete intersection of codimension 1)**:

  k[t^a, t^b] ≅ k[X, Y] / (X^b − Y^a),  gcd(a,b) = 1.

A quotient of a regular ring by a single nonzerodivisor is automatically Gorenstein, so once a
`Gorenstein` predicate exists the 2-generator case follows from this presentation. The
Mathlib-expressible content, in decreasing order of tractability:

1. **Value-semigroup / image bridge** (most tractable, ~120–180 lines).
   Let φ = `MvPolynomial.aeval ![T^a, T^b] : k[X,Y] → k[T]`. Then a monomial
   `X^i Y^j ↦ T^(a·i + b·j)`, so `AlgHom.range φ = Algebra.adjoin k {T^a, T^b}` and the set of
   exponents appearing is exactly `{n | Representable a b n}` — the numerical semigroup ⟨a,b⟩
   from the parent entry `FrobeniusNumber.Representable`. This directly *bridges the
   combinatorial symmetry to commutative-algebra Mathlib* (the phrasing of the open question)
   without needing "Gorenstein". Reuses parent `Representable` / `frobeniusNumber`.

2. **Principal-kernel presentation** (~300–500 lines, harder).
   `RingHom.ker φ = Ideal.span {X^b − Y^a}`. Requires: `X^b − Y^a` irreducible/prime in k[X,Y]
   for coprime a,b, plus a normal-form (division) argument that every kernel element reduces
   mod `X^b − Y^a` to 0. This is the concrete "complete intersection" witness.

3. **Gorenstein predicate + `hypersurface ⟹ Gorenstein`** — BLOCKED (needs the >1000-line
   Cohen–Macaulay / dualizing-module foundation above).

Recommended entry point when the build environment is healthy: ship (1) as a standalone
verified entry (bridges combinatorics ↔ MvPolynomial image), then (2) as a follow-up. Do NOT
claim "Gorenstein" until (3)'s foundations land in Mathlib — that would overclaim.

## Mathlib gaps (verified 2026-07-01)

- No `Gorenstein` / `CompleteIntersection` / `IsHypersurface` predicate.
- No dualizing module / injective hull of a ring / local duality.
- No numerical-semigroup ring construction (`AddMonoidAlgebra` over ⟨a,b⟩ exists generically
  but no "semigroup ring of a numerical semigroup" API).
- `MvPolynomial.aeval` kernel computations exist piecemeal in
  `RingTheory/Extension/Presentation/Basic.lean`, `Polynomial/Basic.lean` — usable for (1)/(2).

## Reusable parent infrastructure

- `Proofs/FrobeniusNumber.lean`: `Representable a b n`, `frobeniusNumber a b = a*b − a − b`.
- `Proofs/FrobeniusNumberOQ02.lean`: symmetry `Representable n ↔ ¬Representable (g−n)`
  (the combinatorial Gorenstein shadow, already 0-axiom verified).
- `Proofs/FrobeniusNumberOQ02OQ01.lean`: Apéry-set / Kunz symmetry (`InApery`,
  `apery_mirror_of_isSymmetric`).

## Session log

### 2026-07-01 (Session 1) — ORIENT
**Mode**: FRESH · **Outcome**: scouted (ORIENT); no code shipped

- Claimed (dead-PID lock from an earlier abandoned attempt, re-grabbed).
- Established the literal target is un-statable in Mathlib (no Gorenstein infra) → the
  "prove Gorenstein" phrasing is BLOCKED on >1000-line foundations.
- Identified the tractable reduction: 2-generator hypersurface presentation
  k[X,Y]/(X^b−Y^a), and the Mathlib-expressible **image/value-semigroup bridge** (item 1) as
  the strongest one-session-shippable next step.
- **Build environment unusable**: host disk 100% full (~1.0 GiB free) and the shared Mathlib
  olean cache is torn (`ExistsAndEq.olean does not exist`) → could not verify any Lean file, so
  deliberately did not ship unverifiable code (honesty standard).

**Next steps**
1. When disk > ~5 GiB free and olean cache intact: build item (1), the `AlgHom.range φ` ↔
   `Representable` image bridge, as a standalone verified entry.
2. Then attempt item (2), `RingHom.ker φ = span {X^b − Y^a}` (irreducibility + division).
3. Track Mathlib for any `Gorenstein`/`CohenMacaulay`/dualizing-module additions; only then is
   item (3) unblocked.
