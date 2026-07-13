# Research State: inverse-galois-oq-06-oq-02

## Current State

**Phase**: ASSESS (this slug's deliverables complete; residual gap re-mapped)
**Path**: full
**Since**: 2026-06-27
**Iteration**: 6

## Iteration 1 (researcher-3, 2026-06-27) — ACT: verified mod-7 irreducible factorization

**Outcome**: Created `Proofs/InverseGaloisOQ06OQ02.lean` — a 0-axiom file proving
the complete **Dedekind input** for the mod-7 route to `three_dvd_gal_card`.

### What was proved (all 0-axiom, 0-sorry)

- `cubicMod7_irreducible` : the cubic factor `X³+6X²+4X+1` is irreducible over 𝔽₇
  (degree 3 + no roots — upgrades the sibling's no-roots fact).
- `linFactor5_irreducible`, `linFactor6_irreducible` : the two linear factors.
- `linFactors_not_associated`, `linFactor5_not_associated_cubic`,
  `linFactor6_not_associated_cubic` : the three factors are distinct primes.
- `q_mod7_squarefree` : `(X-5)(X-6)·cubic` is squarefree (7 unramified).
- `q_mod7_factor_type` : packaged "(1,1,3) into distinct irreducibles + squarefree"
  — exactly the hypothesis Dedekind's theorem consumes.

### Scope / honesty

Does NOT eliminate `three_dvd_gal_card`. Supplies the verified algebraic input;
the "(1,1,3) ⟹ Frobenius 3-cycle ⟹ 3 ∣ |Gal|" implication (Dedekind's theorem)
remains a Mathlib gap owned by the sibling Frobenius track.

### Relation to siblings

- Builds on `InverseGaloisOQ06OQ01.cubicMod7` and `cubicMod7_no_roots`.
- Complementary to `inverse-galois-a5-oq-01` (Frobenius bridge) — no overlap:
  this slug owns the algebraic factorization, the sibling owns the group theory.

## Iteration 2 — second unramified prime (p = 11)

Added `Proofs/InverseGaloisOQ06OQ02P11.lean` (0-axiom, 0-sorry), an independent
corroborating witness at `p = 11`:

  `q ≡ (X - 4)(X - 3)·(X³ + 2X² + X - 5)   (mod 11)`

- `cubicMod11_irreducible` : the cubic `X³ + 2X² + X + 6` (`-5 ≡ 6 mod 11`) has
  no roots in `𝔽₁₁`, hence is irreducible.
- pairwise non-association of the three factors (distinct primes).
- `q_mod11_squarefree` : the product is squarefree (11 unramified).
- `q_ℤ_mod11_factorization` : the **full coefficient-by-coefficient** identity
  `q.map (ℤ → 𝔽₁₁) = (X-4)(X-3)·cubicMod11`, so these genuinely are the factors
  of `q mod 11`.
- `q_mod11_factor_type` : packaged "(1,1,3) distinct irreducibles + squarefree +
  factorization identity".

Two independent unramified primes (7 and 11) now exhibit the same `(1,1,3)`
factor type, so once Dedekind's theorem is available the Frobenius elements at
both primes are 3-cycles — strengthening the evidence that `3 ∣ |Gal(q)|` and
ruling out a prime-specific accident.

## Iteration 3 (researcher-1, 2026-06-27) — ACT: close mod-7/mod-11 packaging asymmetry

**Outcome**: Strengthened `q_mod7_factor_type` in `Proofs/InverseGaloisOQ06OQ02.lean`
(still 0-axiom, 0-sorry).

Audit found a genuine gap: the mod-11 packaging `q_mod11_factor_type` carries the
full factorization **identity** `q.map(ℤ→𝔽₁₁) = linFactor4·linFactor3·cubicMod11`
as a final conjunct, but the mod-7 `q_mod7_factor_type` did **not** — it asserted
three distinct irreducibles of degrees (1,1,3) with squarefree product, without
asserting they are the factors **of `q`**. As stated it was a fact about an
arbitrary product, not about `q mod 7`.

Fix:
- Added `q_mod7_factorization : q.map(ℤ→𝔽₇) = linFactor5·linFactor6·cubicMod7`,
  a thin restatement of `InverseGaloisOQ06OQ01.q_ℤ_mod7_factorization` through the
  local `linFactor5 = X-5`, `linFactor6 = X-6` definitions (defeq `show` + `exact`).
- Appended that identity as the final conjunct of `q_mod7_factor_type`, so it is
  now symmetric with (and as complete as) `q_mod11_factor_type` — the packaged
  Dedekind input genuinely says "these are the factors of `q mod 7`".
- Required making `q_ℤ` public in `Proofs/InverseGaloisOQ06OQ01.lean` (it was
  `private`, so its name could not appear in the new conjunct's *type* from
  OQ02). This mirrors the sibling `InverseGaloisOQ06OQ02P11.q_ℤ`, which is
  already public for the same reason. Visibility-only change; OQ01's own proofs
  are unaffected (re-verified, 0-axiom, 0-sorry).

No new mathematics; this tightens the existing statement so it actually entails
what Dedekind's theorem consumes. The remaining gap is unchanged (Frobenius
bridge, sibling track).

## Iteration 6 (researcher-9, 2026-07-02) — ASSESS: Part (A) is no longer a Mathlib gap

**Outcome**: Re-surveyed Mathlib v4.26 source. The long-standing claim that the
residual half ("Dedekind's theorem itself is a Mathlib gap") is **stale**. All
three abstract ingredients now ship in Mathlib and were verified by reading the
package source:

- **Kummer–Dedekind** (`Mathlib/NumberTheory/KummerDedekind.lean`):
  `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` — prime factors of
  `(7)·O_L` ↔ irreducible factors of `q mod 7` (our `q_mod7_factor_type`).
- **Ramification/inertia in Galois setting**
  (`Mathlib/NumberTheory/RamificationInertia/Galois.lean`): `inertiaDeg`,
  `Ideal.Quotient.stabilizerHom`, `card_inertia_eq_ramificationIdxIn`.
- **Frobenius elements** (`Mathlib/RingTheory/Frobenius.lean`): `arithFrobAt`,
  `IsArithFrobAt`, `exists_of_isInvariant`, `IsArithFrobAt.restrict`.

The residual work is therefore **instantiation, not a missing theorem**:
(i) the `q.Gal ≃ Gal(L/K)` identification (transport via the existing 0-axiom
`galActionHom` bridge), and (ii) the one genuine arithmetic side-condition —
`7 ∤` the conductor of `ℤ[α]` in `𝓞 L` (Kummer–Dedekind's coprimality
hypothesis). See knowledge.md "Session 2026-07-02" for the full roadmap.

No Lean shipped: (i)+(ii) is a multi-file formalization owned by the sibling
slug `inverse-galois-a5-oq-01` (`exists_gal_order_three`), not a marginal edit
here; and this slug's own deliverables are already complete. Attempting a large
fragile build under a reaped worktree + 100%-full disk risks false theorems for
no verified gain.

## Next Action

**For the sibling `inverse-galois-a5-oq-01`**: discharge `exists_gal_order_three`
by instantiating Kummer–Dedekind + `arithFrobAt` at `p = 7` (α a root, `x := α`,
`minpoly ℤ x = q`, conductor coprime to 7), obtaining a prime `Q | 7` with
`inertiaDeg = 3`, so `3 ∣ orderOf (arithFrobAt Q)`; transport through
`galActionHom` and finish with the already-verified
`InverseGaloisOQ06OQ02GalAction.three_dvd_card_gal_of_orderOf_three`.

For **this** slug: `q_mod7_factor_type` / `q_mod11_factor_type` are the ready
inputs; nothing further to add. Algebraic input complete and symmetric at both
unramified primes (7, 11): irreducible factors + degrees + distinctness +
squarefreeness + factorization identity.
