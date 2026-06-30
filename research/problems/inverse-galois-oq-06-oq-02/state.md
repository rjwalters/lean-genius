# Research State: inverse-galois-oq-06-oq-02

## Current State

**Phase**: BLOCKED (this slug's contribution complete; remaining gap is sibling-owned Dedekind theorem, a Mathlib gap)
**Path**: full
**Since**: 2026-06-27
**Iteration**: 1

## Iteration 4 (researcher-1, 2026-06-30) — BLOCKED assessment, no edit

Re-audited the full OQ06OQ02 cluster (7 files). **Every component this slug owns is
complete and 0-axiom / 0-sorry**:
- algebraic Dedekind *input* at two independent unramified primes — `q_mod7_factor_type`
  (`InverseGaloisOQ06OQ02.lean`) and `q_mod11_factor_type` (`...P11.lean`), each carrying
  the full `(1,1,3)` distinct-irreducibles + squarefree + factorization-identity package;
- the *deterministic half* of the bridge — `InverseGaloisOQ06OQ02Cycle.lean` (abstract
  cycle-type ⟹ `3 ∣ |H|`), `...GalAction.lean` / `...GalBridge.lean` (transport to the
  genuine `q.Gal` action: order-3 / 3-cycle Galois element ⟹ `3 ∣ |q.Gal|`), and
  `...GapChar.lean` (`three_dvd_gal_card ↔ |q.Gal| = 60`, the axiom has no slack).

The **only** remaining gap is part (A) of the bridge — *Frobenius ↔ factorization*, i.e.
Dedekind's theorem that the verified `(1,1,3)` factor type at `7` (or `11`) yields a
Galois element that is a genuine 3-cycle. That is a Mathlib 4.26 gap (the number-field
Frobenius / cycle-type theory is absent) and is owned by the sibling track
`inverse-galois-a5-oq-01` (`InverseGaloisA5Dedekind.exists_gal_order_three`). It needs
>1000 lines of foundational ring-of-integers/decomposition-group machinery — out of scope
for an incremental session, and adding a third unramified-prime witness (p=13, …) would be
pure scaffolding inflation with no new information beyond the existing 7/11 pair.

**Flagging BLOCKED** so depth-first re-claims skip this dead end until the sibling Dedekind
bridge lands. Released without edit.

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

## Next Action

If Dedekind's theorem lands in Mathlib (or the sibling Frobenius bridge
completes), `q_mod7_factor_type` / `q_mod11_factor_type` plug in directly to
discharge the axiom. The algebraic input is now complete and symmetric at both
unramified primes (7, 11): irreducible factors + degrees + distinctness +
squarefreeness + factorization identity.
