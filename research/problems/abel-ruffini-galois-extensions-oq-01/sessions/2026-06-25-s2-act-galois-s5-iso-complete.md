# S2 ACT — explicit `Gal(X⁵−4X+2) ≃* S₅` constructed; OQ-01 COMPLETE (0 sorry / 0 axiom)

**Date:** 2026-06-25 (UTC)
**Agent:** researcher-9
**Phase:** S2 ACT → COMPLETE
**Status:** verified, gallery entry authored, PR opened

## Headline

Executed the ACT plan from S1 (researcher-12, 2026-05-13) verbatim. New file
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ01.lean` (272 lines, 0 sorry, 0 axiom)
constructs the explicit isomorphism

    galEquivS5 : (X⁵ − 4X + 2).Gal ≃* Equiv.Perm (Fin 5)

— the headline OQ-01 success criterion — and reads off `gal_card` (= 120),
`gal_not_solvable`, the UNCONDITIONAL `root_not_solvableByRad`, and
`exists_root_not_solvableByRad`.

## What was done

1. **Reproduced** T. Browning's `Archive/Wiedijk100Theorems/AbelRuffini.lean`
   development for `Φ R a b = X⁵ − a·X + b` (Archive is a separate `lean_lib`
   target, NOT importable from a downstream Mathlib client and its oleans are not
   shipped — confirmed `find .lake … Archive*AbelRuffini*` empty). Lemmas copied
   with attribution: coeff/degree/monic, `irreducible_Phi` (Eisenstein),
   `real_roots_Phi_le` (≤3), `real_roots_Phi_ge` (≥2), `complex_roots_Phi` (=5),
   `gal_Phi` (`Bijective (galActionHom (Φ ℚ a b) ℂ)`).
2. **New bridge (the OQ-01 content):**
   - `permCongrMulEquiv` — promotes `Equiv.permCongr` (a bare `Equiv`) to a
     `MulEquiv` of permutation groups (map_mul' by `ext`+`simp`).
   - `galEquivS5 := (MulEquiv.ofBijective (galActionHom q ℂ) q_galActionHom_bijective).trans
       (permCongrMulEquiv (Fintype.equivFinOfCardEq q_card_complex_roots))`.
   - `gal_card`, `gal_not_solvable`, `root_not_solvableByRad`,
     `exists_root_not_solvableByRad`.
3. **Re-attributed** `attribute [local instance] splits_ℚ_ℂ` (S1's load-bearing note).

## Verification

- `lake env lean Proofs/AbelRuffiniGaloisExtensionsOQ01.lean` → exit 0 (host toolchain,
  cached mathlib oleans; Docker build path not needed for single-file type-check).
- `#print axioms` on all five headline results → only `propext`, `Classical.choice`,
  `Quot.sound`. No `sorryAx`, no `Lean.ofReduceBool`. ⇒ `status: verified`, 0-axiom.

## Why this is stronger than the X⁵−X−1 sibling (OQ-07)

`AbelRuffiniOQ07NotSolvable` uses Selmer's `X⁵ − X − 1`, which has FOUR non-real
roots → complex conjugation is a double transposition → the prime-degree
transposition route does not pin Gal to S₅, so that entry only ASSUMES
`Gal ≃* S₅` (needs the unformalized Dedekind–Frobenius bridge). `X⁵ − 4X + 2` has
exactly TWO non-real roots, so `galActionHom_bijective_of_prime_degree'` applies
and the iso is CONSTRUCTED. This entry's Abel–Ruffini conclusion is therefore
unconditional.

## Artifacts

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ01.lean` (+ import in `Proofs.lean`)
- `src/data/proofs/abel-ruffini-galois-extensions-oq-01/{meta.json,annotations.json}`
- PR: (see branch `research/abel-ruffini-galois-extensions-oq-01`)
