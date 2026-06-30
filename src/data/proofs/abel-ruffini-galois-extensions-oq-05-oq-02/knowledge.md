# abel-ruffini-galois-extensions-oq-05-oq-02 — The Artin Realizability Direction

## Problem

Claimed pool entry `abel-ruffini-galois-extensions-oq-05` ("Can Shafarevich's
theorem be stated in Lean as a companion?", tier B, significance 7,
tractability 5). That parent problem was found **already complete**: the gallery
entry `abel-ruffini-galois-extensions-oq-05` exists with Shafarevich recorded as
an axiom (`shafarevich_inverse_galois`, axiomCount 1) and seven corollaries
derived from it. Rather than duplicate it, this entry adds the genuinely missing
piece: the **axiom-free** half of the inverse Galois story.

## What was found in the gallery (state at 2026-06-25)

- `abel-ruffini-galois-extensions-oq-05` — Shafarevich axiomatized (class field
  theory / Brauer groups not in Mathlib). Corollaries (cyclic, abelian, S₃, S₄,
  subgroup/quotient closure, S₅ obstruction) all depend on the axiom.
- `abel-ruffini-galois-extensions-oq-05-oq-01` — cyclic realizability, also
  axiomatized (adds `galois_compositum_product`).
- **No** entry in the abel-ruffini-galois family proves any realizability result
  with 0 axioms. Every realizability statement reduces to the Shafarevich axiom.
- Mathlib **does** have the full Artin fixed-field theorem
  (`Mathlib/FieldTheory/Fixed.lean`, `Mathlib/FieldTheory/Galois/Basic.lean`):
  `IsGalois.of_fixed_field`, `FixedPoints.toAlgAutMulEquiv`,
  `FixedPoints.finrank_eq_card`. This is the elementary, ℚ-free direction of the
  inverse Galois problem and was not packaged anywhere in the gallery.

## Contribution (this entry)

New file `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ02.lean`, namespace
`AbelRuffiniArtinRealizability`, imports `Mathlib`. 4 theorems, 1 def, 97 lines,
0 axioms / 0 sorries (verified via `#print axioms` → only
`propext, Classical.choice, Quot.sound`).

- `extension_isGalois` — for any finite group `G` with `MulSemiringAction G F`
  (F a field), `IsGalois (FixedPoints.subfield G F) F`. No faithfulness needed
  (`IsGalois.of_fixed_field`).
- `galoisGroupEquiv` — for a FAITHFUL finite action,
  `G ≃* (F ≃ₐ[FixedPoints.subfield G F] F)` (`FixedPoints.toAlgAutMulEquiv`):
  G is exactly the Galois group of F over its fixed field.
- `degree_eq_card` — `[F : F^G] = |G|` (`FixedPoints.finrank_eq_card`).
- `artin_realizability` — the three bundled for a faithful finite action.
- `realizable_over_some_subfield` — existence form: G is `Gal(F/k)` for some
  subfield `k ⊆ F` with `[F:k] = |G|` — the inverse-Galois shape over an
  auxiliary base field.

**Framing / why it matters**: realizability of finite groups as Galois groups is
unconditional and elementary over an auxiliary base field (the fixed field of a
faithful action); via Cayley `G ↪ Sym(G)` acting on `K(x_g : g ∈ G)` every finite
group is a Galois group over *some* field. The entire depth of Shafarevich and
the open inverse Galois problem is the constraint **base = ℚ**. This entry is the
verified mirror of the parent's axiom, drawing that line precisely.

**Honesty**: the realization theorems take a finite group already equipped with a
faithful field action (the hypothesis Mathlib's Artin theorem consumes). The
fully unconditional "every finite group is a Galois group over some field" also
needs the Cayley/permutation faithful-action construction, which is described in
the docstring but not formalized (Mathlib lacks a ready `MulSemiringAction` of a
group on `MvPolynomial`/its fraction field from an action on the index set).
Badge is `verified`, not `original`: the deep input is Mathlib's Artin theorem;
the contribution is the realizability packaging and the Shafarevich contrast.

## Verification notes / gotchas

- **Docker daemon down** host-wide (2026-06-25). Verified single-file with
  `proofs/bin/lake env lean` after `lake exe cache unpack` populated the olean
  cache. Olean umbrella is at
  `.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean` (note the extra
  `lean/` dir vs older layouts). Ran from the MAIN repo `proofs/` dir (the
  worktree `.lake` lacks the mathlib build). `#print axioms` on all five
  declarations returned only `propext, Classical.choice, Quot.sound`.
- Key Mathlib names: `IsGalois.of_fixed_field` is an *instance* (so
  `extension_isGalois := inferInstance`); `FixedPoints.toAlgAutMulEquiv` needs
  `[Finite G] [FaithfulSMul G F]`; `FixedPoints.finrank_eq_card` needs
  `[Fintype G] [FaithfulSMul G F]`. `FixedPoints.subfield G F : Subfield F`.
- Branch was created fresh off `origin/main` (the inherited
  `research/ivt-...` branch was stale — its IVT work was already merged to main
  independently, so `gh pr create` there failed "no commits between").

## Next open question

Formalize the universal corollary: construct the faithful `MulSemiringAction` of
a finite group `G` on the rational function field `K(x_g : g ∈ G)` (via Cayley
`G ↪ Sym(G)` + the variable-permutation action of `Sym(G)` on `MvPolynomial`
extended to the fraction field), then apply `realizable_over_some_subfield` to
get the unconditional "every finite group is a Galois group over some field".
Separately, replace the auxiliary base `F^G` by ℚ for cyclic/abelian groups via
cyclotomic fields + Kronecker–Weber, discharging those parent corollaries without
the Shafarevich axiom.
