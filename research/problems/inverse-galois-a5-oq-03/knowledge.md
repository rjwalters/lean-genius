# Knowledge Base: inverse-galois-a5-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

Goal: formalize the "easy half" of the Inverse Galois Problem — every symmetric
group `Sₙ` and alternating group `Aₙ` is a Galois group over `ℚ` — via the classical
Hilbert route (generic polynomial realizing `Sₙ`/`Aₙ` over `ℚ(t)`, then specialize
preserving the group by Hilbert's Irreducibility Theorem). Difficulty: HIGH —
HIT and function-field generic-polynomial Galois computations are absent from Mathlib.

---

## Insights

### Session 2026-06-19 (Session 1) — FRESH, interface-first (Approach A)

**Mode**: FRESH. **Outcome**: progress (staged `axiomatized` entry, builds, 0 sorries).

**Mathlib survey (confirmed gaps):**
- `Polynomial.Gal`, `Polynomial.Gal.galActionHom : p.Gal →* Equiv.Perm (rootSet p E)`,
  `galActionHom_injective` — present.
- `alternatingGroup`, `Equiv.Perm.sign`, `mem_alternatingGroup`, `alternatingGroup.index_eq_two`,
  `two_mul_card_alternatingGroup`, `card_alternatingGroup`, `eq_alternatingGroup_of_index_eq_two`,
  `alternatingGroup.normal` (instance) — present.
- **Fundamental theorem of Galois theory (finite), quotient form**: `IsGalois.normalAutEquivQuotient`
  (`Mathlib/FieldTheory/Galois/Basic.lean:432`): for normal `H ≤ Gal(L/K)`,
  `Gal(L/K) ⧸ H ≃* Gal(fixedField H / K)`, plus the instance
  `IsGalois.of_fixedField_normal_subgroup` giving `IsGalois K (fixedField H)`. **PRESENT and usable.**
- `Polynomial.discr` present (`RingTheory/Polynomial/Resultant/Basic.lean:937`), but the
  **"disc is a square ↔ Gal ⊆ Aₙ" correspondence at the `Polynomial.Gal` level is a Mathlib gap.**
- **Hilbert Irreducibility Theorem: entirely absent.** No `RatFunc` Galois-specialization,
  no thin sets. (`RatFunc ℚ` exists; no specialization API.)

**Key mathematical insight (the reason for two axioms):**
`Aₙ ◁ Sₙ` is a *normal* subgroup with quotient `Sₙ ⧸ Aₙ ≅ ℤ/2`. By the Galois
correspondence, an `Sₙ`-realization `K/ℚ` realizes the *quotient* `ℤ/2` over `ℚ`, and
realizes `Aₙ` only over the quadratic subfield `K^{Aₙ}` — **not over `ℚ`**. So
`Aₙ`-over-`ℚ` does NOT follow from `Sₙ`-over-`ℚ`; it requires the discriminant of the
specialized polynomial to be a square (the separate square-disc family). This is
encoded honestly as a separate axiom, and the contrast is *proved* via
`RealizableOverRat.quotient`.

**Built (genuine, machine-checked):**
- `RealizableOverRat G` — predicate "G is a Galois group over ℚ" (mirrors parent `a5_realizable_iso`).
- `RealizableOverRat.congr` — invariance under group isomorphism.
- `RealizableOverRat.quotient` — **realizability closed under normal quotients**, via
  `IsGalois.normalAutEquivQuotient` + `QuotientGroup.congr` + `Subgroup.Normal.map`.
- `le_alternatingGroup_iff_forall_sign` — abstract square-disc criterion at permutation level.
- `card_symmetricGroup` (|Sₙ| = n!), `card_alternatingGroup_fin` (2|Aₙ| = n!).
- `quotient_Sn_An_realizableOverRat` — ℤ/2 ≅ Sₙ/Aₙ realizable, DERIVED from the Sₙ axiom
  via the quotient theorem (consistency / non-vacuity witness).

**Axiomatized (deep analytic core, 2 axioms):**
- `symmetricGroup_realizableOverRat` — generic Sₙ family + HIT.
- `alternatingGroup_realizableOverRat` — generic Aₙ family (square-disc twist) + HIT.

---

## Dead Ends

- Deriving `Aₙ`-over-`ℚ` from `Sₙ`-over-`ℚ` by the Galois correspondence: FAILS —
  `Aₙ` is a normal subgroup of `Sₙ`, so the correspondence yields the quotient `ℤ/2`
  over `ℚ` and `Aₙ` only over the fixed quadratic subfield, not over `ℚ`. Hence two
  separate assumptions are genuinely required.

---

## Next Steps

1. **Discharge `symmetricGroup_realizableOverRat`**: formalize that the roots of the
   generic polynomial are algebraically independent and `Sₙ` acts as the full Galois
   group over `ℚ(t₁,…,tₙ)`. Mathlib has symmetric-function and `MvPolynomial` machinery;
   the function-field Galois computation is the heavy part.
2. **Formalize the square-disc ↔ Aₙ criterion at the `Polynomial.Gal` level** (currently
   a Mathlib gap), connecting `Polynomial.discr` to `galActionHom`'s image and `sign`.
   This is a self-contained, reusable contribution (~300–500 lines) usable by the parent
   A₅ entry and oq-02 as well.
3. **State a restricted single-variable HIT** (`f(t,X) ∈ ℚ(t)[X]` irreducible ⟹ infinitely
   many `t₀` keep it irreducible) as an interface, then attempt the elementary
   (Mertens/sieve or thin-set) proof for the degree bounds needed. This is the genuine
   long-term target replacing the HIT half of the two axioms.
