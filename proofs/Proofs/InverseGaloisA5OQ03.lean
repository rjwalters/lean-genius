import Mathlib

/-
# The "easy half" of the Inverse Galois Problem: Sₙ and Aₙ over ℚ via Hilbert Irreducibility (Inverse-Galois A₅, OQ-03)

## The open question

The gallery's `inverse-galois-a5` realizes a *single* non-solvable group, `A₅`, as a
Galois group over `ℚ` by exhibiting an explicit quintic. The systematic route to
realizing *every* symmetric group `Sₙ` and alternating group `Aₙ` over `ℚ` (the
classical "easy half" of the Inverse Galois Problem, due to Hilbert) is:

1. Write down the generic degree-`n` polynomial
   `f_n(t₁,…,tₙ, X) = Xⁿ − t₁Xⁿ⁻¹ + ⋯ ± tₙ`, whose Galois group over the rational
   function field `ℚ(t₁,…,tₙ)` is provably the full symmetric group `Sₙ`
   (its roots are algebraically independent; `Sₙ` permutes them).
2. Adjoin `√(disc f_n)` to pass to a family with Galois group the alternating
   group `Aₙ` over `ℚ(t)`.
3. **Specialize** the parameters to rational values `t₀ ∈ ℚ` while *preserving* the
   Galois group. Hilbert's Irreducibility Theorem (HIT) guarantees that "most"
   specializations preserve the group — in fact infinitely many do.

## What this file proves vs. axiomatizes

This is a **staged `axiomatized` entry**, mirroring the sibling `InverseGaloisA5OQ02.lean`
(PSL(2,7)) template. The deep analytic core — the generic-polynomial Galois
computation over a function field *and* Hilbert's Irreducibility Theorem — is
genuinely multi-week work and is **entirely absent from Mathlib** (confirmed:
no `RatFunc` Galois-specialization API, no thin-set / HIT statement). It is stated
here as the **two explicit assumptions** below, with everything else proved.

**Proved here (genuine, build-checked — the session's mathematical content):**

* `RealizableOverRat` — a clean predicate "the finite group `G` occurs as `Gal(K/ℚ)`
  for some finite Galois extension `K/ℚ`", reusable across inverse-Galois entries.
* `RealizableOverRat.congr` — realizability is transported along group isomorphisms.
* `RealizableOverRat.quotient` — **realizability is closed under quotients by normal
  subgroups.** This is a genuine corollary of Mathlib's *fundamental theorem of
  Galois theory* (`IsGalois.normalAutEquivQuotient`): the fixed field of a normal
  subgroup is itself Galois over `ℚ`, with Galois group the quotient. It is the
  rigorous reason the `Aₙ` case below needs a *separate* assumption from the `Sₙ`
  case (see the docstring on `alternatingGroup_realizableOverRat`).
* `le_alternatingGroup_iff_forall_sign` — the abstract "square-discriminant criterion"
  at the permutation level: a subgroup of `Sₙ` lies in `Aₙ` iff every element is an
  even permutation. (This is the permutation-group shadow of `disc` being a square;
  the `Polynomial.Gal`-level version is itself a Mathlib gap.)
* `card_symmetricGroup`, `card_alternatingGroup_fin` — the orders `|Sₙ| = n!` and
  `2·|Aₙ| = n!`.
* `quotient_Sn_An_realizableOverRat` — a derived consistency result: the order-2
  group `Sₙ ⧸ Aₙ` is realizable over `ℚ`, obtained from the `Sₙ` assumption *via the
  proved quotient theorem* (not a fresh assumption), demonstrating the interface is
  non-vacuous and compatible with Mathlib's FTGT.

**Axiomatized (the deep analytic certificate — exactly two assumptions):**

* `symmetricGroup_realizableOverRat` — generic `Sₙ` family + HIT.
* `alternatingGroup_realizableOverRat` — generic `Aₙ` family (square-disc twist) + HIT.

## Honesty note

The headline theorems `symmetricGroup_isGaloisGroup` / `alternatingGroup_isGaloisGroup`
("every `Sₙ`, `Aₙ` is a Galois group over `ℚ`") are *restatements of the assumptions*:
their entire mathematical weight lives in the two axioms, which encapsulate genuinely
hard, currently-unformalized mathematics. The proved content above is the surrounding
framework (the realizability calculus and the quotient theorem), not the easy-half
theorem itself. This entry is therefore `axiomatized`, not `verified`.
-/

open Equiv Equiv.Perm

namespace InverseGaloisA5OQ03

/-! ## The realizability predicate -/

/-- `RealizableOverRat G` : the finite group `G` occurs as the Galois group
`Gal(K/ℚ)` of some finite Galois extension `K/ℚ`. This is the standard
"is a Galois group over `ℚ`" predicate; it mirrors the conclusion shape of the
parent `inverse-galois-a5` entry (`a5_realizable_iso`). -/
def RealizableOverRat (G : Type) [Group G] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : FiniteDimensional ℚ K)
    (_ : IsGalois ℚ K), Nonempty (G ≃* (K ≃ₐ[ℚ] K))

/-- Realizability is invariant under group isomorphism. -/
theorem RealizableOverRat.congr {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (h : RealizableOverRat G) : RealizableOverRat H := by
  obtain ⟨K, fK, aK, fdK, gK, ⟨φ⟩⟩ := h
  exact ⟨K, fK, aK, fdK, gK, ⟨e.symm.trans φ⟩⟩

/-- Field-level core of `RealizableOverRat.quotient`, stated with genuine
instance-implicit binders on `K` (so the fundamental-theorem instances synthesize
cleanly — destructured existential witnesses do not register as local instances). -/
private theorem realizable_quotient_aux {K : Type} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K] {G : Type} [Group G]
    (φ : G ≃* (K ≃ₐ[ℚ] K)) (N : Subgroup G) [N.Normal] :
    RealizableOverRat (G ⧸ N) := by
  -- Transport `N` to a normal subgroup `H` of `Gal(K/ℚ)`.
  let H : Subgroup (K ≃ₐ[ℚ] K) := N.map (φ : G →* (K ≃ₐ[ℚ] K))
  haveI hHnormal : H.Normal :=
    Subgroup.Normal.map inferInstance (φ : G →* (K ≃ₐ[ℚ] K)) φ.surjective
  -- The fixed field of `H` is Galois over `ℚ` (fundamental theorem of Galois theory),
  -- finite-dimensional as an intermediate field of `K/ℚ`, with `Gal(K/ℚ) ⧸ H ≅
  -- Gal(fixedField H / ℚ)` and `G ⧸ N ≅ Gal(K/ℚ) ⧸ H`.
  -- The `Algebra ℚ` instance is supplied as the intermediate field's own `algebra'`
  -- (not the generic `DivisionRing.toRatAlgebra`) so that all the fundamental-theorem
  -- terms below cohere with it, avoiding the ℚ-algebra instance diamond.
  exact ⟨IntermediateField.fixedField H, inferInstance,
    (IntermediateField.fixedField H).algebra',
    IntermediateField.finiteDimensional_left (F := IntermediateField.fixedField H),
    IsGalois.of_fixedField_normal_subgroup H,
    ⟨(QuotientGroup.congr N H φ rfl).trans (IsGalois.normalAutEquivQuotient H)⟩⟩

/-- **Realizability is closed under quotients by normal subgroups.**
If `G` is a Galois group over `ℚ` and `N ◁ G`, then `G ⧸ N` is also a Galois
group over `ℚ`. This is a direct consequence of the fundamental theorem of Galois
theory: the field fixed by (the image of) `N` is Galois over `ℚ`, with Galois group
the quotient (`IsGalois.normalAutEquivQuotient`). -/
theorem RealizableOverRat.quotient {G : Type} [Group G]
    (h : RealizableOverRat G) (N : Subgroup G) [N.Normal] :
    RealizableOverRat (G ⧸ N) := by
  obtain ⟨K, fK, aK, fdK, gK, ⟨φ⟩⟩ := h
  exact @realizable_quotient_aux K fK aK fdK gK G _ φ N _

/-! ## The abstract square-discriminant (sign) criterion -/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The abstract "square-discriminant criterion" at the permutation level:
a subgroup `G ≤ Sₙ` is contained in the alternating group `Aₙ` iff every element of
`G` is an even permutation. For a Galois group acting on the roots of a polynomial
`f`, the left side is `Gal(f) ⊆ Aₙ` and the right side holds exactly when `disc f`
is a square — this is the group-theoretic heart of the `Aₙ` realization. -/
theorem le_alternatingGroup_iff_forall_sign (G : Subgroup (Perm α)) :
    G ≤ alternatingGroup α ↔ ∀ σ ∈ G, Equiv.Perm.sign σ = 1 := by
  constructor
  · intro h σ hσ
    exact Equiv.Perm.mem_alternatingGroup.mp (h hσ)
  · intro h σ hσ
    exact Equiv.Perm.mem_alternatingGroup.mpr (h σ hσ)

/-! ## Orders of the symmetric and alternating groups -/

/-- `|Sₙ| = n!`. -/
theorem card_symmetricGroup (n : ℕ) :
    Fintype.card (Perm (Fin n)) = n.factorial := by
  rw [Fintype.card_perm, Fintype.card_fin]

/-- `2·|Aₙ| = n!` for `n ≥ 2` (so `|Aₙ| = n!/2`). -/
theorem card_alternatingGroup_fin (n : ℕ) [Nontrivial (Fin n)] :
    2 * Fintype.card (alternatingGroup (Fin n)) = n.factorial := by
  rw [two_mul_card_alternatingGroup, Fintype.card_perm, Fintype.card_fin]

/-! ## The two assumptions (generic family + Hilbert Irreducibility) -/

/-- **Generic `Sₙ` family + Hilbert Irreducibility** (assumption).

For every `n`, the generic degree-`n` polynomial realizes the symmetric group
`Sₙ = Perm (Fin n)` over the rational function field `ℚ(t₁,…,tₙ)` (its roots are
algebraically independent), and Hilbert's Irreducibility Theorem supplies infinitely
many rational specializations preserving the Galois group; hence `Sₙ` is realizable
over `ℚ`. Both ingredients — the generic-polynomial Galois computation over a
function field and HIT itself — are currently absent from Mathlib and are bundled
here as a single assumption. -/
axiom symmetricGroup_realizableOverRat (n : ℕ) :
    RealizableOverRat (Perm (Fin n))

/-- **Generic `Aₙ` family + Hilbert Irreducibility** (assumption).

Adjoining `√(disc f_n)` to the generic family produces a degree-`n` family whose
Galois group over `ℚ(t)` is the alternating group `Aₙ`; HIT then yields infinitely
many ℚ-specializations realizing `Aₙ` over `ℚ`.

This is a **genuinely separate** assumption from the `Sₙ` case, and not derivable
from it: `Aₙ ◁ Sₙ` is a *normal* subgroup with quotient `Sₙ ⧸ Aₙ ≅ ℤ/2`. By the
Galois correspondence (see `RealizableOverRat.quotient`), an `Sₙ`-realization
`K/ℚ` realizes the *quotient* `ℤ/2` over `ℚ` and realizes `Aₙ` only over the
quadratic subfield `K^{Aₙ}` fixed by `Aₙ` — not over `ℚ` itself. Pulling `Aₙ` down
to `ℚ` requires the discriminant of the specialized polynomial to be a square, which
is precisely the separate square-disc family above. -/
axiom alternatingGroup_realizableOverRat (n : ℕ) :
    RealizableOverRat (alternatingGroup (Fin n))

/-! ## The easy half of the Inverse Galois Problem -/

/-- **Easy half of IGP (symmetric groups).** Every symmetric group `Sₙ` is a Galois
group over `ℚ`. (Weight carried by `symmetricGroup_realizableOverRat`.) -/
theorem symmetricGroup_isGaloisGroup (n : ℕ) :
    RealizableOverRat (Perm (Fin n)) :=
  symmetricGroup_realizableOverRat n

/-- **Easy half of IGP (alternating groups).** Every alternating group `Aₙ` is a
Galois group over `ℚ`. (Weight carried by `alternatingGroup_realizableOverRat`.) -/
theorem alternatingGroup_isGaloisGroup (n : ℕ) :
    RealizableOverRat (alternatingGroup (Fin n)) :=
  alternatingGroup_realizableOverRat n

/-- **Derived consistency result.** The order-2 quotient `Sₙ ⧸ Aₙ` is realizable
over `ℚ` — obtained from the `Sₙ` assumption *through the proved quotient theorem*
`RealizableOverRat.quotient`, not as a fresh assumption. This witnesses that the
realizability framework is non-vacuous and meshes with Mathlib's fundamental theorem
of Galois theory. -/
theorem quotient_Sn_An_realizableOverRat (n : ℕ) :
    RealizableOverRat (Perm (Fin n) ⧸ alternatingGroup (Fin n)) :=
  (symmetricGroup_realizableOverRat n).quotient (alternatingGroup (Fin n))

end InverseGaloisA5OQ03
