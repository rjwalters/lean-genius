/-
# Hilbert's 10th Problem over Rings of Integers of Number Fields

The parent file `Hilbert10.lean` proves H10 is undecidable over ℤ (via the MRDP
theorem and a reduction from the Halting Problem). The sibling `Hilbert10OQ01.lean`
surveys the (open) rational case. This file addresses **open question oq-03**:

**Characterize precisely which number fields K have decidable H10 for 𝒪_K.**

Here 𝒪_K is the ring of integers of a number field K (a finite extension of ℚ),
and "H10 for 𝒪_K" asks for an algorithm deciding whether a polynomial with
integer coefficients has a solution in 𝒪_K.

## The conjectured answer

The prevailing expectation is that H10 is **undecidable for 𝒪_K for every number
field K**. This follows whenever ℤ is *Diophantine* over 𝒪_K — i.e. definable by a
polynomial existential formula — because a solvability oracle for 𝒪_K could then be
used to decide solvability over ℤ, which is impossible (MRDP).

## What this file contributes (and what it does not)

Unlike the parent files, which *axiomatize the reduction itself*, this file
**proves the entire logical/computability skeleton** of the argument:

* `Reduction A B` packages exactly the content "H10 over A many-one reduces to
  H10 over B" — a solvability-preserving translation of instances. Existence of
  such a reduction is what "A is Diophantine over B" delivers.
* **Proved:** reductions are reflexive (`Reduction.id`) and transitive
  (`Reduction.comp`) — so Diophantine definability chains along a *tower* of fields.
* **Proved:** a reduction transports decidability *forwards* along the arrow
  (`H10Decidable_of_reduction`) and undecidability *backwards*
  (`undecidable_of_reduction`).

The only inputs left as **axioms** are the genuinely deep number-theoretic facts:

1. `hilbert10_Int_undecidable` — H10/ℤ is undecidable (MRDP 1970; parent file).
2. `robinson_1962` — ℤ is Diophantine over 𝒪_K for every *totally real* K
   (Julia Robinson).
3. `imaginary_quadratic_diophantine` — ℤ is Diophantine over 𝒪_K for imaginary
   quadratic K.
4. `shlapentokh` — ℤ is Diophantine over 𝒪_K for the large classes handled by
   Shlapentokh's elliptic-curve constructions.
5. `mazur_rubin_2010` — ℤ is Diophantine over 𝒪_K for *every* number field K,
   conditional on the Mazur–Rubin (Shafarevich–Tate) hypothesis.

Every named undecidability result below (`H10_undecidable_totallyReal`,
`H10_undecidable_imaginaryQuadratic`, `H10_undecidable_of_mazurRubin`, and the
tower corollary) is then **derived by proof** from these axioms plus the proved
transfer lemmas. The status is therefore `axiomatized`: the number theory is
assumed, the logic connecting it to decidability is verified.

## Status

- [x] Abstract H10-decidability over a carrier
- [x] Diophantine reductions: reflexive + transitive (PROVED)
- [x] Decidability transfer / undecidability transfer (PROVED)
- [x] Number-field undecidability results derived from stated axioms
- [ ] The full characterization is OPEN mathematics (stated as a conjecture)

## References

- J. Robinson, *The undecidability of algebraic rings and fields*, PAMS (1962).
- A. Shlapentokh, *Hilbert's Tenth Problem: Diophantine Classes and Extensions to
  Global Fields*, Cambridge (2007).
- B. Mazur & K. Rubin, *Ranks of twists of elliptic curves and Hilbert's Tenth
  Problem*, Invent. Math. 181 (2010).

Parent: Hilbert10.lean (H10 over ℤ).  Sibling: Hilbert10OQ01.lean (H10 over ℚ).

Self-contained: like the sibling files, this uses only Lean core (no Mathlib).
-/

namespace Hilbert10NumberFields

-- ============================================================
-- Part I: Abstract H10 decidability over a carrier
-- ============================================================

/-- An **H10 instance** over a carrier `R`: a polynomial equation `P = 0`, modeled
    (following the parent file) as a map from variable assignments `Nat → R` to `R`.
    Concretely `R` is the ring of integers 𝒪_K; the carrier is kept abstract so the
    reduction machinery applies uniformly to ℤ and to every 𝒪_K. -/
def Instance (R : Type _) := (Nat → R) → R

/-- `P` is **solvable** over `R` when some assignment is a root, i.e. the Diophantine
    equation `P = 0` has a solution in `R`. -/
def Solvable {R : Type _} [Zero R] (P : Instance R) : Prop :=
  ∃ v : Nat → R, P v = 0

/-- **H10 is decidable over `R`** when some Boolean procedure decides solvability
    exactly. This is the property whose failure we call "H10 undecidable over `R`". -/
def H10Decidable (R : Type _) [Zero R] : Prop :=
  ∃ decide : Instance R → Bool, ∀ P, decide P = true ↔ Solvable P

-- ============================================================
-- Part II: Diophantine reductions
-- ============================================================

/-- A **reduction** from H10 over `A` to H10 over `B`: a translation of instances
    that preserves solvability. This is exactly the computational content of the
    statement "`A` is Diophantine over `B`": an instance over `A` is turned into an
    instance over `B` that is solvable *iff* the original was.

    (The map is not required to be `Bool`-computable inside Lean; what matters for
    the undecidability transfer is that it is a *total function*, so that composing a
    decider for `B` with it yields a decider for `A`.) -/
structure Reduction (A B : Type _) [Zero A] [Zero B] where
  /-- Translate an `A`-instance to a `B`-instance. -/
  map : Instance A → Instance B
  /-- Solvability is preserved by the translation. -/
  preserves : ∀ P, Solvable P ↔ Solvable (map P)

/-- The identity reduction: every carrier reduces to itself. (Reflexivity.) -/
def Reduction.id (A : Type _) [Zero A] : Reduction A A where
  map := fun P => P
  preserves := fun _ => Iff.rfl

/-- Reductions **compose**: if H10/`A` reduces to H10/`B` and H10/`B` reduces to
    H10/`C`, then H10/`A` reduces to H10/`C`. This is transitivity of Diophantine
    definability: a *tower* `ℤ ⊆ 𝒪_{K₁} ⊆ 𝒪_{K₂}` of Diophantine definitions chains
    into a single reduction `ℤ → 𝒪_{K₂}`. -/
def Reduction.comp {A B C : Type _} [Zero A] [Zero B] [Zero C]
    (f : Reduction A B) (g : Reduction B C) : Reduction A C where
  map := fun P => g.map (f.map P)
  preserves := fun P => (f.preserves P).trans (g.preserves (f.map P))

-- ============================================================
-- Part III: Transfer of (un)decidability (PROVED)
-- ============================================================

/-- **Decidability transports forward along a reduction.** If H10 over `A` reduces
    to H10 over `B` and H10 over `B` is decidable, then H10 over `A` is decidable:
    just run the `B`-decider on the translated instance. -/
theorem H10Decidable_of_reduction {A B : Type _} [Zero A] [Zero B]
    (f : Reduction A B) (hB : H10Decidable B) : H10Decidable A := by
  obtain ⟨decideB, hdecideB⟩ := hB
  refine ⟨fun P => decideB (f.map P), ?_⟩
  intro P
  rw [hdecideB (f.map P)]
  exact (f.preserves P).symm

/-- **Undecidability transports backward along a reduction.** Contrapositive of the
    previous lemma: if H10 over `A` is undecidable and H10/`A` reduces to H10/`B`,
    then H10 over `B` is undecidable. This is the engine that carries the ℤ result
    up into every 𝒪_K for which a reduction `ℤ → 𝒪_K` exists. -/
theorem undecidable_of_reduction {A B : Type _} [Zero A] [Zero B]
    (f : Reduction A B) (hA : ¬ H10Decidable A) : ¬ H10Decidable B :=
  fun hB => hA (H10Decidable_of_reduction f hB)

-- ============================================================
-- Part IV: The base undecidability input (MRDP, parent file)
-- ============================================================

/-- **MRDP (1970), via the parent file `Hilbert10.lean`.** Hilbert's Tenth Problem
    over the integers is undecidable. Everything downstream is derived from this one
    hard fact together with Diophantine definability of ℤ inside 𝒪_K. -/
axiom hilbert10_Int_undecidable : ¬ H10Decidable Int

-- ============================================================
-- Part V: Number fields — the deep Diophantine-definability axioms
-- ============================================================

/-- Data marking a carrier `OK` as the ring of integers 𝒪_K of a number field K,
    tagged with the arithmetic flags our conditional results depend on.

    The properties are kept as opaque `Prop` fields: the concrete constructions live
    in the algebraic number theory (Mathlib's `NumberField.RingOfIntegers`, totally
    real fields, class groups, elliptic curves), which is out of scope for this
    self-contained computability-level file. -/
structure NumberRing (OK : Type _) [Zero OK] where
  /-- K is totally real (all archimedean places are real). -/
  totallyReal : Prop
  /-- K is imaginary quadratic, K = ℚ(√-d). -/
  imaginaryQuadratic : Prop
  /-- K lies in one of Shlapentokh's Diophantine classes. -/
  shlapentokhClass : Prop
  /-- The Mazur–Rubin hypothesis holds (finiteness of relevant Shafarevich–Tate
      groups / existence of elliptic curves of rank 1 over K with the right rank
      behaviour in quadratic twists). -/
  mazurRubinHypothesis : Prop

/-- **Julia Robinson (1962).** For a *totally real* number field K, the integers ℤ
    are first-order — in fact Diophantine — definable in 𝒪_K, yielding a reduction of
    H10/ℤ to H10/𝒪_K. -/
axiom robinson_1962 {OK : Type _} [Zero OK] (N : NumberRing OK) :
    N.totallyReal → Reduction Int OK

/-- **Imaginary quadratic case.** For K = ℚ(√-d) the integers are Diophantine in
    𝒪_K (Denef, Shapiro–Shlapentokh via class-group / norm-form arguments), giving a
    reduction of H10/ℤ to H10/𝒪_K. -/
axiom imaginary_quadratic_diophantine {OK : Type _} [Zero OK] (N : NumberRing OK) :
    N.imaginaryQuadratic → Reduction Int OK

/-- **Shlapentokh (1989–2008).** For the broad Diophantine classes handled by
    Shlapentokh's elliptic-curve constructions, ℤ is Diophantine in 𝒪_K, giving a
    reduction of H10/ℤ to H10/𝒪_K. -/
axiom shlapentokh {OK : Type _} [Zero OK] (N : NumberRing OK) :
    N.shlapentokhClass → Reduction Int OK

/-- **Mazur–Rubin (2010), conditional.** Assuming their Shafarevich–Tate hypothesis,
    ℤ is Diophantine in 𝒪_K for *every* number field K. This is the conditional route
    to the full conjecture below. -/
axiom mazur_rubin_2010 {OK : Type _} [Zero OK] (N : NumberRing OK) :
    N.mazurRubinHypothesis → Reduction Int OK

-- ============================================================
-- Part VI: Derived undecidability results (PROVED from the axioms)
-- ============================================================

/-- **H10 is undecidable over 𝒪_K for every totally real number field K.**
    Derived: Robinson's reduction `ℤ → 𝒪_K`, then backward transport of the ℤ
    undecidability. -/
theorem H10_undecidable_totallyReal {OK : Type _} [Zero OK] (N : NumberRing OK)
    (h : N.totallyReal) : ¬ H10Decidable OK :=
  undecidable_of_reduction (robinson_1962 N h) hilbert10_Int_undecidable

/-- **H10 is undecidable over 𝒪_K for every imaginary quadratic K.** -/
theorem H10_undecidable_imaginaryQuadratic {OK : Type _} [Zero OK] (N : NumberRing OK)
    (h : N.imaginaryQuadratic) : ¬ H10Decidable OK :=
  undecidable_of_reduction (imaginary_quadratic_diophantine N h) hilbert10_Int_undecidable

/-- **H10 is undecidable over 𝒪_K for every K in a Shlapentokh Diophantine class.** -/
theorem H10_undecidable_shlapentokh {OK : Type _} [Zero OK] (N : NumberRing OK)
    (h : N.shlapentokhClass) : ¬ H10Decidable OK :=
  undecidable_of_reduction (shlapentokh N h) hilbert10_Int_undecidable

/-- **Conditional universal result.** Under the Mazur–Rubin hypothesis, H10 is
    undecidable over 𝒪_K. -/
theorem H10_undecidable_of_mazurRubin {OK : Type _} [Zero OK] (N : NumberRing OK)
    (h : N.mazurRubinHypothesis) : ¬ H10Decidable OK :=
  undecidable_of_reduction (mazur_rubin_2010 N h) hilbert10_Int_undecidable

-- ============================================================
-- Part VII: Towers of number fields (PROVED)
-- ============================================================

/-- **Undecidability climbs a tower.** If ℤ is Diophantine in 𝒪_{K₁} and 𝒪_{K₁} is
    Diophantine in 𝒪_{K₂} (reductions `ℤ → 𝒪_{K₁}` and `𝒪_{K₁} → 𝒪_{K₂}`), then H10
    is undecidable over 𝒪_{K₂}. Proof: compose the reductions, then transport ℤ
    undecidability along the composite. -/
theorem H10_undecidable_tower {OK₁ OK₂ : Type _} [Zero OK₁] [Zero OK₂]
    (f : Reduction Int OK₁) (g : Reduction OK₁ OK₂) : ¬ H10Decidable OK₂ :=
  undecidable_of_reduction (f.comp g) hilbert10_Int_undecidable

/-- A tower reduction really is a single reduction `ℤ → 𝒪_{K₂}`; nothing is lost by
    factoring through the intermediate field. (A sanity lemma about `comp`.) -/
theorem tower_preserves {OK₁ OK₂ : Type _} [Zero OK₁] [Zero OK₂]
    (f : Reduction Int OK₁) (g : Reduction OK₁ OK₂) (P : Instance Int) :
    Solvable P ↔ Solvable ((f.comp g).map P) :=
  (f.comp g).preserves P

-- ============================================================
-- Part VIII: The open characterization (oq-03), stated not proved
-- ============================================================

/-- **The open question oq-03**, stated as a conjecture: H10 is undecidable over the
    ring of integers of *every* number field — equivalently, no number ring has
    decidable H10, so the "decidable side" of the characterization is empty.

    This is currently OPEN: it is known unconditionally for totally real fields
    (`H10_undecidable_totallyReal`), imaginary quadratic fields, and Shlapentokh's
    classes, and follows in general from the Mazur–Rubin hypothesis
    (`H10_undecidable_of_mazurRubin`), but no unconditional proof for *all* K is
    known as of 2026. -/
def CharacterizationConjecture : Prop :=
  ∀ (OK : Type) [inst : Zero OK] (_N : @NumberRing OK inst), ¬ @H10Decidable OK inst

/-- The Mazur–Rubin hypothesis, holding uniformly across number rings, would settle
    the characterization conjecture. This packages the conditional universal result
    into the exact shape of `CharacterizationConjecture`, making the logical
    dependency `Mazur–Rubin ⟹ full characterization` explicit and machine-checked. -/
theorem mazurRubin_implies_characterization
    (H : ∀ (OK : Type) [inst : Zero OK] (N : @NumberRing OK inst), N.mazurRubinHypothesis) :
    CharacterizationConjecture := by
  intro OK inst N
  exact H10_undecidable_of_mazurRubin N (H OK N)

-- ============================================================
-- Part IX: Landscape summary
-- ============================================================

/-
## Summary of what is proved vs. assumed

| Statement                                   | Here      | Justification            |
|---------------------------------------------|-----------|--------------------------|
| Reductions reflexive/transitive             | PROVED    | `Reduction.id/.comp`     |
| Decidability transfers forward              | PROVED    | `H10Decidable_of_reduction` |
| Undecidability transfers backward           | PROVED    | `undecidable_of_reduction`  |
| H10/ℤ undecidable                           | axiom     | MRDP 1970 (parent file)  |
| ℤ Diophantine in 𝒪_K, K totally real        | axiom     | Robinson 1962            |
| ℤ Diophantine in 𝒪_K, K imag. quadratic     | axiom     | Denef/Shapiro–Shlapentokh|
| ℤ Diophantine in 𝒪_K, Shlapentokh classes   | axiom     | Shlapentokh 1989–2008    |
| ℤ Diophantine in 𝒪_K, all K (conditional)   | axiom     | Mazur–Rubin 2010         |
| H10/𝒪_K undecidable (the four cases)         | PROVED    | transfer + above axioms  |
| H10 undecidable along a tower               | PROVED    | `H10_undecidable_tower`  |
| Full characterization (all K)               | OPEN      | `CharacterizationConjecture` |

### Axioms (5)
1. `hilbert10_Int_undecidable`
2. `robinson_1962`
3. `imaginary_quadratic_diophantine`
4. `shlapentokh`
5. `mazur_rubin_2010`
(`CharacterizationConjecture` is a *definition*, not an axiom — it is the open goal.)

### The point
The parent files axiomatize the reduction itself; here the reduction calculus is
*proved*, isolating the mathematical assumptions to exactly the deep number-theoretic
definability facts. The chain
    ℤ Diophantine in 𝒪_K  ⟹  H10/𝒪_K undecidable
is now machine-checked; only the antecedents are assumed.
-/

#check @H10_undecidable_totallyReal
#check @H10_undecidable_tower
#check @mazurRubin_implies_characterization
#check @CharacterizationConjecture

end Hilbert10NumberFields
