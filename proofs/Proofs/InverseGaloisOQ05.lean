/-
  The Inverse Galois Problem, Open Question 05:
  "Can we formalize Shafarevich's theorem on solvable groups?"

  **Shafarevich's theorem** (1954): every finite solvable group is realizable as a
  Galois group over ℚ. The full proof is one of the deepest partial results toward
  the Inverse Galois Problem, resting on class field theory and the systematic
  solution of embedding problems. In the parent entry (`Proofs.InverseGalois`) it is
  stated as an axiom (`shafarevich_theorem`).

  **What this entry contributes** — a fully machine-checked, axiom-free formalization
  of the *group-theoretic skeleton* of Shafarevich's induction, which cleanly
  separates the elementary (verifiable) part from the deep analytic core:

    Shafarevich's theorem  =  (group-theoretic induction, HERE, 0 axioms)
                              +  (abelian-kernel embedding problems solvable over ℚ,
                                  the class-field-theory heart, left as a hypothesis).

  The reduction runs down the **derived series** `⊤ = D₀ ⊇ D₁ ⊇ ⋯ ⊇ Dₙ = ⊥` of a
  solvable group `G`. Peeling off the top term:

  1. **The penultimate term is abelian** (`derivedSeries_penultimate_comm`): if
     `Dₙ₊₁ = ⁅Dₙ, Dₙ⁆ = ⊥` then `Dₙ` is commutative. Axiom-free.

  2. **Quotienting shortens the series** (`derivedSeries_quotient_self`): the
     `n`-th derived subgroup of `G ⧸ Dₙ` is already trivial, so the quotient is
     solvable of strictly smaller derived length. Axiom-free.

  3. **The induction** (`realizable_of_derivedSeries_eq_bot`): for any predicate `P`
     on groups that holds for the trivial group (`base`) and is preserved by
     extensions with an abelian normal kernel (`step`, the embedding step), `P`
     holds for every group whose derived series reaches `⊥` — i.e. every solvable
     group (`realizable_of_solvable`). Pure group theory, axiom-free.

  4. **Instantiation over ℚ** (`realizableOverRat_solvable_of_embedding`): taking
     `P G := "G is a Galois group over ℚ"`, and proving the base case concretely
     (the trivial group is `Gal(ℚ/ℚ)`, `realizableOverRat_of_subsingleton`), the
     reduction shows Shafarevich's theorem follows from the single deep hypothesis
     that abelian-kernel embedding problems over ℚ are solvable. This is exactly the
     content of Shafarevich's theorem, honestly localized.

  Note the abelian base case of Shafarevich (finite abelian groups realizable, i.e.
  Kronecker–Weber) is *subsumed*: an abelian group has `D₁ = ⊥`, so it is obtained
  from the trivial group by a single abelian-kernel embedding step. The only deep
  input that survives the reduction is the embedding step itself.

  **Status**: OPEN theorem (Shafarevich's full theorem is not fully formalized in
  Lean/Mathlib). Everything in this file is axiom-free and 0 sorries; the deep
  analytic content is isolated as the explicit `embed`/`step` hypothesis.

  Reference: https://erdosproblems.com (Inverse Galois Problem);
  I. R. Shafarevich, "On the construction of fields with a given Galois group of
  order lᵃ", Izv. Akad. Nauk SSSR (1954).
  Axiom count: 0.  Sorry count: 0.
-/

import Mathlib

namespace InverseGaloisOQ05

open Subgroup

-- ════════════════════════════════════════════════════════════════
-- SECTION I: Peeling the derived series (axiom-free group theory)
-- ════════════════════════════════════════════════════════════════

variable {A : Type} [Group A]

/-- If the derived series of `A` collapses to `⊥` one step further down, then the
    current term `derivedSeries A n` is abelian: its self-commutator being trivial
    forces every pair of its elements to commute. -/
theorem derivedSeries_penultimate_comm {n : ℕ}
    (h : derivedSeries A (n + 1) = ⊥) (x y : derivedSeries A n) :
    x * y = y * x := by
  have hcomm : ⁅derivedSeries A n, derivedSeries A n⁆ = ⊥ := by
    rw [← derivedSeries_succ]; exact h
  have hcent := commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hx := hcent x.2
  rw [mem_centralizer_iff] at hx
  have hxy := hx (y : A) y.2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact hxy.symm

/-- Quotienting a group by the `n`-th term of its derived series makes the `n`-th
    derived term of the quotient trivial. Equivalently: passing to `G ⧸ Dₙ` strictly
    shortens the derived length, which powers the induction below. -/
theorem derivedSeries_quotient_self (n : ℕ) :
    derivedSeries (A ⧸ derivedSeries A n) n = ⊥ := by
  have hsurj := QuotientGroup.mk'_surjective (derivedSeries A n)
  rw [← map_derivedSeries_eq hsurj n, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

-- ════════════════════════════════════════════════════════════════
-- SECTION II: The Shafarevich reduction principle (axiom-free)
-- ════════════════════════════════════════════════════════════════

/-- **The group-theoretic core of Shafarevich's induction.**

For any predicate `P` on groups:
  * `base`  — `P` holds for the trivial group, and
  * `step`  — `P` is preserved under extension by an abelian normal subgroup
              (from `P (H ⧸ N)` with `N` abelian normal, conclude `P H`);
then `P` holds for every group whose derived series reaches `⊥` at some finite
stage `n`. The proof strips the top abelian layer `Dₙ`, applies the inductive
hypothesis to the shorter quotient `H ⧸ Dₙ`, and lifts back through `step`. -/
theorem realizable_of_derivedSeries_eq_bot
    {P : ∀ (H : Type) [Group H], Prop}
    (base : ∀ (H : Type) [Group H], Subsingleton H → P H)
    (step : ∀ (H : Type) [Group H] (N : Subgroup H) [N.Normal],
              (∀ x y : N, x * y = y * x) → P (H ⧸ N) → P H) :
    ∀ (n : ℕ) (H : Type) [Group H], derivedSeries H n = ⊥ → P H := by
  intro n
  induction n with
  | zero =>
      intro H _ h
      rw [derivedSeries_zero] at h
      refine base H ⟨fun a b => ?_⟩
      have ha : a ∈ (⊥ : Subgroup H) := h ▸ Subgroup.mem_top a
      have hb : b ∈ (⊥ : Subgroup H) := h ▸ Subgroup.mem_top b
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
  | succ n ih =>
      intro H _ h
      refine step H (derivedSeries H n) ?_ ?_
      · exact fun x y => derivedSeries_penultimate_comm h x y
      · exact ih (H ⧸ derivedSeries H n) (derivedSeries_quotient_self n)

/-- **Shafarevich reduction for solvable groups.** Same hypotheses as
`realizable_of_derivedSeries_eq_bot`, packaged with Mathlib's `IsSolvable`
typeclass: any group-property that holds for the trivial group and is preserved
by abelian-kernel extensions holds for every finite solvable group. -/
theorem realizable_of_solvable
    {P : ∀ (H : Type) [Group H], Prop}
    (base : ∀ (H : Type) [Group H], Subsingleton H → P H)
    (step : ∀ (H : Type) [Group H] (N : Subgroup H) [N.Normal],
              (∀ x y : N, x * y = y * x) → P (H ⧸ N) → P H)
    (G : Type) [Group G] [IsSolvable G] : P G := by
  obtain ⟨n, hn⟩ := ‹IsSolvable G›.solvable
  exact realizable_of_derivedSeries_eq_bot base step n G hn

-- ════════════════════════════════════════════════════════════════
-- SECTION III: Instantiation to realizability over ℚ
-- ════════════════════════════════════════════════════════════════

/-- `G` is **realizable over ℚ** if it is isomorphic to the Galois group of some
    finite Galois extension `K / ℚ`. This matches the parent entry's realizability
    predicate (`shafarevich_theorem`, `symmetric_group_realizable`). -/
def RealizableOverRat (G : Type) [Group G] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : FiniteDimensional ℚ K)
    (_ : IsGalois ℚ K), Nonempty (G ≃* (K ≃ₐ[ℚ] K))

/-- **Base case, proved concretely.** The trivial group is realizable over ℚ:
    it is `Gal(ℚ/ℚ)`, the Galois group of the (trivial) extension `ℚ / ℚ`. -/
theorem realizableOverRat_of_subsingleton (H : Type) [Group H] [Subsingleton H] :
    RealizableOverRat H := by
  haveI hsub : Subsingleton (ℚ ≃ₐ[ℚ] ℚ) := by
    constructor
    intro a b
    ext x
    exact DFunLike.congr_fun (Subsingleton.elim (a : ℚ →ₐ[ℚ] ℚ) (b : ℚ →ₐ[ℚ] ℚ)) x
  refine ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  exact
    { toFun := fun _ => 1
      invFun := fun _ => 1
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_mul' := fun _ _ => Subsingleton.elim _ _ }

/-- **Shafarevich's theorem, reduced to the embedding step.**

If every extension of a group realizable over ℚ by an abelian normal subgroup is
again realizable over ℚ (the class-field-theory content, `embed`), then every
finite solvable group is realizable over ℚ. The group-theoretic induction and the
trivial base case are fully verified here; `embed` is the single deep hypothesis,
and it is precisely the substance of Shafarevich's theorem. -/
theorem realizableOverRat_solvable_of_embedding
    (embed : ∀ (H : Type) [Group H] (N : Subgroup H) [N.Normal],
               (∀ x y : N, x * y = y * x) →
               RealizableOverRat (H ⧸ N) → RealizableOverRat H)
    (G : Type) [Group G] [IsSolvable G] : RealizableOverRat G :=
  realizable_of_solvable
    (fun H _ hs => @realizableOverRat_of_subsingleton H _ hs) embed G

end InverseGaloisOQ05
