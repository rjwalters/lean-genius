/-
  Cantor's theorem, branch oq-02 (Lawvere's fixed-point theorem), open
  question oq-04:

      "What types admit Lawvere fixed-point theorems? (Any pointed dcpo
       satisfies a version — connection to Scott's fixed-point theorem.)"

  The parent file `CantorsTheoremOQ02.lean` proves Lawvere's theorem
  (point-surjectivity of `A → (A → B)` forces every endomap of `B` to have a
  fixed point) and its Cantor/Gödel/Tarski corollaries. This file addresses the
  follow-up classification question: *which* types/maps admit a fixed-point
  theorem, and how the diagonal (Lawvere) source of fixed points relates to the
  order-theoretic (Knaster–Tarski / Scott–Kleene) one.

  We isolate two distinct "fixed-point properties":

    * `HasFPP B`           — every self-map `f : B → B` has a fixed point
                             (the *unrestricted* property targeted by Lawvere);
    * `HasMonotoneFPP B`   — every *monotone* self-map has a fixed point
                             (the order-theoretic property satisfied by complete
                             lattices, and a "version" of which holds on any
                             pointed dcpo via Scott–Kleene iteration).

  Main results (all axiom-free / sorry-free):
    * `hasFPP_of_pointSurjective` : Lawvere's theorem in FPP form;
    * `not_hasFPP_bool`, `not_hasFPP_prop` : `Bool`/`Prop` lack the unrestricted
      FPP (the Cantor obstruction — a fixed-point-free `not`);
    * `hasMonotoneFPP_completeLattice` : Knaster–Tarski — every complete lattice
      has the monotone FPP, the order-theoretic counterpart of Lawvere;
    * `bool_monotoneFPP_but_not_FPP` : the discriminating example. `Bool` is a
      complete lattice (so monotone maps always have fixed points) yet lacks the
      unrestricted FPP, because `not` is *antitone*, not monotone, and so slips
      past the order-completeness route. This precisely delineates which
      fixed-point theorem applies to which class of maps.
-/

import Mathlib

namespace CantorsTheoremOQ02OQ04

/-! ## The unrestricted fixed-point property (Lawvere's target) -/

/-- A type `B` has the **(unrestricted) fixed-point property** if every self-map
`f : B → B` has a fixed point. -/
def HasFPP (B : Type*) : Prop := ∀ f : B → B, ∃ b, f b = b

/-- Any nonempty subsingleton (in particular any `Unique` type) has the FPP. -/
theorem hasFPP_of_subsingleton (B : Type*) [Subsingleton B] [Nonempty B] :
    HasFPP B := by
  intro f
  obtain ⟨b⟩ := (inferInstance : Nonempty B)
  exact ⟨b, Subsingleton.elim _ _⟩

/-- **Lawvere's fixed-point theorem (FPP form).**
If there is a point-surjective map `φ : A → (A → B)` then `B` has the FPP. -/
theorem hasFPP_of_pointSurjective {A B : Type*} (φ : A → (A → B))
    (hφ : ∀ g : A → B, ∃ a, φ a = g) : HasFPP B := by
  intro f
  obtain ⟨a, ha⟩ := hφ (fun x => f (φ x x))
  refine ⟨φ a a, ?_⟩
  have h := congrFun ha a
  simpa using h.symm

/-- The Cantor obstruction: `Bool` does **not** have the FPP, since `not` is
fixed-point-free. -/
theorem not_hasFPP_bool : ¬ HasFPP Bool := by
  intro h
  obtain ⟨b, hb⟩ := h (fun x => !x)
  cases b <;> simp at hb

/-- The Cantor obstruction for `Prop`: negation is fixed-point-free
(`p ↔ ¬p` is impossible), so `Prop` does **not** have the FPP. -/
theorem not_hasFPP_prop : ¬ HasFPP Prop := by
  intro h
  obtain ⟨p, hp⟩ := h Not
  exact iff_not_self (iff_of_eq hp).symm

/-! ## The monotone fixed-point property (the order/dcpo form) -/

/-- A preordered type `B` has the **monotone fixed-point property** if every
*monotone* self-map has a fixed point. This is the order-theoretic property
underlying the Scott–Kleene / Knaster–Tarski fixed-point theorems. -/
def HasMonotoneFPP (B : Type*) [Preorder B] : Prop :=
  ∀ f : B →o B, ∃ b, f b = b

/-- **Knaster–Tarski.** Every complete lattice has the monotone FPP — the
order-theoretic counterpart of Lawvere's theorem. The least fixed point
`f.lfp = ⨆ⁿ fⁿ(⊥)`-style construction is provided by Mathlib's `OrderHom.lfp`,
and is exactly the "version" a pointed dcpo satisfies via Scott continuity. -/
theorem hasMonotoneFPP_completeLattice (B : Type*) [CompleteLattice B] :
    HasMonotoneFPP B := fun f => ⟨f.lfp, f.map_lfp⟩

/-! ## Delineating the two properties -/

/-- **The discriminating example.**

`Bool` is a complete lattice, so *every monotone* self-map has a fixed point
(`HasMonotoneFPP Bool`); yet it lacks the *unrestricted* FPP (`not` is
fixed-point-free). The two are reconciled by the fact that `not` is **antitone,
not monotone**, so it lies outside the reach of the order-completeness route.

This shows the answer to oq-04 is genuinely *property-dependent*: a type can
admit the order-theoretic fixed-point theorem while failing the unrestricted
one. Lawvere's theorem supplies unrestricted fixed points from surjectivity;
Knaster–Tarski / Scott supplies monotone fixed points from order completeness;
neither subsumes the other. -/
theorem bool_monotoneFPP_but_not_FPP :
    HasMonotoneFPP Bool ∧ ¬ HasFPP Bool :=
  ⟨hasMonotoneFPP_completeLattice Bool, not_hasFPP_bool⟩

/-- `not : Bool → Bool` witnesses the failure of the unrestricted FPP and is the
reason `Bool` escapes the monotone route: it is not monotone. -/
theorem not_not_monotone : ¬ Monotone (fun b : Bool => !b) := by
  intro hmono
  have hle : (!false) ≤ (!true) := hmono (by decide : (false : Bool) ≤ true)
  exact absurd hle (by decide)

/-- Lawvere's theorem genuinely applies to types with the FPP: e.g. `Prop`
lacking the FPP re-proves Cantor's theorem — there is no point-surjection
`A → (A → Prop)`. -/
theorem no_pointSurjection_to_powerProp {A : Type*} (φ : A → (A → Prop)) :
    ¬ (∀ g : A → Prop, ∃ a, φ a = g) := by
  intro hsurj
  exact not_hasFPP_prop (hasFPP_of_pointSurjective φ hsurj)

end CantorsTheoremOQ02OQ04
