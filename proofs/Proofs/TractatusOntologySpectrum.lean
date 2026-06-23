import Proofs.TractatusOntology

/-
# Tractatus World-Model Spectrum (S2-α)

Companion to `TractatusOntology.lean` addressing the open question
`tractatus-ontology-oq-06`:

  > Can the space of `WorldModel S` inhabitants be organized into a
  > principled spectrum between the free model (full independence)
  > and constrained models?

This file installs the **refinement preorder** on `WorldModel S` and
proves that `freeModel S` is its maximum element.  See
`research/problems/tractatus-ontology-oq-06/` for the full design
document.

Contents:

- `Refines M M'` — refinement relation between world models.
- `refines_refl`, `refines_trans` — preorder axioms.
- `refines_freeModel` — every model refines into the free model.
- `refines_preserves_eval` — evaluation is preserved along refinements
  (the load-bearing lemma for the rest of the spectrum analysis).
- `tautology_pullback`, `contradiction_pullback` — tautologies and
  contradictions are upward-stable along refinements: more constrained
  models inherit them.

No new axioms.  No sorries.
-/

namespace Tractatus

variable {S : Type}

/-- `Refines M M'` says that every world of `M` has the same Boolean
    profile (on states of affairs) as some world of `M'`.  Equivalently,
    there is a function `f : M.W → M'.W` that is `holds`-preserving
    pointwise on `S`.

    The relation models "constraint removal": going from `M` to `M'`
    discards constraints, so `M`'s worlds embed (Boolean-profile-wise)
    into `M'`'s worlds. -/
def Refines (M M' : WorldModel S) : Prop :=
  ∃ f : M.W → M'.W, ∀ (w : M.W) (s : S), M.holds w s ↔ M'.holds (f w) s

/-- The refinement preorder is reflexive: every model refines into
    itself via the identity. -/
theorem refines_refl (M : WorldModel S) : Refines M M :=
  ⟨id, fun _ _ => Iff.rfl⟩

/-- The refinement preorder is transitive: the composition of two
    refinement embeddings is a refinement embedding. -/
theorem refines_trans {M₁ M₂ M₃ : WorldModel S}
    (h₁ : Refines M₁ M₂) (h₂ : Refines M₂ M₃) : Refines M₁ M₃ := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  exact ⟨g ∘ f, fun w s => (hf w s).trans (hg (f w) s)⟩

/-- **Maximum of the refinement preorder.**  Every world model refines
    into `freeModel S`: send each `w : M.W` to its Boolean profile
    `fun s => M.holds w s : S → Prop`, a world of the free model.

    This pins down `freeModel S` as the *unconstrained* benchmark
    against which every other `WorldModel S` is measured. -/
theorem refines_freeModel (M : WorldModel S) : Refines M (freeModel S) :=
  ⟨fun w => fun s => M.holds w s, fun _ _ => Iff.rfl⟩

/-- **Evaluation is invariant along refinements.**  If `f : M.W → M'.W`
    witnesses a refinement `M ≤ M'`, then for every proposition `p` and
    world `w : M.W`, evaluating `p` at `w` in `M` agrees with evaluating
    `p` at `f w` in `M'`.

    Structurally identical to `truth_functional_compositionality_gen`,
    but recast across two different world models. -/
theorem refines_preserves_eval {M M' : WorldModel S}
    (f : M.W → M'.W)
    (hf : ∀ (w : M.W) (s : S), M.holds w s ↔ M'.holds (f w) s)
    (p : Proposition S) (w : M.W) :
    evalM M p w ↔ evalM M' p (f w) := by
  induction p with
  | elementary s => exact hf w s
  | neg q ih     => simp only [evalM]; exact ih.not
  | conj q r ihq ihr => simp only [evalM]; exact ihq.and ihr

/-- **Tautology pullback.**  If `M` refines into `M'`, then every
    tautology of `M'` is automatically a tautology of `M`.

    Intuition: a refinement `M ≤ M'` means `M` is at least as
    constrained as `M'` (its worlds embed into `M'`'s worlds with the
    same Boolean profile).  Constraints shrink the set of worlds and
    therefore can only *grow* the set of tautologies. -/
theorem tautology_pullback {M M' : WorldModel S}
    (h : Refines M M') (p : Proposition S)
    (hp : IsTautologyM M' p) : IsTautologyM M p := by
  obtain ⟨f, hf⟩ := h
  intro w
  exact (refines_preserves_eval f hf p w).mpr (hp (f w))

/-- **Contradiction pullback.**  Dual to `tautology_pullback`. -/
theorem contradiction_pullback {M M' : WorldModel S}
    (h : Refines M M') (p : Proposition S)
    (hp : IsContradictionM M' p) : IsContradictionM M p := by
  obtain ⟨f, hf⟩ := h
  intro w hw
  exact hp (f w) ((refines_preserves_eval f hf p w).mp hw)

/-- Corollary: every tautology of `freeModel S` is a tautology of every
    world model.  This makes the spectrum's *core invariants* precise:
    `freeModel S`-tautologies are exactly the "spectrum-invariant"
    truths of the Tractarian language.

    (Note: the converse — that every spectrum-invariant tautology
    arises from `freeModel S` — is the subject of a separate open
    question, addressed in subsequent S-iterations.) -/
theorem freeModel_tautology_is_universal (p : Proposition S)
    (hp : IsTautologyM (freeModel S) p) (M : WorldModel S) :
    IsTautologyM M p :=
  tautology_pullback (refines_freeModel M) p hp

/-! ## S7 — Spectrum-invariance ↔ freeModel-tautology (point models) -/

/-- The **point model at `w`**: a `WorldModel S` with a single world
    `Unit`, whose Boolean profile equals `w`. Used as a witness that
    every Boolean assignment `w : S → Prop` is realised by *some*
    `WorldModel S` — the converse direction of the spectrum-invariance
    biconditional. -/
def pointModel (w : S → Prop) : WorldModel S where
  W        := Unit
  holds    := fun _ s => w s
  nonempty := ⟨()⟩

/-- The single-world `holds` of `pointModel w` reads off `w` directly. -/
@[simp]
theorem pointModel_holds (w : S → Prop) (u : Unit) (s : S) :
    (pointModel w).holds u s ↔ w s :=
  Iff.rfl

/-- Evaluating a proposition at the unique world of `pointModel w` agrees
    with evaluating it at `w` in `freeModel S`. The proof is the standard
    structural induction on `Proposition S`, matching the existing
    `refines_preserves_eval` pattern. -/
theorem pointModel_evalM (w : S → Prop) (p : Proposition S) :
    evalM (pointModel w) p () ↔ evalM (freeModel S) p w := by
  induction p with
  | elementary s     => exact Iff.rfl
  | neg q ih         => simp only [evalM]; exact ih.not
  | conj q r ihq ihr => simp only [evalM]; exact ihq.and ihr

/-- A proposition is a tautology of `pointModel w` iff it evaluates to
    true at `w` in `freeModel S`. Corollary of `pointModel_evalM`
    together with the singleton-world nature of `pointModel w`. -/
theorem pointModel_isTautology_iff (w : S → Prop) (p : Proposition S) :
    IsTautologyM (pointModel w) p ↔ evalM (freeModel S) p w := by
  unfold IsTautologyM
  constructor
  · intro h
    exact (pointModel_evalM w p).mp (h ())
  · intro h _
    exact (pointModel_evalM w p).mpr h

/-- **Spectrum-invariance theorem.** A proposition is a tautology of
    every `WorldModel S` iff it is a tautology of `freeModel S`. This
    resolves the converse direction of `freeModel_tautology_is_universal`
    flagged as an open question in `state.md`.

    The forward direction is one step: `freeModel S` is itself a member
    of the spectrum, so the universal quantifier instantiates at it.
    The reverse direction is exactly `freeModel_tautology_is_universal`. -/
theorem spectrum_invariant_iff_freeModel_tautology (p : Proposition S) :
    (∀ M : WorldModel S, IsTautologyM M p) ↔ IsTautologyM (freeModel S) p := by
  constructor
  · intro h
    exact h (freeModel S)
  · intro h M
    exact freeModel_tautology_is_universal p h M

/-- Alternative proof of the converse direction via **point models**,
    not exploiting that `freeModel S` is itself a member of the spectrum.

    Strictly more informative than the `freeModel S`-instantiation proof:
    it shows the converse holds even if the spectrum quantifier were
    restricted to "small / point-like" models. Pedagogically central
    for the state.md framing of the question. -/
theorem spectrum_invariant_implies_freeModel_via_pointModels
    (p : Proposition S) (h : ∀ M : WorldModel S, IsTautologyM M p) :
    IsTautologyM (freeModel S) p := by
  intro w
  have hpoint : IsTautologyM (pointModel w) p := h (pointModel w)
  exact (pointModel_evalM w p).mp (hpoint ())

/-- **Dual: spectrum-invariance for contradictions.** A proposition is a
    contradiction of every `WorldModel S` iff it is a contradiction of
    `freeModel S`. Same structural pattern as
    `spectrum_invariant_iff_freeModel_tautology` (forward: instantiate at
    `freeModel S`; backward: pull back along the `refines_freeModel`
    embedding). -/
theorem spectrum_invariant_contradiction_iff_freeModel_contradiction
    (p : Proposition S) :
    (∀ M : WorldModel S, IsContradictionM M p) ↔ IsContradictionM (freeModel S) p := by
  constructor
  · intro h
    exact h (freeModel S)
  · intro h M
    exact contradiction_pullback (refines_freeModel M) p h

/-! ## S5 — `freeModel` uniqueness via `HasIndependentProfiles` -/

/-- A world model has *independent profiles* when every Boolean
    assignment `a : S → Prop` is realised by some world of the model.
    This is the `WorldModel`-side analogue of `IndependentWorlds S`:
    it lifts the property of `S → Prop` (which `IndependentWorlds S`
    quantifies over) to a predicate on `WorldModel S`.

    `freeModel S` satisfies this trivially; subtype-style constrained
    models satisfy it only when their constraint predicate is vacuous
    (see `subtype_model_independent_iff`). -/
def HasIndependentProfiles (M : WorldModel S) : Prop :=
  ∀ assignment : S → Prop, ∃ w : M.W, ∀ s, M.holds w s ↔ assignment s

/-- The *refinement-isomorphism* relation: mutual refinement. Captured
    as the equivalence induced by the `Refines` preorder. Strictly
    weaker than a genuine `Equiv`: two distinct worlds in either model
    may share a Boolean profile, so `Refines`-iso does not yield a
    bijection of world-types without an additional tightness
    hypothesis. -/
def RefinesIso (M M' : WorldModel S) : Prop :=
  Refines M M' ∧ Refines M' M

/-- The free model has independent profiles: every assignment `a` is
    realised by `a` itself (the world *is* the profile). -/
theorem freeModel_hasIndependentProfiles :
    HasIndependentProfiles (freeModel S) :=
  fun a => ⟨a, fun _ => Iff.rfl⟩

/-- **Half 2 of `freeModel` uniqueness.** `freeModel S` refines into
    any model with independent profiles. The witness is the realiser
    map `a ↦ (hM a).choose`. -/
theorem freeModel_refines_independent
    (M : WorldModel S) (hM : HasIndependentProfiles M) :
    Refines (freeModel S) M := by
  classical
  refine ⟨fun a => (hM a).choose, ?_⟩
  intro a s
  exact ((hM a).choose_spec s).symm

/-- **Uniqueness of `freeModel S`** up to refinement-iso.  Any model
    with independent profiles is `RefinesIso`-related to `freeModel S`.
    Closes the S2-γ open question listed in `state.md` (PR #18391):
    *uniqueness of `freeModel` up to refinement-isomorphism among
    independence-satisfying inhabitants*. -/
theorem freeModel_unique_refines_iso
    (M : WorldModel S) (hM : HasIndependentProfiles M) :
    RefinesIso M (freeModel S) :=
  ⟨refines_freeModel M, freeModel_refines_independent M hM⟩

/-- **Subtype-Tier 1 collapse to T0.** A subtype-style constrained
    model satisfies `HasIndependentProfiles` iff its constraint
    predicate is universally true.

    This is the precise content of "constraint = independence-failure":
    inside Tier 1 (predicate-constrained subtype), the *only* point
    satisfying independence is the one whose constraint is vacuous,
    collapsing back to `freeModel S` up to refinement-iso. -/
theorem subtype_model_independent_iff
    (φ : (S → Prop) → Prop) (hne : Nonempty {w : S → Prop // φ w}) :
    HasIndependentProfiles
        { W := {w : S → Prop // φ w}
          holds := fun w s => w.val s
          nonempty := hne }
    ↔ ∀ a : S → Prop, φ a := by
  refine ⟨fun h a => ?_, fun h a => ⟨⟨a, h a⟩, fun _ => Iff.rfl⟩⟩
  obtain ⟨⟨w, hw⟩, hmatch⟩ := h a
  have hwa : w = a := funext (fun s => propext (hmatch s))
  exact hwa ▸ hw

/-- `weatherModel` fails independence at the spectrum level: there is
    no world realising the assignment `s ↦ s = .rain`, because the
    constraint `w .rain → w .clouds` would force `.clouds = .rain`.
    Spectrum-level restatement of `weather_independence_fails`. -/
theorem weatherModel_not_hasIndependentProfiles :
    ¬ HasIndependentProfiles weatherModel := by
  intro h
  let bad : WeatherFacts → Prop := fun s => s = .rain
  obtain ⟨⟨w, hw⟩, hmatch⟩ := h bad
  have hr : w .rain := (hmatch .rain).mpr rfl
  have hc : w .clouds := hw hr
  have habs : (WeatherFacts.clouds : WeatherFacts) = .rain :=
    (hmatch .clouds).mp hc
  cases habs

/-- `freeModel WeatherFacts` does *not* refine into `weatherModel`:
    the embedding direction fails.  Strengthens
    `weather_independence_fails` to a spectrum-level statement —
    `weatherModel` is **strictly below** `freeModel WeatherFacts` in
    the refinement preorder. -/
theorem freeModel_not_refines_weatherModel :
    ¬ Refines (freeModel WeatherFacts) weatherModel := by
  intro ⟨f, hf⟩
  let bad : WeatherFacts → Prop := fun s => s = .rain
  have hr : (f bad).val .rain := (hf bad .rain).mp rfl
  have hc : (f bad).val .clouds := (f bad).property hr
  have habs : (WeatherFacts.clouds : WeatherFacts) = .rain :=
    (hf bad .clouds).mpr hc
  cases habs

/-! ## S4 — Refinement lattice via image profiles

The refinement preorder `Refines` collapses to subset-inclusion on the
set of Boolean profiles each model realises (`ImageProfiles`). Under that
reduction the lattice operations on `(WorldModel S, Refines)` are exactly
the Set-theoretic operations on `Set (S → Prop)`:

- **join** = profile union (`JoinModel`, always defined; arbitrary
  suprema via `iJoinModel`);
- **meet** = profile intersection (`MeetModel`, defined exactly when the
  intersection is non-empty — there is no bottom element);
- **top** = `freeModel S` (`imageProfiles_freeModel`).

See `research/problems/tractatus-ontology-oq-06/sessions/2026-05-13-s4-prep-refines-lattice-via-image-profiles.md`.
-/

/-- The **image profile set** of a world model: the Boolean assignments
    `S → Prop` actually realised by some world of `M`. -/
def ImageProfiles (M : WorldModel S) : Set (S → Prop) :=
  { w | ∃ v : M.W, ∀ s, w s ↔ M.holds v s }

/-- The image profile set is non-empty: the profile of any world of `M`
    (which exists by `M.nonempty`) inhabits it. -/
theorem imageProfiles_nonempty (M : WorldModel S) :
    (ImageProfiles M).Nonempty := by
  obtain ⟨v⟩ := M.nonempty
  exact ⟨fun s => M.holds v s, ⟨v, fun _ => Iff.rfl⟩⟩

/-- **R-Lattice-1.** `Refines` is exactly subset-inclusion on image
    profiles.  This is the load-bearing reduction: a structural question
    on `WorldModel S` becomes a Set-theoretic question on `Set (S → Prop)`. -/
theorem refines_iff_subset_imageProfiles (M M' : WorldModel S) :
    Refines M M' ↔ ImageProfiles M ⊆ ImageProfiles M' := by
  constructor
  · rintro ⟨f, hf⟩ w ⟨v, hv⟩
    refine ⟨f v, fun s => ?_⟩
    rw [hv s]; exact hf v s
  · intro hsub
    classical
    refine ⟨fun v => Classical.choose (hsub ⟨v, fun _ => Iff.rfl⟩), fun v s => ?_⟩
    exact Classical.choose_spec (hsub ⟨v, fun _ => Iff.rfl⟩) s

/-- Mutual refinement is exactly equality of image profile sets. -/
theorem refinesEquiv_iff_image_eq (M M' : WorldModel S) :
    Refines M M' ∧ Refines M' M ↔ ImageProfiles M = ImageProfiles M' := by
  rw [refines_iff_subset_imageProfiles, refines_iff_subset_imageProfiles,
      Set.Subset.antisymm_iff]

/-- **Top element.**  `freeModel S` realises every Boolean profile, so its
    image profile set is the entire ambient `Set (S → Prop)`.  This is the
    image-profile reformulation of `refines_freeModel`. -/
theorem imageProfiles_freeModel : ImageProfiles (freeModel S) = Set.univ := by
  ext w
  exact ⟨fun _ => trivial, fun _ => ⟨w, fun _ => Iff.rfl⟩⟩

/-- The **disjoint-sum join** of two world models: its worlds are the
    disjoint union of the two world-types, with `holds` inherited
    componentwise. -/
def JoinModel (M₁ M₂ : WorldModel S) : WorldModel S where
  W        := M₁.W ⊕ M₂.W
  holds    := fun w s => Sum.elim (fun v₁ => M₁.holds v₁ s)
                                  (fun v₂ => M₂.holds v₂ s) w
  nonempty := M₁.nonempty.map Sum.inl

/-- The join realises exactly the union of the two profile sets. -/
theorem imageProfiles_join (M₁ M₂ : WorldModel S) :
    ImageProfiles (JoinModel M₁ M₂)
      = ImageProfiles M₁ ∪ ImageProfiles M₂ := by
  ext w
  constructor
  · rintro ⟨v, hv⟩
    cases v with
    | inl v₁ => exact Or.inl ⟨v₁, hv⟩
    | inr v₂ => exact Or.inr ⟨v₂, hv⟩
  · rintro (⟨v, hv⟩ | ⟨v, hv⟩)
    · exact ⟨Sum.inl v, hv⟩
    · exact ⟨Sum.inr v, hv⟩

/-- **LUB property.**  `JoinModel M₁ M₂` is the least upper bound of `M₁`
    and `M₂` in the refinement preorder. -/
theorem refines_join_iff (M₁ M₂ M : WorldModel S) :
    Refines (JoinModel M₁ M₂) M ↔ Refines M₁ M ∧ Refines M₂ M := by
  rw [refines_iff_subset_imageProfiles, imageProfiles_join,
      refines_iff_subset_imageProfiles, refines_iff_subset_imageProfiles,
      Set.union_subset_iff]

/-- The **Boolean-profile pullback (meet)** of two world models, defined
    exactly when the intersection of their image profile sets is
    non-empty.  Its worlds are the shared profiles themselves. -/
def MeetModel (M₁ M₂ : WorldModel S)
    (h : (ImageProfiles M₁ ∩ ImageProfiles M₂).Nonempty) : WorldModel S where
  W        := { wp : (S → Prop) // wp ∈ ImageProfiles M₁ ∩ ImageProfiles M₂ }
  holds    := fun wp s => wp.val s
  nonempty := ⟨⟨h.some, h.some_mem⟩⟩

/-- The meet realises exactly the intersection of the two profile sets. -/
theorem imageProfiles_meet (M₁ M₂ : WorldModel S)
    (h : (ImageProfiles M₁ ∩ ImageProfiles M₂).Nonempty) :
    ImageProfiles (MeetModel M₁ M₂ h)
      = ImageProfiles M₁ ∩ ImageProfiles M₂ := by
  ext w
  constructor
  · rintro ⟨⟨wp, hwp⟩, hh⟩
    have heq : w = wp := funext (fun s => propext (hh s))
    rw [heq]; exact hwp
  · intro hw
    exact ⟨⟨w, hw⟩, fun _ => Iff.rfl⟩

/-- **GLB property.**  `MeetModel M₁ M₂ h` is the greatest lower bound of
    `M₁` and `M₂` in the refinement preorder, on the (non-empty
    intersection) domain where it is defined. -/
theorem refines_meet_iff (M M₁ M₂ : WorldModel S)
    (h : (ImageProfiles M₁ ∩ ImageProfiles M₂).Nonempty) :
    Refines M (MeetModel M₁ M₂ h)
      ↔ Refines M M₁ ∧ Refines M M₂ := by
  rw [refines_iff_subset_imageProfiles, imageProfiles_meet,
      refines_iff_subset_imageProfiles, refines_iff_subset_imageProfiles,
      Set.subset_inter_iff]

/-- The **arbitrary join** of a non-empty indexed family of world models
    (`Σ`-type construction), witnessing that the refinement preorder is a
    complete join-semilattice (modulo refinement-equivalence). -/
def iJoinModel {I : Type} [Nonempty I] (M : I → WorldModel S) :
    WorldModel S where
  W        := Σ i : I, (M i).W
  holds    := fun w s => (M w.1).holds w.2 s
  nonempty := by
    obtain ⟨i⟩ := ‹Nonempty I›
    obtain ⟨v⟩ := (M i).nonempty
    exact ⟨⟨i, v⟩⟩

/-- The arbitrary join realises exactly the union of the families'
    profile sets. -/
theorem imageProfiles_iJoin {I : Type} [Nonempty I] (M : I → WorldModel S) :
    ImageProfiles (iJoinModel M) = ⋃ i, ImageProfiles (M i) := by
  ext w
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i, v⟩, hv⟩
    exact ⟨i, v, hv⟩
  · rintro ⟨i, v, hv⟩
    exact ⟨⟨i, v⟩, hv⟩

/-- **Arbitrary LUB property.**  `iJoinModel M` is the least upper bound of
    the family `M` in the refinement preorder. -/
theorem refines_iJoin_iff {I : Type} [Nonempty I]
    (M : I → WorldModel S) (N : WorldModel S) :
    Refines (iJoinModel M) N ↔ ∀ i, Refines (M i) N := by
  rw [refines_iff_subset_imageProfiles, imageProfiles_iJoin,
      Set.iUnion_subset_iff]
  simp_rw [refines_iff_subset_imageProfiles]

end Tractatus
