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

end Tractatus
