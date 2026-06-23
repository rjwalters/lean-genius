import Proofs.TractatusOntologyHorn
import Proofs.TractatusOntologySpectrum

/-
# Tractatus T1b: `EquivModel` constructor via symmetric Horn closure (S6 ACT)

Companion to `TractatusOntologyHorn.lean` and
`TractatusOntologySpectrum.lean` addressing the **T1b tier** of
`tractatus-ontology-oq-06`: biconditional-constrained world models.

The key architectural observation (S6 PREP #18518 §2) is that T1b is
**not** a genuinely independent spectrum tier: a biconditional
`w a ↔ w b` is the conjunction of two Horn implications
`w a → w b` and `w b → w a`. Hence

  EquivModel S cs ≃ HornModel S (cs ++ cs.map Prod.swap)

i.e. T1b is the symmetric-closure subclass of T1a. We keep
`EquivModel` as a named constructor (Option C of S6 PREP §6) for
Lean-side ergonomics and record the subsumption explicitly.

Contents:

- `EquivModel S cs` — subtype of `S → Prop` satisfying every
  biconditional `w c.1 ↔ w c.2` for `c ∈ cs`.
- `EquivModel.toWorld`, `EquivModel.toWorldModel` — projections to
  `World S` and to `WorldModel S` (constantly-`False` nonemptiness
  witness).
- `equivModel_iso_hornModel_symm` — the structural iso witnessing
  T1b ⊆ T1a-symmetric.
- `refines_equivModel_hornModel` — every T1b model refines into
  the T1a model sharing its constraint list (strictly more
  constrained side embeds upward in the refinement preorder).
- `equivModel_independence_fails` — biconditional-tier independence
  failure at the spectrum level.

No new axioms.  No sorries.
-/

namespace Tractatus

/-- A `EquivModel S cs`: world functions satisfying `w c.1 ↔ w c.2`
    for every `(c.1, c.2) ∈ cs`. The biconditional packaging makes
    `cs` act as a list of "truth-equivalence" pairs.

    Structurally `EquivModel S cs ≃ HornModel S (cs ++ cs.map Prod.swap)`
    (see `equivModel_iso_hornModel_symm`): T1b is the
    symmetric-closure subclass of T1a. -/
def EquivModel (S : Type) (cs : List (S × S)) : Type :=
  { w : S → Prop // ∀ c ∈ cs, w c.1 ↔ w c.2 }

/-- Project an `EquivModel` element to its underlying bare world. -/
def EquivModel.toWorld {S : Type} {cs : List (S × S)}
    (w : EquivModel S cs) : World S :=
  w.val

/-- Package the `EquivModel S cs` worlds as a `WorldModel S`. The
    constantly-`False` world satisfies every biconditional vacuously
    (`False ↔ False`). -/
def EquivModel.toWorldModel (S : Type) (cs : List (S × S)) : WorldModel S where
  W        := EquivModel S cs
  holds    := fun w s => w.val s
  nonempty := ⟨⟨fun _ => False, fun _ _ => Iff.rfl⟩⟩

/-- **Architectural subsumption: T1b ⊆ T1a-symmetric.** Every T1b
    model is structurally a T1a model under symmetric-pair closure
    of the constraint list. The forward direction splits each
    biconditional `w a ↔ w b` into the two Horn clauses `w a → w b`
    and `w b → w a`; the inverse recombines them.

    Both directions act trivially on the underlying world, so the
    `Equiv` round-trips are `rfl`. This iso is the structural
    explanation of why T1b adds no genuinely new spectrum tier
    relative to T1a. -/
def equivModel_iso_hornModel_symm
    {S : Type} (cs : List (S × S)) :
    EquivModel S cs ≃ HornModel S (cs ++ cs.map Prod.swap) where
  toFun := fun ⟨w, hw⟩ => ⟨w, by
    intro c hc
    rcases List.mem_append.mp hc with hcs | hswap
    · exact (hw c hcs).mp
    · rcases List.mem_map.mp hswap with ⟨⟨a, b⟩, hab, rfl⟩
      exact (hw (a, b) hab).mpr⟩
  invFun := fun ⟨w, hw⟩ => ⟨w, by
    intro c hc
    refine ⟨hw c (List.mem_append.mpr (Or.inl hc)), ?_⟩
    have hswap : (c.2, c.1) ∈ cs.map Prod.swap :=
      List.mem_map.mpr ⟨c, hc, rfl⟩
    exact hw (c.2, c.1) (List.mem_append.mpr (Or.inr hswap))⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- **Refinement: T1b refines into T1a sharing the constraint list.**
    The map sends each biconditional-constrained world to itself,
    interpreting biconditional satisfaction as implication
    satisfaction (the `.mp` direction).

    The converse direction is **false in general** (S6 PREP §3): for
    `cs = [(a, b)]`, the world `w a = false, w b = true` lives in
    `HornModel S [(a, b)]` (since `false → w b` is vacuously true) but
    not in `EquivModel S [(a, b)]` (since `false ↔ true` is false).
    So T1b sits strictly below T1a in the refinement preorder. -/
theorem refines_equivModel_hornModel
    {S : Type} (cs : List (S × S)) :
    Refines (EquivModel.toWorldModel S cs) (HornModel.toWorldModel S cs) :=
  ⟨fun w => ⟨w.val, fun c hc => (w.property c hc).mp⟩,
   fun _ _ => Iff.rfl⟩

/-- **Generic biconditional-tier independence failure.** If `cs` is
    nonempty and every clause has distinct head/tail, the
    biconditional-constrained model cannot realise every Boolean
    assignment — i.e., `HasIndependentProfiles` fails.

    The bad assignment `s ↦ s = a` (where `(a, b)` is the head clause)
    cannot be realised: the biconditional `w a ↔ w b` together with
    `w a` forces `w b`, which would in turn force `b = a`,
    contradicting `a ≠ b`. Same shape as
    `hornModel_independence_fails`; `.mp` extracts the forward
    implication from the biconditional directly. -/
theorem equivModel_independence_fails
    {S : Type} {cs : List (S × S)}
    (hne : cs ≠ [])
    (hpair_distinct : ∀ c ∈ cs, c.1 ≠ c.2) :
    ¬ HasIndependentProfiles (EquivModel.toWorldModel S cs) := by
  intro h
  obtain ⟨head, rest, hcs⟩ := List.exists_cons_of_ne_nil hne
  subst hcs
  obtain ⟨a, b⟩ := head
  let bad : S → Prop := fun s => s = a
  obtain ⟨⟨w, hw⟩, hmatch⟩ := h bad
  have hab : a ≠ b := hpair_distinct (a, b) List.mem_cons_self
  have ha : w a := (hmatch a).mpr rfl
  have hwab : w a ↔ w b := hw (a, b) List.mem_cons_self
  have hb : w b := hwab.mp ha
  exact hab ((hmatch b).mp hb).symm

end Tractatus
