import Proofs.TractatusOntology

/-
# Tractatus T1a: Generic `HornModel` constructor (S3 ACT)

Companion to `TractatusOntology.lean` and `TractatusOntologySpectrum.lean`
addressing `tractatus-ontology-oq-06`: the **T1a tier** of the world-model
spectrum (single-hypothesis Horn-clause constrained worlds).

This file generalises the parent file's `ConstrainedWorld S a b`
(a single Horn clause `w a → w b`) to a *list* of Horn clauses, exhibits
`weatherModel` as an instance, and proves the independence-failure
theorem at the generic level.

Contents:

- `HornModel S cs` — subtype of `S → Prop` satisfying every Horn
  implication in `cs : List (S × S)`.
- `HornModel.toWorld` — projection to the bare world `S → Prop`.
- `HornModel.toWorldModel` — packaging into a `WorldModel S`.
- `hornModel_equiv_constrainedWorld` — `Equiv` between
  `HornModel S [(a, b)]` and `ConstrainedWorld S a b`.
- `hornModel_independence_fails` — generic Horn-tier independence
  failure: if `cs` is nonempty and every clause has distinct
  head/tail, no Horn-constrained model realises every assignment.
- `weatherModel_equiv_hornModel` — `weatherModel` as a single-clause
  `HornModel` instance, via the equivalence with `ConstrainedWorld`.

No new axioms.  No sorries.
-/

namespace Tractatus

/-- A `HornModel S cs`: world functions satisfying every Horn clause in
    `cs`. Each pair `(a, b) ∈ cs` is read as the implication `w a → w b`.

    This is the **T1a-tier** spectrum representative: a generic
    constructor that recovers `ConstrainedWorld S a b` at
    `cs = [(a, b)]` and admits `weatherModel` as an instance. -/
def HornModel (S : Type) (cs : List (S × S)) : Type :=
  { w : S → Prop // ∀ c ∈ cs, w c.1 → w c.2 }

/-- Project a `HornModel` element to its underlying bare world. -/
def HornModel.toWorld {S : Type} {cs : List (S × S)}
    (hw : HornModel S cs) : World S :=
  hw.val

/-- Package the `HornModel S cs` worlds as a `WorldModel S`. The
    constantly-`False` world satisfies every Horn clause vacuously. -/
def HornModel.toWorldModel (S : Type) (cs : List (S × S)) : WorldModel S where
  W        := HornModel S cs
  holds    := fun hw s => hw.val s
  nonempty := ⟨⟨fun _ => False, fun _ _ h => h.elim⟩⟩

/-- **Single-clause embedding.** A `HornModel S [(a, b)]` is in bijection
    with a `ConstrainedWorld S a b`: both are the subtype
    `{w : S → Prop // w a → w b}`, packaged differently. -/
def hornModel_equiv_constrainedWorld
    {S : Type} (a b : S) :
    HornModel S [(a, b)] ≃ ConstrainedWorld S a b where
  toFun := fun ⟨w, h⟩ =>
    ⟨w, fun ha => h (a, b) (List.mem_singleton.mpr rfl) ha⟩
  invFun := fun ⟨w, h⟩ =>
    ⟨w, fun c hc ha => by
      rcases List.mem_singleton.mp hc with rfl
      exact h ha⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- **Generic Horn-tier independence failure.** If `cs` is nonempty and
    every clause has distinct head and tail, then `HornModel S cs` cannot
    realise every Boolean assignment.

    Generalises `constrained_independence_fails`: the bad assignment
    `s ↦ s = a` (where `(a, b)` is the head clause) cannot be realised,
    because the Horn clause forces `w b` whenever `w a`, contradicting
    `a ≠ b`. -/
theorem hornModel_independence_fails
    {S : Type} {cs : List (S × S)}
    (hne : cs ≠ [])
    (hpair_distinct : ∀ c ∈ cs, c.1 ≠ c.2) :
    ¬ ∀ assignment : S → Prop,
      ∃ hw : HornModel S cs, ∀ s, hw.val s ↔ assignment s := by
  intro h
  obtain ⟨head, rest, hcs⟩ := List.exists_cons_of_ne_nil hne
  subst hcs
  obtain ⟨a, b⟩ := head
  let bad : S → Prop := fun s => s = a
  obtain ⟨⟨w, hw⟩, hmatch⟩ := h bad
  have hab : a ≠ b := hpair_distinct (a, b) List.mem_cons_self
  have ha : w a := (hmatch a).mpr rfl
  have hwab : w a → w b := hw (a, b) List.mem_cons_self
  have hb : w b := hwab ha
  exact hab ((hmatch b).mp hb).symm

/-- **`weatherModel` as a single-clause `HornModel`.** The weather
    model's worlds (subject to `rain → clouds`) are exactly the
    `HornModel WeatherFacts [(.rain, .clouds)]` worlds.

    This exhibits the parent file's ad-hoc `weatherModel` as an
    instance of the generic T1a-tier constructor — closing the
    S3 PREP §5 hand-off item that the existing instances should be
    expressible through the generic family. -/
def weatherModel_equiv_hornModel :
    weatherModel.W ≃ HornModel WeatherFacts
        [(WeatherFacts.rain, WeatherFacts.clouds)] where
  toFun := fun ⟨w, h⟩ =>
    ⟨w, fun c hc => by
      rcases List.mem_singleton.mp hc with rfl
      exact h⟩
  invFun := fun ⟨w, h⟩ =>
    ⟨w, h (WeatherFacts.rain, WeatherFacts.clouds)
        (List.mem_singleton.mpr rfl)⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The weather Horn-clause has distinct head and tail, so the generic
    independence-failure theorem applies. This recovers
    `weather_independence_fails` at the spectrum level. -/
theorem weatherModel_horn_independence_fails :
    ¬ ∀ assignment : WeatherFacts → Prop,
      ∃ hw : HornModel WeatherFacts [(WeatherFacts.rain, WeatherFacts.clouds)],
        ∀ s, hw.val s ↔ assignment s := by
  apply hornModel_independence_fails
  · exact List.cons_ne_nil _ _
  · intro c hc
    rcases List.mem_singleton.mp hc with rfl
    decide

end Tractatus
