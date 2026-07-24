import Proofs.GodelSecondIncompletenessOQ02GLSyntax

/-!
# GL Kripke semantics — S20 ACT: soundness over transitive converse-wellfounded frames

This companion file is the **S20 ACT** for the
`godel-second-incompleteness-oq02-oq-02` research slug (Solovay's arithmetical
completeness for GL). It delivers the genuine Kripke-semantic axis promised in
the S8 `GLSyntax` header ("S5 ACT (Kripke semantics) will define `forces` and
prove `forces_of_GL_proves`"), generalizing the one-world boolean model of S19
(`Kalmar.lean`) to arbitrary **GL frames**: transitive accessibility relations
whose *converse* is well-founded.

## Contents

* `GLFrame` — worlds + transitive, converse-wellfounded accessibility.
* `GLFrame.irrefl` — every GL frame is irreflexive (needed context for Löb;
  a direct consequence of converse well-foundedness).
* `Forces` — the standard Kripke forcing relation (□ quantifies over
  `R`-successors).
* `forces_of_GL_proves` / `valid_of_GL_proves` — **soundness**: every GL
  theorem is forced at every world of every GL frame under every valuation.
  The Löb-axiom case is the mathematical heart: well-founded induction along
  the converse of `R`, using transitivity to propagate the box hypothesis.
* Independence corollaries impossible for the S19 boolean semantics (which
  forces □ to be constantly true, hence validates `□⊥`):
  - `GL_not_proves_box_falsum` — GL ⊬ `□⊥` (via the two-world chain frame);
  - `GL_not_proves_not_box_falsum` — GL ⊬ `¬□⊥`. Under the arithmetical
    reading `□ = Prov_PA`, the formula `¬□⊥` *is* the consistency statement
    `Con(PA)`, so this is the **modal mirror of the second incompleteness
    theorem**: GL, the logic of provability, does not prove consistency
    (via the one-world dead-end frame, where `□⊥` holds vacuously).
  - `GL_consistent_kripke` — semantic re-proof of `¬ GL_proves ⊥`,
    independent of S19's syntactic Kalmár route (imports only `GLSyntax`).

## Design notes

* **Mathlib-free** like S8/S18/S19: `WellFounded`, `Acc`, and
  `Classical.byContradiction` are all Lean-core. The only listed axiom is the
  foundational `Classical.choice` (via `byContradiction` in the k3/Łukasiewicz
  case — Kripke forcing of `¬¬p → p` over `Prop` is genuinely classical);
  `propext`/`Classical.choice`/`Quot.sound` do not count per the project's
  axiom-integrity policy. 0 sorries, 0 `axiom` declarations.
* Completeness (every frame-valid formula is a GL theorem, Segerberg 1971) is
  NOT claimed here — that is a finite-model-property construction of a
  different order, left as a future stage.

## Status
- **0 sorries, 0 axiom declarations**
- New theorems: `GLFrame.irrefl`, `forces_lob`, `forces_of_GL_proves`,
  `valid_of_GL_proves`, `GL_consistent_kripke`, `GL_not_proves_box_falsum`,
  `GL_not_proves_not_box_falsum`

## References
- Boolos, G. (1993). *The Logic of Provability*. Cambridge University Press, Ch. 4.
- Segerberg, K. (1971). *An Essay in Classical Modal Logic*. Uppsala. (GL frame
  characterization: transitive + converse well-founded.)
- Smoryński, C. (1985). *Self-Reference and Modal Logic*. Springer, §1–2.
-/

namespace GodelSecondGLKripke

open GodelSecondGLSyntax

/-- A **GL frame**: a set of worlds with a transitive accessibility relation
    whose converse is well-founded (no infinite ascending `R`-chains). These
    are exactly the frames for which Löb's axiom is sound; converse
    well-foundedness is the semantic counterpart of the arithmetized
    fixed-point argument. -/
structure GLFrame where
  World : Type
  R : World → World → Prop
  trans : ∀ {x y z : World}, R x y → R y z → R x z
  cwf : WellFounded (fun x y : World => R y x)

/-- Every GL frame is irreflexive: a reflexive point would be an infinite
    ascending chain. Direct consequence of converse well-foundedness. -/
theorem GLFrame.irrefl (F : GLFrame) (x : F.World) : ¬ F.R x x := by
  induction F.cwf.apply x with
  | intro a _ ih => exact fun haa => ih a haa haa

/-- Kripke forcing. The valuation `v` assigns a set of worlds to each atom;
    `□p` holds at `w` iff `p` holds at every `R`-successor of `w`. -/
def Forces (F : GLFrame) (v : PropAtom → F.World → Prop) :
    F.World → GLFormula → Prop
  | w, .atom p   => v p w
  | _, .falsum   => False
  | w, .impl p q => Forces F v w p → Forces F v w q
  | w, .box p    => ∀ u : F.World, F.R w u → Forces F v u p

/-- Validity: forced at every world of every GL frame under every valuation. -/
def Valid (φ : GLFormula) : Prop :=
  ∀ (F : GLFrame) (v : PropAtom → F.World → Prop) (w : F.World), Forces F v w φ

/-- **Soundness of Löb's axiom** `□(□p → p) → □p` on GL frames — the heart of
    the file. Well-founded induction along the converse of `R`: to force `p`
    at a successor `u` of `w`, the induction hypothesis provides `p` at all
    successors of `u` (which are successors of `w` by transitivity), i.e.
    `□p` at `u`, and the antecedent then yields `p` at `u`. -/
theorem forces_lob (F : GLFrame) (v : PropAtom → F.World → Prop) (w : F.World)
    (p : GLFormula) :
    Forces F v w (.impl (.box (.impl (.box p) p)) (.box p)) := by
  intro h
  have key : ∀ u : F.World, F.R w u → Forces F v u p := by
    intro u
    induction F.cwf.apply u with
    | intro x _ ih =>
      intro hwx
      exact h x hwx (fun t hxt => ih t hxt (F.trans hwx hxt))
  exact key

/-- **Kripke soundness of GL**: every GL theorem is forced at every world of
    every transitive converse-wellfounded frame, under every valuation.
    (The name follows the contract announced in the S8 `GLSyntax` header.) -/
theorem forces_of_GL_proves {φ : GLFormula} (h : GL_proves φ) :
    ∀ (F : GLFrame) (v : PropAtom → F.World → Prop) (w : F.World),
      Forces F v w φ := by
  induction h with
  | taut ht =>
    intro F v w
    cases ht with
    | k1 p q => exact fun hp _ => hp
    | k2 p q r => exact fun h1 h2 hp => h1 hp (h2 hp)
    | k3 p q =>
      exact fun hnn hq => Classical.byContradiction fun hnp => hnn hnp hq
  | k p q => exact fun F v w h1 h2 u hu => h1 u hu (h2 u hu)
  | lob p => exact fun F v w => forces_lob F v w p
  | mp h₁ h₂ ih₁ ih₂ => exact fun F v w => ih₁ F v w (ih₂ F v w)
  | nec h ih => exact fun F v w u _ => ih F v u

/-- Soundness, packaged through `Valid`. -/
theorem valid_of_GL_proves {φ : GLFormula} (h : GL_proves φ) : Valid φ :=
  forces_of_GL_proves h

/-- The one-world **dead-end frame**: no successors at all. `□ψ` holds
    vacuously at its world, so it separates `□⊥` from `⊥`. -/
def deadEnd : GLFrame where
  World := Unit
  R := fun _ _ => False
  trans := fun h _ => h.elim
  cwf := ⟨fun x => Acc.intro x (fun _ h => h.elim)⟩

/-- The **two-world chain** `false → true`: transitive (vacuously — there is
    no two-step path) and converse-wellfounded. Its root has a successor, so
    `□⊥` fails at the root. -/
def twoChain : GLFrame where
  World := Bool
  R := fun x y => x = false ∧ y = true
  trans := by
    intro x y z hxy hyz
    rw [hxy.2] at hyz
    exact Bool.noConfusion hyz.1
  cwf := by
    constructor
    intro a
    have ht : Acc (fun x y : Bool => y = false ∧ x = true) true :=
      Acc.intro _ (fun _ hy => Bool.noConfusion hy.1)
    cases a with
    | true => exact ht
    | false =>
      refine Acc.intro _ (fun y hy => ?_)
      have hy2 := hy.2
      subst hy2
      exact ht

/-- Semantic consistency of GL: `⊥` is not forced anywhere, so `GL ⊬ ⊥`.
    Independent re-proof of S19's syntactic `GL_consistent` (this file does
    not import `Kalmar`). -/
theorem GL_consistent_kripke : ¬ GL_proves .falsum := fun h =>
  forces_of_GL_proves h deadEnd (fun _ _ => False) ()

/-- **GL ⊬ □⊥**: GL does not prove that the underlying theory proves its own
    inconsistency. Fails at the root of the two-world chain, whose successor
    would have to force `⊥`. Note the S19 boolean semantics (□ ↦ true)
    *validates* `□⊥`, so this separation genuinely requires frames with
    successors. -/
theorem GL_not_proves_box_falsum : ¬ GL_proves (.box .falsum) := fun h =>
  forces_of_GL_proves h twoChain (fun _ _ => False) false true ⟨rfl, rfl⟩

/-- **GL ⊬ ¬□⊥** — the modal mirror of Gödel's second incompleteness theorem.
    Under the arithmetical reading `□ = Prov_PA`, the formula `¬□⊥` is the
    consistency statement `Con(PA)`; by Solovay arithmetical soundness
    (S16 `Soundness.lean`, modulo its hypotheses), a GL proof of `¬□⊥` would
    yield a PA proof of `Con(PA)`, contradicting G2. Here the unprovability is
    established purely semantically: at the dead-end world `□⊥` holds
    vacuously while `⊥` fails. -/
theorem GL_not_proves_not_box_falsum :
    ¬ GL_proves (.impl (.box .falsum) .falsum) := fun h =>
  forces_of_GL_proves h deadEnd (fun _ _ => False) () (fun _ hu => hu.elim)

end GodelSecondGLKripke
