/-
  Gödel Incompleteness vs Turing Undecidability  (godel-incompleteness-oq-02)

  ## The Open Question

  Gödel's First Incompleteness Theorem and Turing's undecidability of the halting
  problem are two faces of the same diagonal argument.  The parent gallery proof
  `GodelIncompleteness` builds the incompleteness phenomenon syntactically (a
  self-referential sentence via the diagonal lemma).  This file makes the *Turing
  route* to incompleteness precise and fully constructive:

    undecidability of a diagonal predicate  ⟹  incompleteness of any sound,
    effectively axiomatized theory that represents it.

  The deep historical point — already implicit in Turing 1936 and made explicit by
  the recursion-theoretic proofs of incompleteness — is that one does *not* need to
  build a Gödel sentence by hand.  Diagonalization against the *provability
  predicate itself* produces an explicit independent sentence, and the witness is
  the code of the theory's own provability decider.

  ## What This File Proves (all 0 axioms, 0 sorries, self-contained)

  ### Part I — the Turing/Cantor diagonal
  `run e n` models "the decision procedure with code `e`, run on input `n`",
  returning a `Bool`.  The diagonal predicate `D n := (run n n = false)` ("procedure
  `n` rejects its own code") is the abstract halting-style predicate.
  * `D_undecidable` : **no code decides `D`.**  This is the Turing/Cantor diagonal
    in its purest form, uniform over every choice of `run`.

  ### Part II — undecidability forces incompleteness
  A `SoundEffectiveTheory` for `D` packages: a provability predicate `Provable`, a
  refutation predicate `Refutable`, soundness of both, and the *effectiveness*
  hypothesis that `Provable` is computed by some code (it is decided by a `run`-code).
  * `godel_via_turing` : every such theory has an **explicit independent sentence**,
    and the witness `n` is the code `e` of the theory's own provability decider —
    the recursion-theoretic Gödel sentence "the prover rejects its own code".
  * `incompleteness` : restating the same fact as `¬ Complete`.
  * `sound_imp_consistent` : soundness already yields consistency for free.

  ### Part III — concrete instance
  `no_decider_for_const_true` exhibits a concrete `run` for which `D` is the empty
  predicate yet still undecidable in the `run`-family, illustrating that the
  obstruction is structural, not about the predicate being "hard".

  ## Relationship to the parent

  The parent's `Provable` is a placeholder; here `Provable` is an arbitrary predicate
  constrained only by soundness + effectiveness, so the incompleteness conclusion is
  a theorem about *all* such theories rather than one fixed encoding.  The bridge to
  Gödel's syntactic sentence is that `D e` plays exactly the role of `G`: a sentence
  true (in the standard interpretation given by `D`) but unprovable.
-/

import Mathlib.Tactic

namespace GodelTuring

/-! ## Part I: The Turing/Cantor diagonal — an undecidable predicate

`run e n` is the abstract "machine `e` on input `n`" returning a `Bool` verdict.
Totality is harmless: the diagonal obstruction below holds for *every* such `run`,
which is exactly why it is the common core of Turing undecidability and Gödel
incompleteness. -/

variable (run : ℕ → ℕ → Bool)

/-- The diagonal predicate: `D n` holds iff procedure `n` *rejects* its own code.
    This is the abstract halting-style predicate that no member of the family can
    decide. -/
def D (n : ℕ) : Prop := run n n = false

/-- A predicate `P` is *decided by code* `e` when `run e` is its characteristic
    function: `run e n = true ↔ P n` for all `n`.  This is the abstract notion of
    "`P` is computable within the family `run`". -/
def DecidedBy (P : ℕ → Prop) (e : ℕ) : Prop := ∀ n, (run e n = true ↔ P n)

/-- **Turing's diagonal (halting-style undecidability).**
    No code decides the diagonal predicate `D`.  If `run e` were `D`'s characteristic
    function, evaluating at `n = e` would force `run e e = true ↔ run e e = false`. -/
theorem D_undecidable : ¬ ∃ e, DecidedBy run (D run) e := by
  rintro ⟨e, he⟩
  -- `he e : run e e = true ↔ D run e`, and `D run e` is `run e e = false`.
  have key : run e e = true ↔ run e e = false := he e
  cases h : run e e with
  | false => rw [h] at key; simp at key
  | true => rw [h] at key; simp at key

/-! ## Part II: Undecidability forces incompleteness

A theory that is *sound* about `D` and whose provability predicate is *effective*
(computed by some code in the family) cannot be complete: diagonalizing against the
provability decider yields an explicit independent sentence. -/

/-- A sound, effectively axiomatized theory of the `D`-sentences.

* `Provable n`   — the theory proves the sentence asserting `D n`.
* `Refutable n`  — the theory proves its negation `¬ D n`.
* `sound_pos`    — provability is truthful: proving `D n` makes `D n` true.
* `sound_neg`    — refutation is truthful: refuting `D n` makes `D n` false.
* `decidable_provable` — *effectiveness*: provability is decided by some code `e`.
  This is the recursion-theoretic stand-in for "the axioms are recursively
  enumerable / the theory is effectively axiomatized". -/
structure SoundEffectiveTheory where
  /-- The theory proves the sentence asserting `D n`. -/
  Provable : ℕ → Prop
  /-- The theory proves the negation of the sentence asserting `D n`. -/
  Refutable : ℕ → Prop
  /-- Soundness on the positive side: a proof of `D n` makes `D n` true. -/
  sound_pos : ∀ n, Provable n → D run n
  /-- Soundness on the negative side: a refutation of `D n` makes `D n` false. -/
  sound_neg : ∀ n, Refutable n → ¬ D run n
  /-- Effectiveness: the provability predicate is decided by some code. -/
  decidable_provable : ∃ e, DecidedBy run Provable e

variable {run}

/-- Soundness alone yields **consistency**: no sentence is both provable and
    refutable, since that would make `D n` simultaneously true and false. -/
theorem sound_imp_consistent (T : SoundEffectiveTheory run) (n : ℕ) :
    ¬ (T.Provable n ∧ T.Refutable n) := by
  rintro ⟨hp, hr⟩
  exact T.sound_neg n hr (T.sound_pos n hp)

/-- **Gödel's First Incompleteness Theorem, via Turing.**
    Every sound, effectively axiomatized theory of the `D`-sentences has an explicit
    independent sentence, neither provable nor refutable.  The witness is `e`, the
    *code of the theory's own provability decider*: the sentence `D e` says "the
    prover rejects its own code", the recursion-theoretic Gödel sentence. -/
theorem godel_via_turing (T : SoundEffectiveTheory run) :
    ∃ n, ¬ T.Provable n ∧ ¬ T.Refutable n := by
  obtain ⟨e, he⟩ := T.decidable_provable
  refine ⟨e, ?_, ?_⟩
  · -- If `D e` were provable, soundness gives `run e e = false`, but the decider
    -- characterization gives `run e e = true`.
    intro hp
    have h1 : run e e = true := (he e).mpr hp
    have h2 : run e e = false := T.sound_pos e hp
    rw [h1] at h2
    exact Bool.noConfusion h2
  · -- If `D e` were refutable, soundness gives `run e e = true`; the decider then
    -- makes `D e` provable, and soundness again makes `D e` true — contradiction.
    intro hr
    have h2 : ¬ D run e := T.sound_neg e hr
    have h1 : run e e = true := by
      cases h : run e e with
      | false => exact absurd h h2
      | true => rfl
    have hp : T.Provable e := (he e).mp h1
    exact h2 (T.sound_pos e hp)

/-- The independent sentence is `D e`, with `e` the code of the provability decider.
    This isolates the explicit Gödel sentence produced by the Turing route. -/
theorem godel_sentence_independent (T : SoundEffectiveTheory run)
    (e : ℕ) (he : DecidedBy run T.Provable e) :
    ¬ T.Provable e ∧ ¬ T.Refutable e := by
  constructor
  · intro hp
    have h1 : run e e = true := (he e).mpr hp
    have h2 : run e e = false := T.sound_pos e hp
    rw [h1] at h2; exact Bool.noConfusion h2
  · intro hr
    have h2 : ¬ D run e := T.sound_neg e hr
    have h1 : run e e = true := by
      cases h : run e e with
      | false => exact absurd h h2
      | true => rfl
    exact h2 (T.sound_pos e ((he e).mp h1))

/-- Completeness of a theory: every `D`-sentence is provable or refutable. -/
def Complete (T : SoundEffectiveTheory run) : Prop :=
  ∀ n, T.Provable n ∨ T.Refutable n

/-- **Incompleteness, stated negatively.**  A sound, effectively axiomatized theory
    of the `D`-sentences is never complete. -/
theorem incompleteness (T : SoundEffectiveTheory run) : ¬ Complete T := by
  intro hC
  obtain ⟨n, hnp, hnr⟩ := godel_via_turing T
  rcases hC n with h | h
  · exact hnp h
  · exact hnr h

/-! ## Part III: A concrete instance

The obstruction is structural, not a matter of the predicate being "hard": even the
*empty* predicate is undecidable inside a family that never answers `false`. -/

/-- For the constant-`true` family, `D` is the empty predicate (`run n n = false` is
    never true), yet no code decides it: a decider would need `run e n = true ↔ False`
    while `run e n` is always `true`. -/
theorem no_decider_for_const_true :
    ¬ ∃ e, DecidedBy (fun _ _ => true) (D (fun _ _ => true)) e := by
  exact D_undecidable (fun _ _ => true)

/-- In the constant-`true` family `D` is identically `False`. -/
theorem const_true_D_false (n : ℕ) : ¬ D (fun _ _ => true) n := by
  simp [D]

end GodelTuring
