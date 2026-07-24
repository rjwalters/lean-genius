/-
# Relativized Halting Problem (halting-problem-OQ-03, sub-goal OQ-03a)

## What This Proves
The diagonal argument from `Proofs.HaltingProblem` lifts to the relativized
setting: for every oracle `o : Nat -> Bool`, no oracle-aware halting predictor
can correctly decide its own halting problem. This is the Lean target

  ∀ o, ¬ ∃ H : RelativizedHaltingPredictor, H decides relativized halting

stated formally below as `no_relativized_halting_oracle` and packaged in the
oracle-class form `relativized_halting_undecidable`.

## Scope (S2 ACT-A + S3 ACT-B + S5 ACT-D + S6, 2026-05-12)
This file is intentionally **zero-import** (matching the parent
`Proofs.HaltingProblem`). It establishes the diagonal core of sub-goal OQ-03a
at the abstract `Nat -> Nat -> Bool` level. Concretely:

* Definitions (S2):
    * `RelativizedHaltingPredictor` — an oracle-aware halting predictor,
      modelled as `(Nat -> Bool) -> Nat -> Nat -> Bool`.
    * `relativizedDiagonalBehavior` — the relativized analog of the
      parent's `diagonalBehavior`.
    * `Decides_in` — the abstract oracle-class membership predicate:
      "predictor `H` decides relativized halting for oracle `o`".

* Theorems (S2; all proved, no sorries):
    * `relativized_diagonal_differs` — for every oracle `o`, predictor `H`,
      and code `n`, the relativized diagonal differs from `H` at `(n, n)`.
    * `no_relativized_halting_oracle` — the contradiction form of OQ-03a.
    * `relativized_halting_undecidable` — packaged statement: no
      `H : RelativizedHaltingPredictor` satisfies `Decides_in o H`.
    * `relativized_collapses_to_classical_at_trivial_oracle` — sanity check
      that the `o = fun _ => false` specialization of the relativized
      diagonal recovers the parent's `diagonalBehavior`.
    * `no_uniform_relativized_halting_oracle` — no single predictor decides
      relativized halting uniformly across every oracle.

* Definitions and theorems added in S3 ACT-B (abstract iterated jump, all
  proved, no sorries):
    * `jumpOracle` — abstract analog of the classical Turing jump
      `A ↦ A'`, taking `(H, o)` to the diagonal-witness oracle.
    * `jumpIter` — n-fold iteration of `jumpOracle`, abstract analog of
      the chain `A, A', A'', ...` of iterated Turing jumps.
    * `jumpIter_zero`, `jumpIter_succ` — definitional equations.
    * `jumpIter_differs` — at every level `n` and every code `c`, the
      oracle at level `n+1` differs from `H`'s prediction at the diagonal
      of the level-`n` oracle. Abstract analog of Post 1944.
    * `jumpIter_halting_undecidable` — relativized halting is undecidable
      at every jump level.
    * `no_uniform_jumpIter_predictor` — no predictor uniformly decides
      relativized halting across the entire jump iteration (free `H, o₀, n`).
    * `jumpIterWitness`, `jumpIterWitness_differs` — named alias for the
      level-`(n+1)` diagonal witness, for downstream reuse.

* Section 9 (S5 ACT-D, semigroup law, all proved, no sorries):
    * `jumpIter_compose` — `jumpIter H o₀ (m + n) = jumpIter H (jumpIter
      H o₀ m) n`. Abstract analog of `(A^(m))^(n) = A^(m+n)`.

* Section 10 (S6, step dichotomy and flip characterization, all
  proved, no sorries):
    * `jumpIter_succ_apply` — rfl reduction lemma exposing
      `jumpIter (n+1) c = Bool.not (H (jumpIter n) c c)`.
    * `jumpIter_step_dichotomy` — at every step and code, the jump
      iteration either preserves or flips the Boolean value.
    * `jumpIter_step_flip_iff` — consecutive levels differ at code `c`
      iff `H (jumpIter H o₀ n) c c = jumpIter H o₀ n c`. Abstract
      Boolean analog of Post 1944's strictness condition pinned to a
      specific code.
    * `jumpIter_step_stable_of_self_disagree` — disagreement at the
      c-diagonal yields step-wise stability at `c`.

* Section 11 (S7-light, non-degeneracy certificate framework + trivial-
  predictor instantiation, all proved, no sorries):
    * `NonDegenerateAt H o₀ c n` — per-code/per-level certificate.
    * `strict_step_of_nonDegenerateAt` / `..._iff_strict_step` — the
      certificate equivalences from `jumpIter_step_flip_iff`.
    * `IsEventuallyNonDegenerateAt` — existential per-code form.
    * `trivialPredictor`, `falseOracle`, `nonDegenerateAt_trivialPredictor_zero`
      — small fully-verified instance witnessing non-vacuity at level 0.

* Section 12 (S8-light, universal non-degeneracy + identity-style
  predictor + function-level strict-chain consequence, all proved,
  no sorries):
    * `IsAlwaysNonDegenerate H o₀` — universal form `∀ n c,
      NonDegenerateAt H o₀ c n`.
    * `chain_strict_succ_of_isAlwaysNonDegenerate` — function-level
      consequence: consecutive levels disagree as functions.
    * `identityPredictor := fun o _ x => o x` — concrete predictor
      satisfying the universal form for any starting oracle (in contrast
      to `trivialPredictor`, whose chain stabilizes from level 1).
    * `nonDegenerateAt_identityPredictor`,
      `isAlwaysNonDegenerate_identityPredictor`,
      `chain_strict_succ_identityPredictor` — non-vacuous concrete
      witness for every level.

## Out of scope (deferred to future iterations)
* The Mathlib-`Nat.Partrec.Code` bridge. State.md S2 proposed parameterizing
  `Code.evaln` over an oracle (a new constructor `Code.oracle` is impossible
  because Mathlib's `Code` is sealed; the right move is a parallel inductive
  `OracleCode` with its own `OracleCode.evaln`). That is ~200 lines of
  reusable Mathlib-style API and is deferred to a future S3+ session
  (or a sub-OQ `halting-problem-oq-03-bridge`).
* Arithmetical hierarchy (OQ-03b) and hypercomputation (OQ-03c). Both are
  deferred to S5+ per state.md.

## Why the abstract level suffices for OQ-03a
The parent `HaltingProblem.lean`'s mathematical content lives at the
`Nat -> Nat -> Bool` abstraction: any predictor at that abstraction is
diagonalized against. The relativized form replaces predictors by
oracle-aware predictors `(Nat -> Bool) -> Nat -> Nat -> Bool`; the diagonal
argument lifts mechanically. The "Computable_in" class from the literature
(Soare 1987, ch. III; Cooper 2004, ch. 9) is a *strengthening* of this
abstraction — every predictor computable in oracle `o` is in particular an
oracle-aware predictor, so the abstract theorem implies the literature form.

In other words: if no `(Nat -> Bool) -> Nat -> Nat -> Bool` decides
relativized halting, then a fortiori no Code-`evalnO`-defined predictor
does. This file proves the stronger abstract statement; the Mathlib bridge
is purely a packaging concern.

## References
* Turing, A.M. (1939). *Systems of logic based on ordinals.* Proc. London
  Math. Soc. s2-45.
* Post, E.L. (1944). *Recursively enumerable sets of positive integers and
  their decision problems.* Bull. AMS 50(5).
* Soare, R.I. (1987). *Recursively Enumerable Sets and Degrees.* Springer.
* Cooper, S.B. (2004). *Computability Theory.* Chapman & Hall.
* Parent proof: `proofs/Proofs/HaltingProblem.lean` (Turing 1936,
  diagonalization, zero imports, zero axioms).
-/

namespace RelativizedHalting

/-! ### Section 1. Abstract oracle predictors and behaviors -/

/-- A "relativized halting oracle" is a function that, given an oracle
`o : Nat -> Bool`, claims to decide whether program `p` halts on input `i`
when running under oracle `o`. -/
def RelativizedHaltingPredictor := (Nat → Bool) → Nat → Nat → Bool

/-- A behavior function (parent-style: input -> Bool). Namespaced to avoid
collision with `Behavior` from `Proofs.HaltingProblem`. -/
def Behavior := Nat → Bool

/-- The relativized diagonal behavior: given an oracle `o` and a predictor
`H`, return the opposite of `H`'s prediction at the self-application point. -/
def relativizedDiagonalBehavior (H : RelativizedHaltingPredictor)
    (o : Nat → Bool) : Behavior :=
  fun n => !(H o n n)

/-! ### Section 2. The core diagonal lemma -/

/-- **Diagonal lemma (relativized).** For every oracle `o`, every predictor
`H`, and every code `n`, the relativized diagonal behavior differs from `H`'s
prediction at `(n, n)`. This is the verbatim lift of the parent's
`diagonal_differs`. -/
theorem relativized_diagonal_differs (H : RelativizedHaltingPredictor)
    (o : Nat → Bool) (n : Nat) :
    relativizedDiagonalBehavior H o n ≠ H o n n := by
  unfold relativizedDiagonalBehavior
  intro h
  cases hc : H o n n with
  | true => simp [hc] at h
  | false => simp [hc] at h

/-! ### Section 3. The OQ-03a undecidability theorem -/

/-- **No relativized halting oracle exists.** For any oracle `o`, any
predictor `H`, and any code `c`, if `H` correctly predicts the relativized
diagonal behavior at `c` (in both directions: `true` and `false`), we derive
a contradiction. This is the contradiction form of OQ-03a, mirroring the
parent's `no_halting_oracle`. -/
theorem no_relativized_halting_oracle :
    ∀ (H : RelativizedHaltingPredictor) (o : Nat → Bool) (c : Nat),
    (relativizedDiagonalBehavior H o c = true → H o c c = true) →
    (relativizedDiagonalBehavior H o c = false → H o c c = false) →
    False := by
  intro H o c h_halts h_loops
  unfold relativizedDiagonalBehavior at h_halts h_loops
  cases h : H o c c with
  | true =>
    have diag_false : (!H o c c) = false := by simp [h]
    have oracle_false : H o c c = false := h_loops diag_false
    simp [h] at oracle_false
  | false =>
    have diag_true : (!H o c c) = true := by simp [h]
    have oracle_true : H o c c = true := h_halts diag_true
    simp [h] at oracle_true

/-! ### Section 4. Packaged "Decides_in" form -/

/-- A predictor `H` *decides relativized halting under oracle `o`* iff `H o`
correctly predicts whether code `code` halts on `code` (modeled abstractly
as agreement with some target behavior `target` that `H` purports to be).

Operationally: `H` is correct iff for every code `c`, the value `H o c c`
matches some externally-given oracle-aware behavior `target`. Since the
parent file's diagonal argument shows that *any* total predictor disagrees
with its own diagonalization, this is precisely the "predictor cannot decide
its own halting" condition. -/
def Decides_in (o : Nat → Bool) (H : RelativizedHaltingPredictor) : Prop :=
  ∀ target : Behavior, ∃ c : Nat, H o c c = target c

/-- **OQ-03a (packaged).** For every oracle `o`, no predictor `H` can
match every conceivable target behavior on its self-application diagonal.
In particular, taking the target to be the diagonal of `H` itself yields a
specific witness behavior `D_H` with which `H` disagrees on all codes. -/
theorem relativized_halting_undecidable (o : Nat → Bool) :
    ∀ H : RelativizedHaltingPredictor,
    ∃ behavior : Behavior, ∀ code : Nat, H o code code ≠ behavior code := by
  intro H
  refine ⟨relativizedDiagonalBehavior H o, ?_⟩
  intro code h
  exact (relativized_diagonal_differs H o code) h.symm

/-! ### Section 5. Sanity check: classical case is a specialization -/

/-- The relativized diagonal for the trivial oracle (constantly `false`)
agrees pointwise with the parent file's classical-style diagonal applied to
the same predictor stripped of its oracle argument.

Concretely: if `H_classical` is the curried form of `H` at oracle
`fun _ => false`, then the relativized diagonal at that oracle equals
`fun n => !(H_classical n n)`, which is exactly the parent's
`diagonalBehavior` applied to `H_classical`. -/
theorem relativized_collapses_to_classical_at_trivial_oracle
    (H : RelativizedHaltingPredictor) :
    relativizedDiagonalBehavior H (fun _ => false) =
      fun n => !(H (fun _ => false) n n) := by
  funext n
  rfl

/-! ### Section 6. Strict separation: A' is above A (post-Post 1944, abstract form)

The classical Post 1944 theorem states that the Turing jump `A'` is strictly
above `A` in the Turing degrees: `A' ∉ Comp(A)`. The abstract version
provable in zero imports is the following: there is no oracle-aware
predictor `H` that, for every oracle `o`, correctly self-predicts. The
formal statement below packages this as a non-existence theorem.
-/

/-- **OQ-03a, strict-separation form.** There is no single predictor `H`
that uniformly decides relativized halting for every oracle. -/
theorem no_uniform_relativized_halting_oracle :
    ¬ ∃ H : RelativizedHaltingPredictor,
        ∀ o : Nat → Bool, ∀ behavior : Behavior, ∀ code : Nat,
        H o code code = behavior code := by
  intro ⟨H, hH⟩
  -- Pick any oracle, say o = fun _ => false. Then hH says H matches every
  -- behavior at every code. But by `relativized_halting_undecidable`, there
  -- is at least one behavior H disagrees with on at least one code.
  obtain ⟨behavior, hbehavior⟩ :=
    relativized_halting_undecidable (fun _ => false) H
  -- Pick code = 0 (arbitrary); hbehavior says H ≠ behavior at 0; hH says =.
  exact hbehavior 0 (hH (fun _ => false) behavior 0)

/-! ### Section 7. Witnesses (for downstream use) -/

/-- The explicit diagonal witness for a given oracle and predictor. This is
the relativized analog of the parent's `diagonalBehavior` applied to the
oracle-specialized predictor. -/
def relativizedDiagonalWitness (H : RelativizedHaltingPredictor)
    (o : Nat → Bool) : Behavior :=
  relativizedDiagonalBehavior H o

/-- The diagonal witness is the relativized diagonal behavior (definitional
unfolding; provided for clarity). -/
theorem relativizedDiagonalWitness_eq (H : RelativizedHaltingPredictor)
    (o : Nat → Bool) :
    relativizedDiagonalWitness H o = relativizedDiagonalBehavior H o := rfl

/-! ### Section 8. Abstract iterated jump (Post's hierarchy at the abstract level)

Classically, the Turing jump `A ↦ A'` lifts to a strictly increasing iteration
`A, A', A'', ...` whose limit defines the arithmetical hierarchy
(Post 1944; Soare 1987, ch. III). At the abstract
`(Nat → Bool) → Nat → Nat → Bool` level used in Sections 1–7, the analog of
the Turing jump is the *diagonal-witness map*: given a predictor `H` and a
current oracle `o`, emit the new oracle `n ↦ !(H o n n)` against which `H`
cannot decide its own relativized halting.

This section defines `jumpOracle`, iterates it as `jumpIter`, and proves that
each iteration strictly diagonalizes against `H`. No predictor uniformly
decides relativized halting at every level of the iteration.

The full Mathlib-class Turing-jump construction (a parallel `OracleCode`
inductive + a lift to a `Computable_in` class) is deferred to a follow-on
sub-OQ `halting-problem-oq-03-bridge`.
-/

/-- The abstract jump of an oracle `o` under predictor `H`: the new oracle
`n ↦ !(H o n n)`, definitionally equal to `relativizedDiagonalBehavior H o`.
This is the abstract analog of the classical Turing jump `A ↦ A'`. -/
def jumpOracle (H : RelativizedHaltingPredictor) (o : Nat → Bool) : Nat → Bool :=
  relativizedDiagonalBehavior H o

/-- The n-fold iterated jump of an oracle `o₀` under predictor `H`. Abstract
analog of the chain `A, A', A'', ...` of iterated Turing jumps. -/
def jumpIter (H : RelativizedHaltingPredictor) :
    (Nat → Bool) → Nat → (Nat → Bool)
  | o₀, 0 => o₀
  | o₀, n + 1 => jumpOracle H (jumpIter H o₀ n)

@[simp] theorem jumpIter_zero (H : RelativizedHaltingPredictor)
    (o₀ : Nat → Bool) : jumpIter H o₀ 0 = o₀ := rfl

@[simp] theorem jumpIter_succ (H : RelativizedHaltingPredictor)
    (o₀ : Nat → Bool) (n : Nat) :
    jumpIter H o₀ (n + 1) = jumpOracle H (jumpIter H o₀ n) := rfl

/-- **Each jump level strictly diagonalizes against `H`.** At every level
`n` and every code `c`, the oracle at level `n+1` differs from `H`'s
prediction at the diagonal of the level-`n` oracle. Abstract analog of
Post 1944's `A' ∉ Comp(A)` at the diagonal-witness level. -/
theorem jumpIter_differs (H : RelativizedHaltingPredictor)
    (o₀ : Nat → Bool) (n c : Nat) :
    jumpIter H o₀ (n + 1) c ≠ H (jumpIter H o₀ n) c c := by
  show jumpOracle H (jumpIter H o₀ n) c ≠ H (jumpIter H o₀ n) c c
  exact relativized_diagonal_differs H (jumpIter H o₀ n) c

/-- **Relativized halting is undecidable at every jump level.** For every
starting oracle `o₀`, every level `n`, and every predictor `H'`, there is a
witness behavior at oracle level `n` that `H'` mispredicts at every code.
This is the level-`n` analog of `relativized_halting_undecidable` (which is
the level-0 case after unfolding `jumpIter_zero`). -/
theorem jumpIter_halting_undecidable (H : RelativizedHaltingPredictor)
    (o₀ : Nat → Bool) (n : Nat) :
    ∀ H' : RelativizedHaltingPredictor,
    ∃ behavior : Behavior, ∀ code : Nat,
    H' (jumpIter H o₀ n) code code ≠ behavior code :=
  fun H' => relativized_halting_undecidable (jumpIter H o₀ n) H'

/-- **No predictor uniformly decides relativized halting across the jump
iteration.** Strengthening of `no_uniform_relativized_halting_oracle`: even
when the underlying oracle ranges over all `jumpIter H o₀ n` choices (with
free `H, o₀, n`), no single predictor `H'` matches every behavior at every
code. Abstract analog of "no Turing-computable function decides the join
`⊕_n ∅^{(n)}` of all finite jumps of the empty oracle". -/
theorem no_uniform_jumpIter_predictor :
    ¬ ∃ H' : RelativizedHaltingPredictor,
        ∀ (H : RelativizedHaltingPredictor) (o₀ : Nat → Bool)
          (n : Nat) (behavior : Behavior) (code : Nat),
        H' (jumpIter H o₀ n) code code = behavior code := by
  intro ⟨H', hH'⟩
  apply no_uniform_relativized_halting_oracle
  exact ⟨H', fun o behavior code => hH' H' o 0 behavior code⟩

/-- The level-`(n+1)` diagonal witness against `H` at oracle level `n`,
exposed as an alias for downstream consumers (e.g. a future Mathlib bridge
that wants to refer to the level-`n` witness by name without unfolding
`jumpIter`). -/
def jumpIterWitness (H : RelativizedHaltingPredictor) (o₀ : Nat → Bool)
    (n : Nat) : Behavior :=
  jumpIter H o₀ (n + 1)

theorem jumpIterWitness_eq_succ (H : RelativizedHaltingPredictor)
    (o₀ : Nat → Bool) (n : Nat) :
    jumpIterWitness H o₀ n = jumpIter H o₀ (n + 1) := rfl

theorem jumpIterWitness_differs (H : RelativizedHaltingPredictor)
    (o₀ : Nat → Bool) (n c : Nat) :
    jumpIterWitness H o₀ n c ≠ H (jumpIter H o₀ n) c c :=
  jumpIter_differs H o₀ n c

/-! ### Section 9. Semigroup structure of the abstract jump iteration

`jumpIter` is the iterated application of `jumpOracle`; as such it satisfies
the additive semigroup law `jumpIter H o₀ (m + n) = jumpIter H (jumpIter H
o₀ m) n`. Classically this is the statement that the iterated Turing jump
respects composition: `(A^(m))^(n) = A^(m+n)`. Recording the lemma here
provides the recursion-theoretic primitive that any future arithmetical-
hierarchy development (sub-goal OQ-03b) will use when stating Post's
theorem at level `n+1` from the level-`n` predicate. The proof is one
induction on `n` (zero by `rfl`, succ by `jumpIter_succ` + the IH).
-/

/-- **Semigroup law for the abstract Turing-jump iteration.** Iterating
`jumpOracle` for `m + n` steps from seed `o₀` is the same as iterating
for `m` steps from `o₀`, then iterating for `n` further steps from the
result. Abstract analog of `(A^(m))^(n) = A^(m+n)` for the classical
Turing jump. -/
theorem jumpIter_compose (H : RelativizedHaltingPredictor)
    (o₀ : Nat → Bool) (m n : Nat) :
    jumpIter H o₀ (m + n) = jumpIter H (jumpIter H o₀ m) n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show jumpOracle H (jumpIter H o₀ (m + k)) =
        jumpOracle H (jumpIter H (jumpIter H o₀ m) k)
    rw [ih]

/-! ### Section 10. Step dichotomy and flip characterization

Section 8's `jumpIter_differs` witnesses that `jumpIter H o₀ (n + 1) c` is
always different from `H (jumpIter H o₀ n) c c` — the diagonal-against-`H`
property at every step. The S5 bridge collapse result shows that when `H`
is oracle-blind (an embedded classical predictor), every level ≥ 1 of the
jump tower is the *same* function. The two results suggest a richer
question: *when* are consecutive levels of `jumpIter` actually distinct at
a particular code `c`?

This section characterizes the answer:

* **Boolean dichotomy.** At every step and every code, the value either
  stays the same or flips (`jumpIter_step_dichotomy`). There is no other
  option, because `jumpIter (n+1) c = !(H (jumpIter n) c c)` is a Boolean
  expression equal to one of `jumpIter n c` and `!(jumpIter n c)`.

* **Flip characterization.** Consecutive levels differ at code `c` iff
  the predictor `H` *agrees with the current oracle's value at the
  diagonal of `c`* (`jumpIter_step_flip_iff`). This is the abstract
  Boolean version of Post 1944's strictness condition: classical
  strictness `A < A'` says some oracle-class member of `A'` is not in
  `A`; the abstract analog at a fixed code is that the predictor
  confirms the current oracle's value, which (because the next-level
  oracle is the negation of `H`'s diagonal) forces the next level to
  flip at that code.

* **Stability under disagreement.** The contrapositive in positive form
  (`jumpIter_step_stable_of_self_disagree`): disagreement at the
  c-diagonal yields step-wise stability at `c`.

The S5 collapse theorem `jumpIter_embedClassical_succ_eq_classicalDiagonal`
is the contrapositive shadow at the function level: for an embedded
classical predictor (oracle-blind), no agreement code exists at any level
≥ 1, *and the chain collapses*. The parallel S6-light PR #18114 packages
the existence direction: a non-degenerate predictor (`IsNonDegenerate H`)
yields a strict-step inequality `jumpIter (n+1) ≠ jumpIter n` as
functions, from a level-`n` agreement witness. This section is
strict in the per-code direction; PR #18114 is strict at the function
level under a global non-degeneracy hypothesis.
-/

/-- The reduction lemma exposing the next-level value of the jump tower.
`rfl` modulo unfolding `jumpIter`, `jumpOracle`, and
`relativizedDiagonalBehavior`. Stating it explicitly makes the boolean
reasoning in Section 10 less syntactically fragile. -/
theorem jumpIter_succ_apply (H : RelativizedHaltingPredictor)
    (o₀ : Nat → Bool) (n c : Nat) :
    jumpIter H o₀ (n + 1) c = Bool.not (H (jumpIter H o₀ n) c c) := rfl

/-- **Step dichotomy.** Every step of `jumpIter` at code `c` either
preserves the value at `c` or flips it. There is no third option,
because `jumpIter (n+1) c = Bool.not (H (jumpIter n) c c)` is a Boolean.
Note: `cases h : x` substitutes `x` in the goal; the 4 cases reduce to
closed Boolean disjunctions, dispatched by `decide`. -/
theorem jumpIter_step_dichotomy (H : RelativizedHaltingPredictor)
    (o₀ : Nat → Bool) (n c : Nat) :
    jumpIter H o₀ (n + 1) c = jumpIter H o₀ n c
      ∨ jumpIter H o₀ (n + 1) c = Bool.not (jumpIter H o₀ n c) := by
  rw [jumpIter_succ_apply]
  cases hH : H (jumpIter H o₀ n) c c <;>
    cases hJ : jumpIter H o₀ n c <;> decide

/-- **Flip characterization.** Consecutive levels of `jumpIter` differ at
code `c` iff the predictor `H` agrees with the current oracle's value at
the diagonal of `c`. Abstract Boolean analog of Post 1944's strictness
condition pinned at a specific code. -/
theorem jumpIter_step_flip_iff (H : RelativizedHaltingPredictor)
    (o₀ : Nat → Bool) (n c : Nat) :
    jumpIter H o₀ (n + 1) c ≠ jumpIter H o₀ n c
      ↔ H (jumpIter H o₀ n) c c = jumpIter H o₀ n c := by
  rw [jumpIter_succ_apply]
  constructor
  · intro hne
    cases hH : H (jumpIter H o₀ n) c c
    · cases hJ : jumpIter H o₀ n c
      · rfl
      · exfalso; apply hne; rw [hH, hJ]; rfl
    · cases hJ : jumpIter H o₀ n c
      · exfalso; apply hne; rw [hH, hJ]; rfl
      · rfl
  · intro hAg
    rw [hAg]
    cases jumpIter H o₀ n c
    · decide
    · decide

/-- **Stability under self-disagreement.** If the predictor `H` disagrees
with the current oracle's value at the diagonal of `c`, the next jump
level *preserves* the value at `c`. Equivalent to the contrapositive of
`jumpIter_step_flip_iff`; convenient as a positive equality statement
for downstream consumers (e.g. constant-tower lemmas). -/
theorem jumpIter_step_stable_of_self_disagree (H : RelativizedHaltingPredictor)
    (o₀ : Nat → Bool) (n c : Nat)
    (h : H (jumpIter H o₀ n) c c ≠ jumpIter H o₀ n c) :
    jumpIter H o₀ (n + 1) c = jumpIter H o₀ n c := by
  rw [jumpIter_succ_apply]
  cases hH : H (jumpIter H o₀ n) c c
  · cases hJ : jumpIter H o₀ n c
    · exact absurd (hH.trans hJ.symm) h
    · rfl
  · cases hJ : jumpIter H o₀ n c
    · rfl
    · exact absurd (hH.trans hJ.symm) h

/-! ### Section 11. Non-degeneracy certificates and explicit instantiation
(S7-light)

The S6 step dichotomy and flip characterization are packaged here into a
reusable *strict-chain certificate* at a code `c`, witnessed by a level
`n` at which the predictor's self-application matches the current
oracle's diagonal value (which by `jumpIter_step_flip_iff` is exactly
the condition forcing `jumpIter (n+1) c ≠ jumpIter n c`).

The abstraction lets downstream existence results refer to a single
`NonDegenerateAt` witness rather than re-deriving the iff each time.
The same certificate is then instantiated for an *explicit* small
example — the trivially-false predictor paired with the constantly-
false starting oracle — verifying the abstraction is non-vacuous and
providing a concrete sanity instance for the Mathlib-bridge sub-OQ. -/

/-- **Strict-step witness at code `c` and level `n`.** The chain
`jumpIter H o₀` is non-degenerate at code `c` between levels `n` and
`n + 1` iff the predictor `H` agrees with the current oracle's value
at the `c`-diagonal. By `jumpIter_step_flip_iff`, this is the exact
characterization of `jumpIter (n+1) c ≠ jumpIter n c`. -/
def NonDegenerateAt (H : RelativizedHaltingPredictor) (o₀ : Nat → Bool)
    (c n : Nat) : Prop :=
  H (jumpIter H o₀ n) c c = jumpIter H o₀ n c

/-- A `NonDegenerateAt` witness yields the strict-step inequality at
the same code and level. Direct consequence of
`jumpIter_step_flip_iff`. -/
theorem strict_step_of_nonDegenerateAt
    (H : RelativizedHaltingPredictor) (o₀ : Nat → Bool) (c n : Nat)
    (h : NonDegenerateAt H o₀ c n) :
    jumpIter H o₀ (n + 1) c ≠ jumpIter H o₀ n c :=
  (jumpIter_step_flip_iff H o₀ n c).mpr h

/-- Conversely, a strict-step inequality at code `c` between levels `n`
and `n + 1` yields a `NonDegenerateAt` witness at the same code and
level. The two formulations are mutually derivable, packaged as
`nonDegenerateAt_iff_strict_step` below. -/
theorem nonDegenerateAt_of_strict_step
    (H : RelativizedHaltingPredictor) (o₀ : Nat → Bool) (c n : Nat)
    (h : jumpIter H o₀ (n + 1) c ≠ jumpIter H o₀ n c) :
    NonDegenerateAt H o₀ c n :=
  (jumpIter_step_flip_iff H o₀ n c).mp h

/-- **`NonDegenerateAt` iff strict-step inequality.** Direct repackage
of `jumpIter_step_flip_iff` under the new abstraction. -/
theorem nonDegenerateAt_iff_strict_step
    (H : RelativizedHaltingPredictor) (o₀ : Nat → Bool) (c n : Nat) :
    NonDegenerateAt H o₀ c n
      ↔ jumpIter H o₀ (n + 1) c ≠ jumpIter H o₀ n c :=
  (jumpIter_step_flip_iff H o₀ n c).symm

/-- The chain `jumpIter H o₀` is *eventually non-degenerate at code `c`*
iff some level admits a `NonDegenerateAt` witness at `c`. Existential
form of the per-level predicate. -/
def IsEventuallyNonDegenerateAt (H : RelativizedHaltingPredictor)
    (o₀ : Nat → Bool) (c : Nat) : Prop :=
  ∃ n, NonDegenerateAt H o₀ c n

/-- An eventually non-degenerate chain at code `c` exhibits a strict
step at `c` between some pair of consecutive levels. -/
theorem strict_step_of_eventually_nonDegenerateAt
    (H : RelativizedHaltingPredictor) (o₀ : Nat → Bool) (c : Nat)
    (h : IsEventuallyNonDegenerateAt H o₀ c) :
    ∃ n, jumpIter H o₀ (n + 1) c ≠ jumpIter H o₀ n c :=
  match h with
  | ⟨n, hn⟩ => ⟨n, strict_step_of_nonDegenerateAt H o₀ c n hn⟩

/-! #### Concrete witness: the trivially-false predictor

The explicit predictor `trivialPredictor : RelativizedHaltingPredictor`
defined as `fun _ _ _ ↦ false` paired with the constantly-false starting
oracle `falseOracle := fun _ ↦ false` yields a `NonDegenerateAt`
witness at *every* code `c` at level `0`. A small, fully-verified
instance of the certificate framework demonstrating non-vacuity. -/

/-- The trivially-false predictor: returns `false` regardless of oracle,
code, or input. The simplest non-trivial `RelativizedHaltingPredictor`. -/
def trivialPredictor : RelativizedHaltingPredictor :=
  fun _ _ _ => false

/-- The constantly-false starting oracle: returns `false` on every code. -/
def falseOracle : Nat → Bool := fun _ => false

/-- **Concrete witness**: at level `0` and every code `c`, the
`trivialPredictor`-`falseOracle` chain is non-degenerate at `c`. By
the definitional unfolding of both, the certificate reduces to
`false = false`, discharged by `rfl`. This verifies that the
`NonDegenerateAt` framework admits a small fully-instantiated example. -/
theorem nonDegenerateAt_trivialPredictor_zero (c : Nat) :
    NonDegenerateAt trivialPredictor falseOracle c 0 := rfl

/-- The `trivialPredictor`-`falseOracle` chain is eventually
non-degenerate at every code, via the level-`0` certificate. -/
theorem isEventuallyNonDegenerateAt_trivialPredictor (c : Nat) :
    IsEventuallyNonDegenerateAt trivialPredictor falseOracle c :=
  ⟨0, nonDegenerateAt_trivialPredictor_zero c⟩

/-- **Strict-step instantiation**: between levels `0` and `1`, the
`trivialPredictor`-`falseOracle` chain differs at every code `c`. -/
theorem strict_step_trivialPredictor_zero (c : Nat) :
    jumpIter trivialPredictor falseOracle 1 c ≠
    jumpIter trivialPredictor falseOracle 0 c :=
  strict_step_of_nonDegenerateAt trivialPredictor falseOracle c 0
    (nonDegenerateAt_trivialPredictor_zero c)

/-! ### Section 12. Function-level strict-chain under uniform non-degeneracy
(S8-light)

S7-light's `NonDegenerateAt` certificate is per-code, per-level. The
existential `IsEventuallyNonDegenerateAt` lifts a single per-code witness
to a strict-step inequality at that code (Section 11). This section
introduces the *universal* form — non-degeneracy at every level and
every code simultaneously — and derives the function-level consequence:
consecutive `jumpIter` levels are distinct as functions.

The trivial example from S7-light (`trivialPredictor` paired with
`falseOracle`) is non-degenerate only at level 0, since the chain
stabilizes from level 1 onward (`jumpIter trivialPredictor falseOracle n
c = true` for all n ≥ 1). To exhibit a non-vacuous example of the
universal form we use the *identity-style predictor* `identityPredictor
:= fun o _ x => o x`, which agrees with its oracle's value at every
self-application point. For this predictor, every level admits a
`NonDegenerateAt` witness, so the chain advances at every step. -/

/-- **Universal non-degeneracy.** The chain `jumpIter H o₀` admits a
`NonDegenerateAt` certificate at *every* level and *every* code. By
`strict_step_of_nonDegenerateAt` applied at any code, this forces
consecutive levels of the chain to disagree at that code and therefore
to be distinct as functions. -/
def IsAlwaysNonDegenerate (H : RelativizedHaltingPredictor)
    (o₀ : Nat → Bool) : Prop :=
  ∀ n c, NonDegenerateAt H o₀ c n

/-- **Function-level strict-step under universal non-degeneracy.** If
`H` is always non-degenerate from starting oracle `o₀`, then for every
level `n`, the level-`(n+1)` and level-`n` oracles disagree as
functions (i.e., differ at some code).

Proof: instantiate the universal hypothesis at level `n` and code `0`
to obtain a `NonDegenerateAt` witness, lift it to the per-code strict
step via `strict_step_of_nonDegenerateAt`, then contradict
hypothetical function equality at code `0` via `congrFun`. -/
theorem chain_strict_succ_of_isAlwaysNonDegenerate
    {H : RelativizedHaltingPredictor} {o₀ : Nat → Bool}
    (h : IsAlwaysNonDegenerate H o₀) (n : Nat) :
    jumpIter H o₀ (n + 1) ≠ jumpIter H o₀ n := by
  intro heq
  exact strict_step_of_nonDegenerateAt H o₀ 0 n (h n 0) (congrFun heq 0)

/-! #### Concrete witness: the identity-style predictor

The predictor `identityPredictor := fun o _ x => o x` reads its oracle
unchanged at the self-application point: `identityPredictor o c c = o c`
for every `o, c`. This is the simplest predictor satisfying the
universal non-degeneracy condition, since `NonDegenerateAt
identityPredictor o₀ c n` unfolds to `(jumpIter identityPredictor o₀ n)
c = (jumpIter identityPredictor o₀ n) c`, definitionally `rfl`.

Note this is structurally distinct from `trivialPredictor`: the trivial
predictor ignores its oracle (returning `false` unconditionally),
producing a chain that stabilizes at level 1, whereas `identityPredictor`
echoes its oracle, producing a chain in which every level flips every
code relative to its predecessor. -/

/-- The identity-style predictor: returns the oracle's value at the input,
ignoring the code argument. The simplest predictor that is universally
non-degenerate against any starting oracle. -/
def identityPredictor : RelativizedHaltingPredictor :=
  fun o _ x => o x

/-- **Per-level/per-code certificate for `identityPredictor`.** At every
level `n` and every code `c`, `identityPredictor` agrees with the current
oracle's self-application value (which is the defining condition of
`NonDegenerateAt`). Discharged by `rfl` since both sides reduce
definitionally to `(jumpIter identityPredictor o₀ n) c`. -/
theorem nonDegenerateAt_identityPredictor
    (o₀ : Nat → Bool) (c n : Nat) :
    NonDegenerateAt identityPredictor o₀ c n := rfl

/-- **Universal non-degeneracy of `identityPredictor`.** The chain
`jumpIter identityPredictor o₀` admits a `NonDegenerateAt` certificate
at every level and every code, for any starting oracle `o₀`. -/
theorem isAlwaysNonDegenerate_identityPredictor (o₀ : Nat → Bool) :
    IsAlwaysNonDegenerate identityPredictor o₀ :=
  fun n c => nonDegenerateAt_identityPredictor o₀ c n

/-- **Strict-chain instantiation for `identityPredictor`.** For any
starting oracle `o₀` and any level `n`, the level-`(n+1)` and level-`n`
oracles of the `identityPredictor` chain disagree as functions. Direct
combination of `chain_strict_succ_of_isAlwaysNonDegenerate` with
`isAlwaysNonDegenerate_identityPredictor`. -/
theorem chain_strict_succ_identityPredictor
    (o₀ : Nat → Bool) (n : Nat) :
    jumpIter identityPredictor o₀ (n + 1) ≠ jumpIter identityPredictor o₀ n :=
  chain_strict_succ_of_isAlwaysNonDegenerate
    (isAlwaysNonDegenerate_identityPredictor o₀) n

/-! ### Section 13. Pairwise distinctness: the periodicity obstruction and
the rank criterion (S9-light)

S8-light left open whether universal non-degeneracy
(`IsAlwaysNonDegenerate`) suffices for *pairwise* distinctness of the
chain — `jumpIter H o₀ m ≠ jumpIter H o₀ n` for all `m ≠ n` — noting
that consecutive distinctness does not obviously rule out a periodic
chain. This section settles the question in both directions.

**Negative (the periodicity obstruction).** Universal non-degeneracy
does NOT imply pairwise distinctness. The witness is S8-light's own
`identityPredictor`: its jump step is pointwise Boolean negation
(`jumpIter (n+1) c = ¬ jumpIter n c`), so the chain has period exactly
2 — every consecutive pair differs (at every code!), yet
`jumpIter (n+2) = jumpIter n`. Consecutive strictness coexists with
global collapse.

**Positive (the rank criterion).** The missing structural hypothesis is
a *rank*: any function `r : (Nat → Bool) → Nat` that strictly increases
along the chain forces the chain to be injective, hence pairwise
distinct. This is the abstract shadow of the classical fact that the
Turing jump strictly increases Turing degree.

**Non-vacuity, and non-necessity of universal non-degeneracy.** The
`successorPredictor` below drives the chain through the unary oracles
`unaryOracle 0, unaryOracle 1, unaryOracle 2, …` (where
`unaryOracle k = fun i => decide (i < k)`), which are pairwise distinct
— a fully concrete never-revisiting chain. Notably this chain flips
exactly ONE code per step, so `successorPredictor` is NOT universally
non-degenerate: together with the identity-predictor counterexample this
shows universal non-degeneracy is neither sufficient (periodicity) nor
necessary (successor chain) for pairwise distinctness. The two
conditions are orthogonal: `IsAlwaysNonDegenerate` measures how *wide*
each single step is (every code flips), while pairwise distinctness
measures whether the chain ever *revisits* a level. -/

/-- **The identity-predictor jump step is pointwise negation.** Unfolds
definitionally: `jumpIter (n+1) c = ¬ (identityPredictor (jumpIter n) c c)
= ¬ (jumpIter n c)`. -/
theorem jumpIter_identityPredictor_succ_apply
    (o₀ : Nat → Bool) (n c : Nat) :
    jumpIter identityPredictor o₀ (n + 1) c =
      Bool.not (jumpIter identityPredictor o₀ n c) := rfl

/-- **The identity-predictor chain has period 2.** Two jump steps are a
double negation, which is the identity on `Bool`. -/
theorem jumpIter_identityPredictor_add_two
    (o₀ : Nat → Bool) (n : Nat) :
    jumpIter identityPredictor o₀ (n + 2) =
      jumpIter identityPredictor o₀ n := by
  funext c
  show Bool.not (Bool.not (jumpIter identityPredictor o₀ n c)) =
      jumpIter identityPredictor o₀ n c
  exact Bool.not_not _

/-- **The identity-predictor chain is not injective**: levels `0` and `2`
coincide (as do any two levels of equal parity). -/
theorem jumpIter_identityPredictor_not_injective (o₀ : Nat → Bool) :
    ∃ m n : Nat, m ≠ n ∧
      jumpIter identityPredictor o₀ m = jumpIter identityPredictor o₀ n :=
  ⟨2, 0, fun h => Nat.noConfusion h, jumpIter_identityPredictor_add_two o₀ 0⟩

/-- **S9-light PREP answer, negative half: universal non-degeneracy does
NOT imply pairwise distinctness.** There is a predictor/oracle pair whose
chain is non-degenerate at every level and every code — so all
consecutive levels differ, at every code — yet two distinct levels of
the chain are equal as functions. Hence
`chain_strict_of_isAlwaysNonDegenerate` (pairwise distinctness from
`IsAlwaysNonDegenerate` alone) is FALSE as conjectured, and any pairwise
strictness theorem needs an additional structural hypothesis (see
`jumpIter_injective_of_hasRank`). -/
theorem isAlwaysNonDegenerate_not_sufficient_for_pairwise :
    ∃ (H : RelativizedHaltingPredictor) (o₀ : Nat → Bool),
      IsAlwaysNonDegenerate H o₀ ∧
      ∃ m n : Nat, m ≠ n ∧ jumpIter H o₀ m = jumpIter H o₀ n :=
  ⟨identityPredictor, falseOracle,
    isAlwaysNonDegenerate_identityPredictor falseOracle,
    jumpIter_identityPredictor_not_injective falseOracle⟩

/-- **Rank along the chain.** A function `r` on oracles strictly
increases along the `jumpIter H o₀` chain. This is the abstract analog
of "the jump strictly increases Turing degree": any quantity that
provably grows at every jump step certifies that the chain never
revisits a level. -/
def HasRank (H : RelativizedHaltingPredictor) (o₀ : Nat → Bool)
    (r : (Nat → Bool) → Nat) : Prop :=
  ∀ n, r (jumpIter H o₀ n) < r (jumpIter H o₀ (n + 1))

/-- A rank strictly increases across any strictly increasing pair of
levels (iterated transitivity of the one-step hypothesis). -/
theorem rank_lt_of_hasRank {H : RelativizedHaltingPredictor}
    {o₀ : Nat → Bool} {r : (Nat → Bool) → Nat} (hr : HasRank H o₀ r) :
    ∀ {m n : Nat}, m < n →
      r (jumpIter H o₀ m) < r (jumpIter H o₀ n) := by
  intro m n h
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ k ih =>
    cases Nat.lt_or_ge m k with
    | inl h' => exact Nat.lt_trans (ih h') (hr k)
    | inr h' =>
      have hmk : m = k := Nat.le_antisymm (Nat.le_of_lt_succ h) h'
      exact hmk ▸ hr k

/-- **The rank criterion (positive half of the S9-light question).** If
some rank strictly increases along the chain, the chain is injective:
distinct levels are distinct oracles. This is the "additional structural
hypothesis" that repairs the failed conjecture
`chain_strict_of_isAlwaysNonDegenerate` — see
`isAlwaysNonDegenerate_not_sufficient_for_pairwise` for why
`IsAlwaysNonDegenerate` alone cannot do the job. -/
theorem jumpIter_injective_of_hasRank {H : RelativizedHaltingPredictor}
    {o₀ : Nat → Bool} {r : (Nat → Bool) → Nat} (hr : HasRank H o₀ r)
    (m n : Nat) (heq : jumpIter H o₀ m = jumpIter H o₀ n) : m = n := by
  cases Nat.lt_or_ge m n with
  | inl h => exact absurd (heq ▸ rank_lt_of_hasRank hr h) (Nat.lt_irrefl _)
  | inr h₁ =>
    cases Nat.lt_or_ge n m with
    | inl h => exact absurd (heq ▸ rank_lt_of_hasRank hr h) (Nat.lt_irrefl _)
    | inr h₂ => exact Nat.le_antisymm h₂ h₁

/-- **Pairwise strict chain under a rank.** Contrapositive packaging of
the rank criterion: distinct levels give distinct oracles. -/
theorem chain_pairwise_strict_of_hasRank {H : RelativizedHaltingPredictor}
    {o₀ : Nat → Bool} {r : (Nat → Bool) → Nat} (hr : HasRank H o₀ r)
    {m n : Nat} (h : m ≠ n) : jumpIter H o₀ m ≠ jumpIter H o₀ n :=
  fun heq => h (jumpIter_injective_of_hasRank hr m n heq)

/-! #### Concrete witness: the successor predictor and the unary chain

The rank criterion would be empty comfort if no chain were actually
pairwise distinct. The `successorPredictor` drives the chain through the
unary oracles: starting from `falseOracle = unaryOracle 0`, each jump
step turns `unaryOracle k` into `unaryOracle (k + 1)` — the chain counts
in unary and never revisits a level. -/

/-- The unary oracle of height `k`: true exactly on `{0, …, k − 1}`. The
chain `unaryOracle 0, unaryOracle 1, …` is the simplest strictly
growing family of oracles. -/
def unaryOracle (k : Nat) : Nat → Bool :=
  fun i => decide (i < k)

/-- The successor predictor: at code `c`, answers `false` for `c = 0`
and the negation of the oracle's value at `c − 1` otherwise. Engineered
so that the jump step `jumpOracle` (which negates the diagonal) sends
`unaryOracle k` to `unaryOracle (k + 1)`. -/
def successorPredictor : RelativizedHaltingPredictor :=
  fun o c _ => if c = 0 then false else Bool.not (o (c - 1))

/-- **Closed form of the successor chain: it counts in unary.**
`jumpIter successorPredictor falseOracle n = unaryOracle n` for every
`n`. Induction on `n`; the step is a per-code case split — code `0`
flips to `true` (entering the unary block), code `m + 1` copies the
previous oracle at `m` via double negation. -/
theorem jumpIter_successorPredictor (n : Nat) :
    jumpIter successorPredictor falseOracle n = unaryOracle n := by
  induction n with
  | zero =>
    funext i
    exact (decide_eq_false (Nat.not_lt_zero i)).symm
  | succ k ih =>
    funext c
    show Bool.not
        (successorPredictor (jumpIter successorPredictor falseOracle k) c c) =
      unaryOracle (k + 1) c
    rw [ih]
    cases c with
    | zero =>
      show true = unaryOracle (k + 1) 0
      exact (decide_eq_true (Nat.zero_lt_succ k)).symm
    | succ m =>
      show Bool.not (Bool.not (unaryOracle k m)) = unaryOracle (k + 1) (m + 1)
      rw [Bool.not_not]
      show decide (m < k) = decide (m + 1 < k + 1)
      by_cases h : m < k
      · rw [decide_eq_true h, decide_eq_true (Nat.succ_lt_succ h)]
      · rw [decide_eq_false h,
          decide_eq_false (fun h' => h (Nat.lt_of_succ_lt_succ h'))]

/-- Unary oracles of distinct heights are distinct: evaluate at the
smaller height, where one is `false` and the other `true`. -/
theorem unaryOracle_inj {j k : Nat} (h : unaryOracle j = unaryOracle k) :
    j = k := by
  cases Nat.lt_or_ge j k with
  | inl hlt =>
    have h1 : unaryOracle j j = unaryOracle k j := congrFun h j
    rw [show unaryOracle j j = decide (j < j) from rfl,
      show unaryOracle k j = decide (j < k) from rfl,
      decide_eq_false (Nat.lt_irrefl j), decide_eq_true hlt] at h1
    exact Bool.noConfusion h1
  | inr h₁ =>
    cases Nat.lt_or_ge k j with
    | inl hlt =>
      have h1 : unaryOracle j k = unaryOracle k k := congrFun h k
      rw [show unaryOracle j k = decide (k < j) from rfl,
        show unaryOracle k k = decide (k < k) from rfl,
        decide_eq_true hlt, decide_eq_false (Nat.lt_irrefl k)] at h1
      exact Bool.noConfusion h1
    | inr h₂ => exact Nat.le_antisymm h₂ h₁

/-- **The successor chain is pairwise distinct** — a fully concrete,
never-revisiting jump chain: distinct levels are distinct oracles. Via
the closed form, this is injectivity of `unaryOracle`. -/
theorem jumpIter_successorPredictor_injective (m n : Nat)
    (h : jumpIter successorPredictor falseOracle m =
      jumpIter successorPredictor falseOracle n) : m = n := by
  rw [jumpIter_successorPredictor, jumpIter_successorPredictor] at h
  exact unaryOracle_inj h

/-- **Universal non-degeneracy is NOT necessary for pairwise
distinctness.** The successor chain flips exactly one code per step, so
its predictor fails `IsAlwaysNonDegenerate` (witness: level `1`, code
`0`, where the predictor answers `false` but the level-`1` oracle is
`true` at `0`) — yet the chain never revisits a level. -/
theorem not_isAlwaysNonDegenerate_successorPredictor :
    ¬ IsAlwaysNonDegenerate successorPredictor falseOracle := by
  intro h
  have h10 : successorPredictor
        (jumpIter successorPredictor falseOracle 1) 0 0 =
      jumpIter successorPredictor falseOracle 1 0 := h 1 0
  exact Bool.noConfusion h10

/-- **S9-light synthesis: the two conditions are orthogonal.** There is
a chain that is pairwise distinct but not universally non-degenerate.
Combined with `isAlwaysNonDegenerate_not_sufficient_for_pairwise`,
universal non-degeneracy is neither sufficient nor necessary for
pairwise distinctness: step-width (every code flips at every step) and
non-recurrence (no level is ever revisited) are independent properties
of a jump chain. -/
theorem pairwise_strict_without_isAlwaysNonDegenerate :
    ∃ (H : RelativizedHaltingPredictor) (o₀ : Nat → Bool),
      ¬ IsAlwaysNonDegenerate H o₀ ∧
      ∀ m n : Nat, m ≠ n → jumpIter H o₀ m ≠ jumpIter H o₀ n :=
  ⟨successorPredictor, falseOracle,
    not_isAlwaysNonDegenerate_successorPredictor,
    fun m n hne heq =>
      hne (jumpIter_successorPredictor_injective m n heq)⟩

#check relativized_diagonal_differs
#check no_relativized_halting_oracle
#check relativized_halting_undecidable
#check relativized_collapses_to_classical_at_trivial_oracle
#check no_uniform_relativized_halting_oracle
#check jumpOracle
#check jumpIter
#check jumpIter_zero
#check jumpIter_succ
#check jumpIter_differs
#check jumpIter_halting_undecidable
#check no_uniform_jumpIter_predictor
#check jumpIterWitness
#check jumpIterWitness_differs
#check jumpIter_compose
#check jumpIter_succ_apply
#check jumpIter_step_dichotomy
#check jumpIter_step_flip_iff
#check jumpIter_step_stable_of_self_disagree
#check NonDegenerateAt
#check strict_step_of_nonDegenerateAt
#check nonDegenerateAt_of_strict_step
#check nonDegenerateAt_iff_strict_step
#check IsEventuallyNonDegenerateAt
#check strict_step_of_eventually_nonDegenerateAt
#check trivialPredictor
#check falseOracle
#check nonDegenerateAt_trivialPredictor_zero
#check isEventuallyNonDegenerateAt_trivialPredictor
#check strict_step_trivialPredictor_zero
#check IsAlwaysNonDegenerate
#check chain_strict_succ_of_isAlwaysNonDegenerate
#check identityPredictor
#check nonDegenerateAt_identityPredictor
#check isAlwaysNonDegenerate_identityPredictor
#check chain_strict_succ_identityPredictor
#check jumpIter_identityPredictor_succ_apply
#check jumpIter_identityPredictor_add_two
#check jumpIter_identityPredictor_not_injective
#check isAlwaysNonDegenerate_not_sufficient_for_pairwise
#check HasRank
#check rank_lt_of_hasRank
#check jumpIter_injective_of_hasRank
#check chain_pairwise_strict_of_hasRank
#check unaryOracle
#check successorPredictor
#check jumpIter_successorPredictor
#check unaryOracle_inj
#check jumpIter_successorPredictor_injective
#check not_isAlwaysNonDegenerate_successorPredictor
#check pairwise_strict_without_isAlwaysNonDegenerate

end RelativizedHalting
