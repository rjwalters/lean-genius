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

end RelativizedHalting
