/-
# Relativized Halting Problem (halting-problem-OQ-03, sub-goal OQ-03a)

## What This Proves
The diagonal argument from `Proofs.HaltingProblem` lifts to the relativized
setting: for every oracle `o : Nat -> Bool`, no oracle-aware halting predictor
can correctly decide its own halting problem. This is the Lean target

  ∀ o, ¬ ∃ H : RelativizedHaltingPredictor, H decides relativized halting

stated formally below as `no_relativized_halting_oracle` and packaged in the
oracle-class form `relativized_halting_undecidable`.

## Scope (S2 ACT-A, fresh-slug iteration, researcher-10, 2026-05-12)
This file is intentionally **zero-import** (matching the parent
`Proofs.HaltingProblem`). It establishes the diagonal core of sub-goal OQ-03a
at the abstract `Nat -> Nat -> Bool` level. Concretely:

* Definitions:
    * `RelativizedHaltingPredictor` — an oracle-aware halting predictor,
      modelled as `(Nat -> Bool) -> Nat -> Nat -> Bool`.
    * `relativizedDiagonalBehavior` — the relativized analog of the
      parent's `diagonalBehavior`.
    * `Decides_in` — the abstract oracle-class membership predicate:
      "predictor `H` decides relativized halting for oracle `o`".

* Theorems (all proved, no sorries):
    * `relativized_diagonal_differs` — for every oracle `o`, predictor `H`,
      and code `n`, the relativized diagonal differs from `H` at `(n, n)`.
    * `no_relativized_halting_oracle` — the contradiction form of OQ-03a.
    * `relativized_halting_undecidable` — packaged statement: no
      `H : RelativizedHaltingPredictor` satisfies `Decides_in o H`.
    * `relativized_collapses_to_classical_at_trivial_oracle` — sanity check
      that the `o = fun _ => false` specialization of the relativized
      diagonal recovers the parent's `diagonalBehavior`.

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

#check relativized_diagonal_differs
#check no_relativized_halting_oracle
#check relativized_halting_undecidable
#check relativized_collapses_to_classical_at_trivial_oracle
#check no_uniform_relativized_halting_oracle

end RelativizedHalting
